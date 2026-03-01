#!/usr/bin/env python3
"""
discover_basis.py — Truncated SVD basis discovery for the hyperdimensional index.

Mirrors IntensionalShift.HDShift: computes a compressed basis from all stored
embeddings, stores the basis matrix (Vt) and metadata to R2, then reprojects
every entry onto the new basis.

Usage:
    python infra/discover_basis.py \\
        --lancedb-uri  "s3://TODO_R2_BUCKET/lancedb" \\
        --table        "embeddings" \\
        --basis-version 1 \\
        --k            32 \\
        --endpoint-url "$R2_ENDPOINT_URL" \\
        --bucket       "$R2_BUCKET_NAME" \\
        --access-key-id "$R2_ACCESS_KEY_ID" \\
        --secret-access-key "$R2_SECRET_ACCESS_KEY" \\
        [--dry-run]

Environment variables (alternative to CLI flags):
    R2_ENDPOINT_URL
    R2_BUCKET_NAME
    R2_ACCESS_KEY_ID
    R2_SECRET_ACCESS_KEY
    LANCEDB_URI
    LANCEDB_TABLE

R2 objects written:
    embeddings/basis/current              — JSON { version }
    embeddings/basis/v<N>/meta.json       — basis metadata
    embeddings/basis/v<N>/Vt.npy          — float32[k x 768] basis matrix
    embeddings/entries/<blake3-hash>      — updated per-entry coefficients

SVD implementation:
    Uses scipy.sparse.linalg.svds (truncated SVD, fast for k << min(n, d)).
    Equivalent to numpy.linalg.svd for dense matrices but O(n*k*d) vs O(n*d^2).
"""

from __future__ import annotations

import argparse
import io
import json
import os
import struct
import sys
from typing import Any

import boto3
import lancedb
import numpy as np
from scipy.sparse.linalg import svds

# ---------------------------------------------------------------------------
# BLAKE3 + base58 (same as index_lean.py — keep in sync or extract to util)
# ---------------------------------------------------------------------------

try:
    import blake3 as _blake3_mod

    def blake3_hash(data: bytes) -> str:
        digest = _blake3_mod.blake3(data).digest()
        return _base58_encode(digest)

except ImportError:
    import hashlib

    def blake3_hash(data: bytes) -> str:  # type: ignore[misc]
        # Fallback to SHA3-256 when blake3 is unavailable in the environment.
        # TODO: install the blake3 package — `pip install blake3`
        digest = hashlib.sha3_256(data).digest()
        return _base58_encode(digest)


_BASE58_ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def _base58_encode(data: bytes) -> str:
    n = int.from_bytes(data, "big")
    result = []
    while n:
        n, r = divmod(n, 58)
        result.append(_BASE58_ALPHABET[r])
    result.extend(_BASE58_ALPHABET[0] for b in data if b == 0)
    return "".join(reversed(result))


# ---------------------------------------------------------------------------
# NumPy .npy serialisation (no scipy.io dependency for writing)
# ---------------------------------------------------------------------------

def array_to_npy(arr: np.ndarray) -> bytes:
    """
    Serialise a numpy array to .npy format (v1.0) in memory.

    The .npy format is a de-facto standard understood by numpy, scipy,
    and most scientific Python tooling.  Reference:
      https://numpy.org/doc/stable/reference/generated/numpy.lib.format.html
    """
    buf = io.BytesIO()
    np.save(buf, arr)
    return buf.getvalue()


# ---------------------------------------------------------------------------
# R2 helpers
# ---------------------------------------------------------------------------

def make_r2_client(
    endpoint_url: str,
    access_key_id: str,
    secret_access_key: str,
) -> Any:
    return boto3.client(
        "s3",
        endpoint_url=endpoint_url,
        aws_access_key_id=access_key_id,
        aws_secret_access_key=secret_access_key,
        region_name="auto",
    )


def put_object(
    client: Any,
    bucket: str,
    key: str,
    body: bytes,
    content_type: str = "application/octet-stream",
    dry_run: bool = False,
) -> None:
    if dry_run:
        print(f"  [dry-run] PUT {key} ({len(body):,} bytes)")
        return
    client.put_object(
        Bucket=bucket,
        Key=key,
        Body=body,
        ContentType=content_type,
    )


# ---------------------------------------------------------------------------
# LanceDB helpers
# ---------------------------------------------------------------------------

def load_embeddings(
    lancedb_uri: str, table_name: str
) -> tuple[np.ndarray, list[dict[str, Any]]]:
    """
    Load all raw embeddings from LanceDB.

    Returns:
        E        — float32 array of shape (n, d), one row per entry.
        records  — list of dicts with at minimum:
                   { content_hash, formal_ref, depth, compression_loss, ... }

    LanceDB schema expected (see SPEC.md queue consumer, step 16):
        content_hash      string
        formal_ref        string
        id                string (optional)
        depth             int
        compression_loss  int
        embedding_raw     vector[768]   <-- this is what we load
        basis_coeffs      list[float]   (will be overwritten)
        basis_version     int
    """
    # TODO: configure LanceDB to point at R2 by passing storage options.
    # For Lance files on R2 the URI should be an S3-compatible path, e.g.:
    #   lancedb.connect("s3://bucket/lancedb", storage_options={
    #       "aws_access_key_id": ...,
    #       "aws_secret_access_key": ...,
    #       "aws_endpoint_url": ...,
    #   })
    db = lancedb.connect(lancedb_uri)
    table = db.open_table(table_name)

    df = table.to_pandas()

    if len(df) == 0:
        sys.exit("No entries in LanceDB table — nothing to do.")

    if "embedding_raw" not in df.columns:
        sys.exit(
            "LanceDB table is missing 'embedding_raw' column. "
            "Has the queue consumer run yet?"
        )

    # Stack embeddings into a matrix.
    raw_vecs = np.stack(df["embedding_raw"].to_numpy()).astype(np.float32)

    records = df.to_dict(orient="records")
    return raw_vecs, records


# ---------------------------------------------------------------------------
# SVD basis discovery
# ---------------------------------------------------------------------------

def discover_basis(
    E: np.ndarray, k: int
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """
    Run truncated SVD on a centred embedding matrix.

    Returns:
        global_mean  — float32[d]    mean of all embeddings
        Vt           — float32[k, d] right singular vectors (basis)
        singular_values — float64[k] singular values (descending)
        coeffs       — float32[n, k] projections of all entries
    """
    n, d = E.shape
    k = min(k, n - 1)  # svds requires k < min(n, d)
    print(f"Running truncated SVD: n={n}, d={d}, k={k}")

    global_mean = E.mean(axis=0)
    E_centred = E - global_mean

    # svds returns singular values in ascending order — reverse for convention.
    U, S, Vt = svds(E_centred, k=k)
    # Sort descending by singular value.
    order = np.argsort(S)[::-1]
    S = S[order]
    Vt = Vt[order, :]  # shape: (k, d)

    coeffs = E_centred @ Vt.T  # shape: (n, k)

    return global_mean.astype(np.float32), Vt.astype(np.float32), S, coeffs.astype(np.float32)


# ---------------------------------------------------------------------------
# Reproject and update LanceDB entries
# ---------------------------------------------------------------------------

def update_lancedb_entries(
    lancedb_uri: str,
    table_name: str,
    records: list[dict[str, Any]],
    coeffs: np.ndarray,
    basis_version: int,
    dry_run: bool,
) -> None:
    """
    Write updated basis_coeffs and basis_version back to every LanceDB entry.

    Uses LanceDB merge-insert (upsert) keyed on content_hash.
    """
    if dry_run:
        print(f"  [dry-run] Would update {len(records)} LanceDB entries (basis_version={basis_version})")
        return

    # TODO: configure LanceDB storage options for R2 (see load_embeddings).
    db = lancedb.connect(lancedb_uri)
    table = db.open_table(table_name)

    # Build a list of updated records with new coefficients.
    updates = []
    for i, rec in enumerate(records):
        updates.append({
            **rec,
            "basis_coeffs": coeffs[i].tolist(),
            "basis_version": basis_version,
        })

    import pandas as pd  # local import to avoid hard dep if not needed

    update_df = pd.DataFrame(updates)
    # Upsert: merge on content_hash.
    table.merge_insert("content_hash").when_matched_update_all().execute(update_df)
    print(f"  Updated {len(updates)} entries in LanceDB (basis_version={basis_version})")


# ---------------------------------------------------------------------------
# R2 entry metadata upload
# ---------------------------------------------------------------------------

def upload_entry_metadata(
    client: Any,
    bucket: str,
    records: list[dict[str, Any]],
    coeffs: np.ndarray,
    basis_version: int,
    dry_run: bool,
) -> None:
    """
    Write embeddings/entries/<content_hash> for every entry.

    Schema: { basis_coeffs: [float, ...], basis_version: int }
    """
    print(f"Uploading {len(records)} entry metadata objects to R2...")
    for i, rec in enumerate(records):
        content_hash = rec.get("content_hash")
        if not content_hash:
            print(f"  Warning: record {i} has no content_hash, skipping")
            continue

        entry_meta = {
            "basis_coeffs": coeffs[i].tolist(),
            "basis_version": basis_version,
        }
        key = f"embeddings/entries/{content_hash}"
        put_object(
            client,
            bucket,
            key,
            json.dumps(entry_meta).encode(),
            "application/json",
            dry_run,
        )

    print("  Done.")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def run(
    lancedb_uri: str,
    table_name: str,
    basis_version: int,
    k: int,
    model: str,
    endpoint_url: str,
    bucket: str,
    access_key_id: str,
    secret_access_key: str,
    dry_run: bool,
) -> None:
    client = make_r2_client(endpoint_url, access_key_id, secret_access_key)

    # 1. Load all raw embeddings from LanceDB.
    print(f"Loading embeddings from LanceDB: uri={lancedb_uri}, table={table_name}")
    E, records = load_embeddings(lancedb_uri, table_name)
    n, d = E.shape
    print(f"Loaded {n} embeddings (dim={d})")

    # 2. Truncated SVD.
    global_mean, Vt, singular_values, coeffs = discover_basis(E, k)
    actual_k = Vt.shape[0]

    # 3. Upload basis matrix.
    vt_npy = array_to_npy(Vt)
    vt_key = f"embeddings/basis/v{basis_version}/Vt.npy"
    print(f"Uploading basis matrix: {vt_key} ({len(vt_npy):,} bytes, shape={Vt.shape})")
    put_object(client, bucket, vt_key, vt_npy, "application/octet-stream", dry_run)

    # 4. Upload global mean alongside the basis (needed at query time).
    mean_npy = array_to_npy(global_mean)
    mean_key = f"embeddings/basis/v{basis_version}/global_mean.npy"
    print(f"Uploading global mean: {mean_key}")
    put_object(client, bucket, mean_key, mean_npy, "application/octet-stream", dry_run)

    # 5. Upload basis metadata.
    meta = {
        "version": basis_version,
        "k": actual_k,
        "d": d,
        "model": model,
        "n_entries": n,
        "singular_values": singular_values.tolist(),
        "reconstruction_threshold": 0.2,
        # Frobenius norm of residual / total — useful for monitoring drift.
        "explained_variance_ratio": float(
            np.sum(singular_values**2) / np.sum((E - global_mean) ** 2)
        ),
    }
    meta_key = f"embeddings/basis/v{basis_version}/meta.json"
    print(f"Uploading basis metadata: {meta_key}")
    put_object(
        client, bucket, meta_key, json.dumps(meta, indent=2).encode(), "application/json", dry_run
    )

    # 6. Update current basis pointer.
    current_meta = {"version": basis_version}
    current_key = "embeddings/basis/current"
    print(f"Updating basis current pointer: {current_key}")
    put_object(
        client, bucket, current_key, json.dumps(current_meta).encode(), "application/json", dry_run
    )

    # 7. Upload per-entry coefficients to R2.
    upload_entry_metadata(client, bucket, records, coeffs, basis_version, dry_run)

    # 8. Update LanceDB entries with new basis_coeffs and basis_version.
    print("Updating LanceDB entry table...")
    update_lancedb_entries(
        lancedb_uri, table_name, records, coeffs, basis_version, dry_run
    )

    print(
        f"\nBasis v{basis_version} complete: k={actual_k}, n={n}, "
        f"explained_variance={meta['explained_variance_ratio']:.3f}"
    )
    if dry_run:
        print("(dry-run: no objects were actually written)")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Discover SVD basis from embeddings and upload to R2."
    )
    parser.add_argument(
        "--lancedb-uri",
        default=os.environ.get("LANCEDB_URI", "./lancedb"),
        help="LanceDB URI (local path or s3:// path). Default: $LANCEDB_URI or ./lancedb",
    )
    parser.add_argument(
        "--table",
        default=os.environ.get("LANCEDB_TABLE", "embeddings"),
        help="LanceDB table name (default: $LANCEDB_TABLE or 'embeddings')",
    )
    parser.add_argument(
        "--basis-version",
        type=int,
        required=True,
        help="Version number for this basis (monotone, e.g. 1, 2, 3, ...)",
    )
    parser.add_argument(
        "--k",
        type=int,
        default=32,
        help="Number of basis vectors (default: 32, must be < number of entries)",
    )
    parser.add_argument(
        "--model",
        default="nomic-embed-text-v1.5",
        help="Embedding model name to record in metadata (default: nomic-embed-text-v1.5)",
    )
    parser.add_argument(
        "--endpoint-url",
        default=os.environ.get("R2_ENDPOINT_URL"),
        help="R2 S3-compatible endpoint URL (or set R2_ENDPOINT_URL)",
    )
    parser.add_argument(
        "--bucket",
        default=os.environ.get("R2_BUCKET_NAME"),
        help="R2 bucket name (or set R2_BUCKET_NAME)",
    )
    parser.add_argument(
        "--access-key-id",
        default=os.environ.get("R2_ACCESS_KEY_ID"),
        help="R2 access key ID (or set R2_ACCESS_KEY_ID)",
    )
    parser.add_argument(
        "--secret-access-key",
        default=os.environ.get("R2_SECRET_ACCESS_KEY"),
        help="R2 secret access key (or set R2_SECRET_ACCESS_KEY)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print what would be written without uploading or modifying LanceDB",
    )
    args = parser.parse_args()

    missing = [
        name
        for name, val in [
            ("--endpoint-url", args.endpoint_url),
            ("--bucket", args.bucket),
            ("--access-key-id", args.access_key_id),
            ("--secret-access-key", args.secret_access_key),
        ]
        if not val and not args.dry_run
    ]
    if missing:
        parser.error(
            f"Missing required arguments (or set the corresponding env vars): {', '.join(missing)}"
        )

    if args.basis_version < 1:
        parser.error("--basis-version must be a positive integer")

    run(
        lancedb_uri=args.lancedb_uri,
        table_name=args.table,
        basis_version=args.basis_version,
        k=args.k,
        model=args.model,
        endpoint_url=args.endpoint_url or "",
        bucket=args.bucket or "",
        access_key_id=args.access_key_id or "",
        secret_access_key=args.secret_access_key or "",
        dry_run=args.dry_run,
    )


if __name__ == "__main__":
    main()
