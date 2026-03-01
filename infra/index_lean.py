#!/usr/bin/env python3
"""
index_lean.py — Walk Formal/**/*.lean, extract declarations, upload to R2.

Run as a GitHub Actions step after `lake build`:

    python infra/index_lean.py \\
        --formal-root ./Formal \\
        --lean-version "$(cat lean-toolchain)" \\
        --endpoint-url "$R2_ENDPOINT_URL" \\
        --bucket "$R2_BUCKET_NAME" \\
        --access-key-id "$R2_ACCESS_KEY_ID" \\
        --secret-access-key "$R2_SECRET_ACCESS_KEY" \\
        [--dry-run]

Environment variables (alternative to CLI flags):
    R2_ENDPOINT_URL        — e.g. https://<account-id>.r2.cloudflarestorage.com
    R2_BUCKET_NAME
    R2_ACCESS_KEY_ID
    R2_SECRET_ACCESS_KEY

R2 key schema written:
    cas/<blake3-hash>                       — raw Lean file bytes
    lean/by-decl/<Namespace.Name>           — JSON declaration metadata
    lean/by-hash/<blake3-hash>              — JSON: { decl_names: [...] }
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Iterator

import boto3
import blake3

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

# Declaration kinds recognised in Lean 4 source.
DECL_KEYWORDS = ["def", "theorem", "lemma", "structure", "inductive", "abbrev", "class", "instance"]

# Regex that matches a declaration header at the start of a line.
# Groups: (keyword, name)
# Handles optional modifiers: private, protected, noncomputable, @[...] attributes.
DECL_RE = re.compile(
    r"^(?:@\[.*?\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?P<keyword>" + "|".join(DECL_KEYWORDS) + r")\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_.']*)",
    re.MULTILINE,
)

# Namespace open/close tracking.
NAMESPACE_OPEN_RE = re.compile(r"^namespace\s+(?P<name>[A-Za-z_][A-Za-z0-9_.]*)", re.MULTILINE)
NAMESPACE_END_RE = re.compile(r"^end\s+(?P<name>[A-Za-z_][A-Za-z0-9_.]*)\s*$", re.MULTILINE)

# ---------------------------------------------------------------------------
# Data types
# ---------------------------------------------------------------------------

@dataclass
class DeclRecord:
    """A single Lean declaration extracted from a source file."""
    decl_name: str          # Fully qualified: Namespace.Name
    kind: str               # def / theorem / structure / …
    file_path: str          # Relative path under the formal root
    module: str             # Module name derived from file path
    file_hash: str          # BLAKE3 of the file bytes (base58)
    lean_version: str       # From lean-toolchain
    source_text: str = ""   # Declaration source text (optional, best-effort)


@dataclass
class FileRecord:
    """Metadata for an indexed Lean file."""
    file_path: str
    file_hash: str
    module: str
    decl_names: list[str] = field(default_factory=list)


# ---------------------------------------------------------------------------
# BLAKE3 + base58
# ---------------------------------------------------------------------------

_BASE58_ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def _base58_encode(data: bytes) -> str:
    """Encode bytes as a Bitcoin-style base58 string."""
    n = int.from_bytes(data, "big")
    result = []
    while n:
        n, r = divmod(n, 58)
        result.append(_BASE58_ALPHABET[r])
    # Preserve leading zero bytes.
    result.extend(_BASE58_ALPHABET[0] for b in data if b == 0)
    return "".join(reversed(result))


def blake3_hash(data: bytes) -> str:
    """Return the BLAKE3 hash of `data` as a base58-encoded string."""
    digest = blake3.blake3(data).digest()
    return _base58_encode(digest)


# ---------------------------------------------------------------------------
# Namespace tracking
# ---------------------------------------------------------------------------

def extract_namespace_stack(source: str, char_pos: int) -> list[str]:
    """
    Return the namespace stack active at `char_pos` in `source`.

    Walks `namespace X` / `end X` pairs up to (but not including) char_pos.
    This is a best-effort heuristic — it does not handle section/variable
    blocks or conditional namespaces.
    """
    stack: list[str] = []
    for m in re.finditer(
        r"^(?P<open>namespace\s+(?P<oname>[A-Za-z_][A-Za-z0-9_.]*)|end\s+(?P<ename>[A-Za-z_][A-Za-z0-9_.]*))\s*$",
        source,
        re.MULTILINE,
    ):
        if m.start() >= char_pos:
            break
        if m.group("open").startswith("namespace"):
            stack.append(m.group("oname"))
        else:
            ename = m.group("ename")
            # Pop the innermost matching namespace (ignore mismatches).
            for i in range(len(stack) - 1, -1, -1):
                if stack[i] == ename:
                    stack = stack[:i]
                    break
    return stack


# ---------------------------------------------------------------------------
# Declaration extraction
# ---------------------------------------------------------------------------

def extract_declarations(
    source: str,
    file_path: str,
    module: str,
    file_hash: str,
    lean_version: str,
) -> list[DeclRecord]:
    """
    Extract all top-level declarations from `source`.

    Returns a list of DeclRecord, one per matched declaration.
    """
    records: list[DeclRecord] = []
    seen: set[str] = set()

    for m in DECL_RE.finditer(source):
        keyword = m.group("keyword")
        local_name = m.group("name")

        # Resolve namespace context at this position.
        ns_stack = extract_namespace_stack(source, m.start())
        if ns_stack:
            full_name = ".".join(ns_stack) + "." + local_name
        else:
            full_name = local_name

        # Avoid duplicates (e.g. from multi-line attribute blocks).
        if full_name in seen:
            continue
        seen.add(full_name)

        # Best-effort: extract declaration source text from this match
        # to the next declaration or end of file.
        decl_start = m.start()
        next_decl = DECL_RE.search(source, m.end())
        decl_end = next_decl.start() if next_decl else len(source)
        source_text = source[decl_start:decl_end].strip()

        records.append(
            DeclRecord(
                decl_name=full_name,
                kind=keyword,
                file_path=file_path,
                module=module,
                file_hash=file_hash,
                lean_version=lean_version,
                source_text=source_text,
            )
        )

    return records


# ---------------------------------------------------------------------------
# File walking
# ---------------------------------------------------------------------------

def module_name(formal_root: Path, lean_file: Path) -> str:
    """
    Derive the Lean module name from a file path.

    e.g. Formal/Derivation/IntensionalShift.lean -> Derivation.IntensionalShift
    """
    rel = lean_file.relative_to(formal_root)
    parts = list(rel.parts)
    parts[-1] = parts[-1].removesuffix(".lean")
    return ".".join(parts)


def walk_lean_files(formal_root: Path) -> Iterator[Path]:
    """Yield all .lean files under `formal_root` recursively."""
    for path in sorted(formal_root.rglob("*.lean")):
        if path.is_file():
            yield path


# ---------------------------------------------------------------------------
# R2 upload helpers
# ---------------------------------------------------------------------------

def make_r2_client(
    endpoint_url: str,
    access_key_id: str,
    secret_access_key: str,
) -> "boto3.client":
    """Return a boto3 S3 client pointed at the R2 endpoint."""
    return boto3.client(
        "s3",
        endpoint_url=endpoint_url,
        aws_access_key_id=access_key_id,
        aws_secret_access_key=secret_access_key,
        region_name="auto",
    )


def object_exists(client, bucket: str, key: str) -> bool:
    """Return True if the R2 object exists (HEAD request)."""
    try:
        client.head_object(Bucket=bucket, Key=key)
        return True
    except client.exceptions.ClientError as e:
        if e.response["Error"]["Code"] in ("404", "NoSuchKey"):
            return False
        raise


def put_object(
    client,
    bucket: str,
    key: str,
    body: bytes,
    content_type: str = "application/octet-stream",
    dry_run: bool = False,
) -> None:
    """Upload `body` to `key` in `bucket`."""
    if dry_run:
        print(f"  [dry-run] PUT {key} ({len(body)} bytes)")
        return
    client.put_object(
        Bucket=bucket,
        Key=key,
        Body=body,
        ContentType=content_type,
    )


# ---------------------------------------------------------------------------
# Main indexing logic
# ---------------------------------------------------------------------------

def index_file(
    lean_file: Path,
    formal_root: Path,
    lean_version: str,
    client,
    bucket: str,
    dry_run: bool,
) -> FileRecord:
    """Index one .lean file: hash, upload to CAS, upload declaration metadata."""
    source_bytes = lean_file.read_bytes()
    file_hash = blake3_hash(source_bytes)
    rel_path = str(lean_file.relative_to(formal_root.parent))
    mod_name = module_name(formal_root, lean_file)

    print(f"  {rel_path}  blake3={file_hash[:16]}...")

    # Upload raw file bytes to CAS (skip if already present).
    cas_key = f"cas/{file_hash}"
    if not object_exists(client, bucket, cas_key) or dry_run:
        put_object(client, bucket, cas_key, source_bytes, "text/plain", dry_run)

    # Extract declarations.
    source_text = source_bytes.decode("utf-8", errors="replace")
    decls = extract_declarations(
        source=source_text,
        file_path=rel_path,
        module=mod_name,
        file_hash=file_hash,
        lean_version=lean_version,
    )

    file_record = FileRecord(
        file_path=rel_path,
        file_hash=file_hash,
        module=mod_name,
    )

    for decl in decls:
        # Declaration-level CID: blake3 of the declaration source text.
        decl_source_bytes = decl.source_text.encode("utf-8")
        decl_hash = blake3_hash(decl_source_bytes)

        # Write declaration source to CAS.
        decl_cas_key = f"cas/{decl_hash}"
        if not object_exists(client, bucket, decl_cas_key) or dry_run:
            put_object(
                client, bucket, decl_cas_key, decl_source_bytes, "text/plain", dry_run
            )

        # lean/by-decl/<Namespace.Name>
        by_decl_key = f"lean/by-decl/{decl.decl_name}"
        meta = {
            "hash": decl_hash,
            "file_hash": file_hash,
            "file_path": rel_path,
            "module": mod_name,
            "kind": decl.kind,
            "lean_version": lean_version,
            # Declaration-level CID in the lean: URI scheme.
            "cid": f"lean:{mod_name}.{decl.decl_name.split('.')[-1]}@{decl_hash}",
        }
        put_object(
            client,
            bucket,
            by_decl_key,
            json.dumps(meta).encode(),
            "application/json",
            dry_run,
        )
        print(f"    {decl.kind} {decl.decl_name}")
        file_record.decl_names.append(decl.decl_name)

    # lean/by-hash/<file-hash> — maps file hash to list of decls.
    by_hash_key = f"lean/by-hash/{file_hash}"
    by_hash_meta = {
        "file_path": rel_path,
        "module": mod_name,
        "decl_names": file_record.decl_names,
    }
    put_object(
        client,
        bucket,
        by_hash_key,
        json.dumps(by_hash_meta).encode(),
        "application/json",
        dry_run,
    )

    return file_record


def run(
    formal_root: Path,
    lean_version: str,
    endpoint_url: str,
    bucket: str,
    access_key_id: str,
    secret_access_key: str,
    dry_run: bool,
) -> None:
    client = make_r2_client(endpoint_url, access_key_id, secret_access_key)

    lean_files = list(walk_lean_files(formal_root))
    print(f"Found {len(lean_files)} .lean file(s) under {formal_root}")

    total_decls = 0
    for lean_file in lean_files:
        record = index_file(
            lean_file, formal_root, lean_version, client, bucket, dry_run
        )
        total_decls += len(record.decl_names)

    print(f"\nIndexed {len(lean_files)} files, {total_decls} declarations.")
    if dry_run:
        print("(dry-run: no objects were actually written)")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Index Lean declarations and upload to R2."
    )
    parser.add_argument(
        "--formal-root",
        default="./Formal",
        help="Path to the Formal/ directory (default: ./Formal)",
    )
    parser.add_argument(
        "--lean-version",
        default=os.environ.get("LEAN_VERSION", "unknown"),
        help="Lean toolchain version string (default: $LEAN_VERSION or 'unknown')",
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
        help="Print what would be uploaded without writing to R2",
    )
    args = parser.parse_args()

    # Validate required arguments.
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

    formal_root = Path(args.formal_root).resolve()
    if not formal_root.is_dir():
        sys.exit(f"Error: --formal-root '{formal_root}' is not a directory")

    run(
        formal_root=formal_root,
        lean_version=args.lean_version,
        endpoint_url=args.endpoint_url or "",
        bucket=args.bucket or "",
        access_key_id=args.access_key_id or "",
        secret_access_key=args.secret_access_key or "",
        dry_run=args.dry_run,
    )


if __name__ == "__main__":
    main()
