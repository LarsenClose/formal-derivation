# Infrastructure Specification

Cloud-native, serverless, interoperable storage and retrieval layer for formal
content and semantic deposits. Three priorities in order:

1. **Security guarantees** — content integrity, author attribution, immutable history
2. **Dedup / compression / indexing** — content-addressed storage, hyperdimensional index
3. **Path for semantics** — any deposit, however small and remote, finds its way in

---

## Stack

| Layer | Technology | Why |
|-------|-----------|-----|
| Object store | Cloudflare R2 | S3-compatible, zero egress fees, built into Workers runtime |
| Serverless compute | Cloudflare Workers | Zero cold-start, global edge, R2 SDK built-in |
| Async jobs | Cloudflare Queues | Decouples deposit from embedding without a server |
| Vector index | LanceDB (Lance files on R2) | Stores basis coefficients natively; open format; embedded |
| Embeddings | `nomic-embed-text-v1.5` | Open weights (Apache 2.0), 768-dim, matryoshka, runs locally |
| Content addressing | BLAKE3 | Speed + security; base58 encoding for human legibility |
| Signing | Ed25519 (`@noble/ed25519`) | Fast, small keys, standard |
| Basis discovery | Truncated SVD (scipy) | Offline, deterministic, directly mirrors `HDShift` formalization |

---

## R2 Key Schema

```
cas/
  <blake3-hash>                       -- raw content blobs (all types, deduplicated)

lean/
  by-decl/<Namespace.Name>            -- JSON: { hash, file_path, module, kind, lean_version }
  by-hash/<blake3-hash>               -- JSON: { decl_name }

semantic/
  by-id/<slug>/current                -- JSON: { version, hash, formal_ref }  (only mutable pointer)
  by-id/<slug>/v<N>                   -- JSON: { hash, version, formal_ref, depth,
                                      --        compression_loss, ts }  (locked, never deleted)

embeddings/
  basis/current                       -- JSON: { version }
  basis/v<N>/meta.json                -- JSON: { k, d, model, n_entries, singular_values, ... }
  basis/v<N>/Vt.npy                   -- float32[k x 768] basis matrix
  entries/<blake3-hash>               -- JSON: { basis_coeffs, basis_version }

signatures/
  <content-hash>.sig                  -- detached Ed25519 signature (base64)
  <content-hash>.pubkey               -- public key (base64)
```

---

## Deposit Flow

```
Depositor (anywhere)
  |
  | 1. Compose minimal payload:
  |    { formal_ref, note, depth, compression_loss,
  |      [id, title, tags, version, improved_over] }
  |    Minimum valid: { formal_ref, note, depth, compression_loss }
  |
  | 2. Sign with Ed25519 private key:
  |    sig = sign(blake3(canonical_json(payload)), privkey)
  |    envelope = { payload, sig, pubkey }
  |
  v
POST /deposit  (Cloudflare Worker, edge)
  |
  | 3. Verify Ed25519 sig — reject if invalid
  | 4. Validate schema — reject if depth or compression_loss out of [1,10]
  |    Unresolvable formal_ref: accept, mark pending_formal_verification
  |    ("any deposit finds its way in")
  |
  | 5. content_hash = blake3(canonical_json(payload))
  | 6. Dedup: GET cas/<content_hash> — return 200 if already exists
  |
  | 7. PUT cas/<content_hash>
  | 8. PUT signatures/<content_hash>.sig
  | 9. PUT signatures/<content_hash>.pubkey
  |
  |10. Monotone version check:
  |    GET semantic/by-id/<slug>/current -> { version: N }
  |    Reject if payload.version <= N
  |    PUT semantic/by-id/<slug>/v<N+1>   (Object Lock: immutable)
  |    PUT semantic/by-id/<slug>/current  (update pointer)
  |
  |11. Enqueue embedding job:
  |    { content_hash, formal_ref, text: note + title + tags }
  |
  v
200 { cas_key, version, monotone_confirmed: true }

Queue Consumer Worker (async)
  |
  |12. Dequeue job
  |13. embed(text) -> float32[768]
  |14. Load basis/v<N>/Vt.npy from R2
  |15. basis_coeffs = (embed - global_mean) @ Vt.T  [float32[k]]
  |16. Write LanceDB entry:
  |    { content_hash, formal_ref, id, depth, compression_loss,
  |      embedding_raw, basis_coeffs, basis_version }
  |17. PUT embeddings/entries/<content_hash>
```

---

## Lean Indexing (CI, post-build)

`infra/index_lean.py` runs as a GitHub Actions step after `lake build`.

1. Walk `Formal/**/*.lean`, extract declaration names (regex on `def `, `theorem `,
   `structure `, `inductive `, `abbrev `) with namespace context
2. Compute `blake3(file_bytes)` per file
3. Upload to `cas/<hash>`, index at `lean/by-decl/<Namespace.Name>`
4. Declaration-level CID (optional, sub-file granularity):
   `lean:<Module>.<DeclName>@<blake3-of-declaration-source-text>`

---

## Hyperdimensional Index

The index directly mirrors `IntensionalShift.HDShift`:

```
HDShift in Lean:            This system:
─────────────────────       ──────────────────────────────────────
extensional: List V         embedding_raw: float32[768] per entry
basis.basis: List V         Vt: float32[k x 768] in R2
basis.bind: V → V → V       bind(u,v) = normalize(project(u+v))
                             where project(w) = (w @ Vt.T) @ Vt
compressed: k < n           k = min(32, n-1) basis vectors for n entries
recoverable: Generated      reconstruction_error < 0.2 threshold
```

**Basis discovery** (offline, Python, runs weekly or on corpus doubling):

```python
E = load_all_embeddings()          # (n, 768)
E_c = E - E.mean(axis=0)           # center
k = min(32, len(E) - 1)
U, S, Vt = svds(E_c, k=k)          # Vt: (k, 768)
coeffs = E_c @ Vt.T                # (n, k) — sparse projections
upload_basis(Vt, global_mean=E.mean(axis=0))
reindex_all_entries(coeffs)
```

New entries between updates: project onto current basis. Reconstruction error
grows until next SVD run. This is the correct tradeoff — don't recompute SVD per deposit.

**Query**:
```
q_vec = embed(query_text)
q_coeffs = (q_vec - global_mean) @ Vt.T
LanceDB ANN search on basis_coeffs column by dot product with q_coeffs
```

---

## Security Guarantees

| Guarantee | Mechanism |
|-----------|-----------|
| Content integrity | BLAKE3 hash — rehash any object to verify |
| Author attribution | Ed25519 signature per deposit, stored alongside content |
| Non-repudiation | Signed hash in immutable object — cannot deny after signing |
| Monotone improvement | `current` pointer update gated on `version > current.version` |
| Immutable history | R2 Object Lock (compliance mode) on `v<N>` objects — cannot delete or overwrite |
| Tamper detection | Stored sig verifiable against stored content at any time |

**What this does not do**: access control (public corpus, permissive by default), privacy (all content is public), or content-quality enforcement (improvement is human judgment, not script).

The key fingerprint should be published in `CITATION.cff` or `README.md` so deposits can be independently verified.

---

## Read Paths

```
GET /formal/Reception.DiamondPoint
    -> lean/by-decl/Reception.DiamondPoint (JSON)
    -> cas/<hash> (lean source, sliced to declaration)
    -> semantic/by-id/diamond-point/current (version pointer)
    -> cas/<semantic-hash> (markdown)

GET /search?q=threshold+where+announcing+and+receiving+collapse
    -> embed(query) -> project to basis -> LanceDB ANN
    -> cas/<hash> per result (markdown excerpts)
    -> ranked by basis_coeffs dot product, then depth DESC

GET /cross/Reception.DiamondPoint
    -> embed lean declaration source -> LanceDB ANN on semantic entries
    -> return: { formal: decl, semantic: [ranked entries] }
```

---

## Interoperability

- R2 is S3-compatible — any S3 client reads the store
- Deposit API is a simple HTTP POST with JSON — no SDK required
- LanceDB Lance files are open format (Apache Arrow)
- Embedding model is open weights — reproducible locally
- All metadata is JSON or YAML — no binary-only formats on the hot path
- Key format (BLAKE3 base58) is self-describing and stable

---

## Build vs. Wire

| Component | Status | Effort |
|-----------|--------|--------|
| Cloudflare Worker — deposit endpoint | Wire (~300 lines TS) | Low |
| R2 storage layout | Wire — naming convention only | Trivial |
| Ed25519 + BLAKE3 | Wire (`@noble/` libs in Worker) | Low |
| LanceDB on R2 | Wire (Node.js writer process) | Medium |
| Nomic embeddings | Wire (sentence-transformers) | Low |
| Truncated SVD basis discovery | Wire (scipy, ~50 lines) | Low |
| Lean declaration parser | Partial build (~100 lines Python) | Low-Medium |
| Cloudflare Queues (async embed) | Wire | Low |
| R2 Object Lock | Wire (bucket policy) | Trivial |
| `infra/index_lean.py` (CI step) | Build | Low |
| `infra/discover_basis.py` | Build | Low |
| `infra/worker/` (Worker source) | Build | Medium |

**Genuinely novel**: storing `basis_coeffs` as the primary search vector rather than
raw embeddings, and searching in basis space. This is the infrastructure analog of
`hd_shift_complete`: the index is a materialized SVD decomposition, and retrieval
is decomposition-space search. Standard vector stores do not do this.

---

## Tensions

**"Any deposit finds its way in" vs. spam resistance.**
Ed25519 signing is the only gate. Unknown `formal_ref` values are accepted and
flagged `pending_formal_verification`. A compromised key is the only injection
vector. Resolution: single-author key, fingerprint published in repo.

**Monotone improvement is human judgment, not script.**
The structural layer (Object Lock + version counter) prevents overwriting and
makes rollback detectable. It does not check whether the description got better.
That remains a human commitment, attested by `improved_over` and legible in git
history. The SCHEMA.md already states this explicitly.

**LanceDB write path is not purely serverless.**
Lance format requires a compaction writer. For this write cadence (weeks between
deposits), a cron-scheduled Fly.io machine or Durable Object handles writes;
reads from static Lance files on R2 are fully stateless. Not a blocker.
