/**
 * Cloudflare Worker — Formal Derivation deposit and read API.
 *
 * Endpoints:
 *   POST /deposit           — write a signed semantic deposit
 *   GET  /formal/:ns/:name  — lookup by Lean declaration name
 *   GET  /search?q=text     — vector search (stub, returns 501)
 *   GET  /health            — liveness check
 *
 * Environment bindings (configure in wrangler.toml):
 *   BUCKET   — R2Bucket  (main object store)
 *   EMBED_QUEUE — Queue  (async embedding jobs)
 *   SIGNING_KEY_PUBKEY — string (authorised depositor public key, base64)
 */

import {
  R2Bucket,
  Queue,
  ExecutionContext,
} from "@cloudflare/workers-types";

import { validateEnvelope, slugFromRef } from "./schema";
import { verifySignature } from "./verify";
import { hashPayload, canonicalJson } from "./hash";
import { getCurrentVersion, writeVersion, resolveNextVersion } from "./version";

// ---------------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------------

export interface Env {
  /** R2 bucket for all content-addressed and structured objects. */
  BUCKET: R2Bucket;
  /**
   * Cloudflare Queue for async embedding jobs.
   * TODO: bind in wrangler.toml under [[queues.producers]]
   */
  EMBED_QUEUE: Queue;
  /**
   * Comma-separated list of authorised depositor public keys (base64).
   * If empty or unset, any valid Ed25519 key is accepted.
   * TODO: set in wrangler.toml [vars] or as a secret
   */
  SIGNING_KEY_PUBKEY?: string;
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function json(body: unknown, status = 200): Response {
  return new Response(JSON.stringify(body), {
    status,
    headers: { "content-type": "application/json" },
  });
}

function err(message: string, status: number, extra?: object): Response {
  return json({ error: message, ...extra }, status);
}

/**
 * Check whether a public key is in the SIGNING_KEY_PUBKEY allow-list.
 * If the env var is absent/empty, all keys are permitted (open deposit).
 */
function isAuthorisedKey(pubkey: string, env: Env): boolean {
  if (!env.SIGNING_KEY_PUBKEY || env.SIGNING_KEY_PUBKEY.trim() === "") {
    return true;
  }
  const allowed = env.SIGNING_KEY_PUBKEY.split(",").map((k) => k.trim());
  return allowed.includes(pubkey.trim());
}

// ---------------------------------------------------------------------------
// POST /deposit
// ---------------------------------------------------------------------------

async function handleDeposit(
  request: Request,
  env: Env
): Promise<Response> {
  let raw: unknown;
  try {
    raw = await request.json();
  } catch {
    return err("Request body must be valid JSON", 400);
  }

  // 1. Schema validation.
  const validation = validateEnvelope(raw);
  if (!validation.ok) {
    return json({ error: "Validation failed", errors: validation.errors }, 400);
  }
  const { envelope } = validation;
  const { payload, sig, pubkey } = envelope;

  // 2. Allow-list check (optional; open by default).
  if (!isAuthorisedKey(pubkey, env)) {
    return err("Public key not in allowed list", 403);
  }

  // 3. Ed25519 signature verification.
  //    The signed message is BLAKE3(canonical_json(payload)) as raw bytes.
  //    We re-derive the canonical JSON so we can produce the raw digest
  //    bytes that the depositor actually signed.
  const canonicalJsonStr = canonicalJson(payload);
  const contentHashStr = hashPayload(payload);

  // Import blake3 directly to get raw bytes (hashPayload returns base58).
  const { blake3 } = await import("@noble/hashes/blake3");
  const messageBytes = blake3(new TextEncoder().encode(canonicalJsonStr));

  const verifyResult = await verifySignature(messageBytes, sig, pubkey);
  if (!verifyResult.valid) {
    return err(`Signature verification failed: ${verifyResult.reason}`, 401);
  }

  // 4. Dedup: check if this content hash already exists.
  const casKey = `cas/${contentHashStr}`;
  const existing = await env.BUCKET.head(casKey);
  if (existing !== null) {
    // Already stored — return the existing record without re-writing.
    // Read current version for context.
    const slug = payload.id ?? slugFromRef(payload.formal_ref);
    const { version } = await getCurrentVersion(env.BUCKET, slug);
    return json({
      cas_key: casKey,
      version,
      monotone_confirmed: true,
      deduplicated: true,
    });
  }

  // 5. Check whether formal_ref resolves to a known Lean declaration.
  const leanKey = `lean/by-decl/${payload.formal_ref}`;
  const leanEntry = await env.BUCKET.head(leanKey);
  const pendingFormalVerification = leanEntry === null;

  // 6. Write CAS blob.
  const canonicalBytes = new TextEncoder().encode(canonicalJsonStr);
  await env.BUCKET.put(casKey, canonicalBytes, {
    httpMetadata: { contentType: "application/json" },
    customMetadata: {
      formal_ref: payload.formal_ref,
      pending_formal_verification: String(pendingFormalVerification),
    },
  });

  // 7. Write signature and public key.
  await Promise.all([
    env.BUCKET.put(
      `signatures/${contentHashStr}.sig`,
      sig,
      { httpMetadata: { contentType: "text/plain" } }
    ),
    env.BUCKET.put(
      `signatures/${contentHashStr}.pubkey`,
      pubkey,
      { httpMetadata: { contentType: "text/plain" } }
    ),
  ]);

  // 8. Monotone version write.
  const slug = payload.id ?? slugFromRef(payload.formal_ref);
  const { version: currentVersion } = await getCurrentVersion(
    env.BUCKET,
    slug
  );
  const nextResolution = resolveNextVersion(currentVersion, payload.version);

  if ("conflict" in nextResolution) {
    return err(
      `Monotone constraint violated: incoming version ${payload.version} is not greater than current version ${nextResolution.current}`,
      409,
      { current_version: nextResolution.current }
    );
  }

  const writeResult = await writeVersion(
    env.BUCKET,
    slug,
    {
      hash: contentHashStr,
      formal_ref: payload.formal_ref,
      depth: payload.depth,
      compression_loss: payload.compression_loss,
      pending_formal_verification: pendingFormalVerification || undefined,
      improved_over: payload.improved_over,
    },
    nextResolution.version
  );

  if (!writeResult.ok) {
    // Race condition — another write happened between our read and our write.
    return err(writeResult.message, 409, {
      current_version: writeResult.current_version,
    });
  }

  // 9. Enqueue async embedding job.
  const embedText = [
    payload.note,
    payload.title ?? "",
    (payload.tags ?? []).join(" "),
  ]
    .filter(Boolean)
    .join(" ");

  try {
    await env.EMBED_QUEUE.send({
      content_hash: contentHashStr,
      formal_ref: payload.formal_ref,
      slug,
      text: embedText,
    });
  } catch (queueErr) {
    // Non-fatal: the deposit is written; embedding happens asynchronously.
    // Log for observability but do not fail the request.
    console.error("Failed to enqueue embedding job:", queueErr);
  }

  return json({
    cas_key: writeResult.cas_key,
    version: writeResult.version,
    monotone_confirmed: true,
    pending_formal_verification: pendingFormalVerification,
  });
}

// ---------------------------------------------------------------------------
// GET /formal/:namespace/:name
// ---------------------------------------------------------------------------

async function handleFormalLookup(
  namespace: string,
  name: string,
  env: Env
): Promise<Response> {
  const declName = `${namespace}.${name}`;
  const leanKey = `lean/by-decl/${declName}`;

  const obj = await env.BUCKET.get(leanKey);
  if (obj === null) {
    return err(`Declaration not found: ${declName}`, 404);
  }

  const declMeta = JSON.parse(await obj.text()) as {
    hash: string;
    file_path: string;
    module: string;
    kind: string;
    lean_version: string;
  };

  // Fetch the raw Lean source blob from CAS.
  const sourceObj = await env.BUCKET.get(`cas/${declMeta.hash}`);
  const sourceAvailable = sourceObj !== null;

  // Fetch current semantic pointer if one exists.
  const slug = slugFromRef(declName);
  const semanticKey = `semantic/by-id/${slug}/current`;
  const semanticObj = await env.BUCKET.get(semanticKey);
  const semantic = semanticObj
    ? JSON.parse(await semanticObj.text())
    : null;

  // Fetch semantic content from CAS if available.
  let semanticContent: string | null = null;
  if (semantic?.hash) {
    const semCasObj = await env.BUCKET.get(`cas/${semantic.hash}`);
    if (semCasObj !== null) {
      semanticContent = await semCasObj.text();
    }
  }

  return json({
    decl_name: declName,
    meta: declMeta,
    source_available: sourceAvailable,
    semantic,
    semantic_content: semanticContent,
  });
}

// ---------------------------------------------------------------------------
// GET /search?q=text
// ---------------------------------------------------------------------------

async function handleSearch(query: string): Promise<Response> {
  // TODO: implement vector search.
  //
  // Implementation outline:
  //   1. Call the nomic-embed-text-v1.5 model to embed `query` into float32[768].
  //      (Workers AI binding, or an external embedding service.)
  //   2. Load global_mean from embeddings/basis/current -> embeddings/basis/v<N>/meta.json
  //   3. Load Vt matrix from embeddings/basis/v<N>/Vt.npy (parse float32 npy from R2)
  //   4. Compute q_coeffs = (q_vec - global_mean) @ Vt.T  [float32[k]]
  //   5. Open LanceDB table from R2 Lance files.
  //   6. Run ANN search on basis_coeffs column using dot product with q_coeffs.
  //   7. For each result, load cas/<hash> to get markdown content.
  //   8. Rank by basis_coeffs dot product, then depth DESC.
  //   9. Return ranked array of { cas_key, formal_ref, depth, snippet }.
  //
  // LanceDB integration requires a Lance-compatible reader in the Worker
  // or a sidecar process.  See SPEC.md "Tensions" section.
  void query;
  return json(
    {
      error: "Not implemented",
      message:
        "Vector search requires LanceDB integration. See TODO in src/index.ts handleSearch.",
    },
    501
  );
}

// ---------------------------------------------------------------------------
// Router
// ---------------------------------------------------------------------------

export default {
  async fetch(
    request: Request,
    env: Env,
    _ctx: ExecutionContext
  ): Promise<Response> {
    const url = new URL(request.url);
    const method = request.method.toUpperCase();
    const pathname = url.pathname;

    // Health check.
    if (pathname === "/health" && method === "GET") {
      return json({ ok: true });
    }

    // Deposit.
    if (pathname === "/deposit" && method === "POST") {
      return handleDeposit(request, env);
    }

    // Formal lookup: GET /formal/<namespace>/<name>
    // Supports exactly one dot-separated namespace component; deeper
    // namespaces should be URL-encoded in `name`.
    const formalMatch = pathname.match(
      /^\/formal\/([A-Za-z][A-Za-z0-9_]*)\/([A-Za-z][A-Za-z0-9_.]*)\/?$/
    );
    if (formalMatch && method === "GET") {
      return handleFormalLookup(formalMatch[1], formalMatch[2], env);
    }

    // Vector search.
    if (pathname === "/search" && method === "GET") {
      const q = url.searchParams.get("q");
      if (!q || q.trim() === "") {
        return err("Query parameter `q` is required", 400);
      }
      return handleSearch(q.trim());
    }

    return err("Not found", 404);
  },
};
