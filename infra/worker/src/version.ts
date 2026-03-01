/**
 * Monotone version pointer logic.
 *
 * The `current` pointer at `semantic/by-id/<slug>/current` is the only
 * mutable object in the semantic namespace.  Every deposit that changes
 * the state writes a new immutable versioned object (`v<N>`) and then
 * atomically updates the `current` pointer.
 *
 * Invariant: version numbers are strictly increasing.  Any attempt to
 * write version N when current is already >= N is rejected with 409.
 */

import { R2Bucket } from "@cloudflare/workers-types";

/** Shape of the `current` pointer object. */
export interface CurrentPointer {
  version: number;
  hash: string;
  formal_ref: string;
}

/** Shape of a versioned semantic entry (`v<N>`). */
export interface VersionedEntry {
  hash: string;
  version: number;
  formal_ref: string;
  depth: number;
  compression_loss: number;
  /** ISO 8601 timestamp recorded at write time. */
  ts: string;
  /** Whether the formal_ref resolved to a known Lean declaration. */
  pending_formal_verification?: boolean;
  /** Slug of a previous version this supersedes, if any. */
  improved_over?: string;
}

/** Result of a version write attempt. */
export type VersionWriteResult =
  | { ok: true; version: number; cas_key: string }
  | { ok: false; conflict: true; current_version: number; message: string };

/**
 * Read the current version for a slug from R2.
 * Returns 0 if no entry exists yet (first deposit).
 */
export async function getCurrentVersion(
  bucket: R2Bucket,
  slug: string
): Promise<{ version: number; pointer: CurrentPointer | null }> {
  const key = `semantic/by-id/${slug}/current`;
  const obj = await bucket.get(key);
  if (obj === null) return { version: 0, pointer: null };

  const text = await obj.text();
  const pointer = JSON.parse(text) as CurrentPointer;
  return { version: pointer.version, pointer };
}

/**
 * Attempt to write a new versioned entry and update the current pointer.
 *
 * @param bucket      - The R2 bucket bound to the worker.
 * @param slug        - URL-safe identifier for this semantic entry.
 * @param entry       - The versioned entry data to persist.
 * @param newVersion  - The version number to write (must be > current).
 *
 * Returns the version written and the CAS key on success, or a conflict
 * descriptor if the monotone constraint is violated.
 */
export async function writeVersion(
  bucket: R2Bucket,
  slug: string,
  entry: Omit<VersionedEntry, "version" | "ts">,
  newVersion: number
): Promise<VersionWriteResult> {
  // Read current version — must do this inside the write path to catch
  // any races (best-effort; R2 is not transactional, but single-author
  // use means true concurrent writes are extremely unlikely).
  const { version: currentVersion } = await getCurrentVersion(bucket, slug);

  if (newVersion <= currentVersion) {
    return {
      ok: false,
      conflict: true,
      current_version: currentVersion,
      message: `Monotone constraint violated: incoming version ${newVersion} is not greater than current version ${currentVersion}`,
    };
  }

  const ts = new Date().toISOString();
  const versionedEntry: VersionedEntry = {
    ...entry,
    version: newVersion,
    ts,
  };

  // Write immutable versioned object first.
  // In production, the bucket should have Object Lock in compliance mode
  // so these objects cannot be deleted or overwritten after writing.
  const versionKey = `semantic/by-id/${slug}/v${newVersion}`;
  await bucket.put(versionKey, JSON.stringify(versionedEntry), {
    httpMetadata: { contentType: "application/json" },
  });

  // Update the mutable current pointer.
  const currentPointer: CurrentPointer = {
    version: newVersion,
    hash: entry.hash,
    formal_ref: entry.formal_ref,
  };
  const currentKey = `semantic/by-id/${slug}/current`;
  await bucket.put(currentKey, JSON.stringify(currentPointer), {
    httpMetadata: { contentType: "application/json" },
  });

  return { ok: true, version: newVersion, cas_key: `cas/${entry.hash}` };
}

/**
 * Determine the next version to write.
 *
 * If the payload specifies an explicit version, validate it against
 * current.  If not, auto-increment from current.
 *
 * @returns The version to write, or null if the payload version conflicts.
 */
export function resolveNextVersion(
  currentVersion: number,
  payloadVersion?: number
): { version: number } | { conflict: true; current: number } {
  if (payloadVersion === undefined) {
    // Auto-increment.
    return { version: currentVersion + 1 };
  }
  if (payloadVersion <= currentVersion) {
    return { conflict: true, current: currentVersion };
  }
  return { version: payloadVersion };
}
