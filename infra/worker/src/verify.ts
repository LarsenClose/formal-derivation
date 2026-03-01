/**
 * Ed25519 signature verification.
 *
 * Uses @noble/ed25519 for pure-JS, audited Ed25519 over the standard
 * RFC 8032 curve.  All key and signature material is expected as
 * base64url or base64 strings on the wire and converted here.
 */

import * as ed from "@noble/ed25519";

/**
 * Decode a base64 or base64url string to Uint8Array.
 * Both variants are accepted because JSON consumers use plain base64
 * while URL-safe variants appear in some signing libraries.
 */
function decodeBase64(b64: string): Uint8Array {
  // Normalise base64url -> base64.
  const padded = b64
    .replace(/-/g, "+")
    .replace(/_/g, "/")
    .padEnd(Math.ceil(b64.length / 4) * 4, "=");

  const binary = atob(padded);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return bytes;
}

/**
 * Result of a signature verification attempt.
 */
export interface VerifyResult {
  valid: boolean;
  reason?: string;
}

/**
 * Verify an Ed25519 signature over a message.
 *
 * @param message   - The raw bytes that were signed (BLAKE3 hash of canonical JSON).
 * @param sigB64    - Base64 or base64url-encoded signature (64 bytes).
 * @param pubkeyB64 - Base64 or base64url-encoded public key (32 bytes).
 * @returns         { valid: true } on success, { valid: false, reason } on failure.
 */
export async function verifySignature(
  message: Uint8Array,
  sigB64: string,
  pubkeyB64: string
): Promise<VerifyResult> {
  let sig: Uint8Array;
  let pubkey: Uint8Array;

  try {
    sig = decodeBase64(sigB64);
  } catch {
    return { valid: false, reason: "sig: invalid base64" };
  }

  try {
    pubkey = decodeBase64(pubkeyB64);
  } catch {
    return { valid: false, reason: "pubkey: invalid base64" };
  }

  if (sig.length !== 64) {
    return {
      valid: false,
      reason: `sig: expected 64 bytes, got ${sig.length}`,
    };
  }
  if (pubkey.length !== 32) {
    return {
      valid: false,
      reason: `pubkey: expected 32 bytes, got ${pubkey.length}`,
    };
  }

  try {
    const ok = await ed.verifyAsync(sig, message, pubkey);
    if (!ok) return { valid: false, reason: "signature does not verify" };
    return { valid: true };
  } catch (err) {
    return {
      valid: false,
      reason: `verification error: ${(err as Error).message}`,
    };
  }
}
