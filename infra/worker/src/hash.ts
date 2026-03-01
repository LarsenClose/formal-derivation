/**
 * BLAKE3 content addressing.
 *
 * Computes BLAKE3 hashes and encodes them as base58 strings for
 * human-legible, self-describing content-addressable keys.
 */

import { blake3 } from "@noble/hashes/blake3";

// Base58 alphabet (Bitcoin-style, no 0/O/I/l ambiguity).
const BASE58_ALPHABET =
  "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";

/**
 * Encode a Uint8Array as a base58 string.
 */
export function base58Encode(bytes: Uint8Array): string {
  // Count leading zero bytes.
  let leadingZeros = 0;
  for (const b of bytes) {
    if (b !== 0) break;
    leadingZeros++;
  }

  // Convert big-endian bytes to a big integer via intermediate array.
  const digits: number[] = [0];
  for (const byte of bytes) {
    let carry = byte;
    for (let i = 0; i < digits.length; i++) {
      carry += digits[i] << 8;
      digits[i] = carry % 58;
      carry = Math.floor(carry / 58);
    }
    while (carry > 0) {
      digits.push(carry % 58);
      carry = Math.floor(carry / 58);
    }
  }

  // Map to alphabet, prepend leading '1's for leading zero bytes.
  const result = "1".repeat(leadingZeros);
  const encoded = digits
    .reverse()
    .map((d) => BASE58_ALPHABET[d])
    .join("");
  return result + encoded;
}

/**
 * Decode a base58 string to a Uint8Array.
 * Throws if the string contains characters outside the alphabet.
 */
export function base58Decode(str: string): Uint8Array {
  let leadingZeros = 0;
  for (const ch of str) {
    if (ch !== "1") break;
    leadingZeros++;
  }

  const digits: number[] = [0];
  for (const ch of str) {
    const idx = BASE58_ALPHABET.indexOf(ch);
    if (idx < 0) throw new Error(`Invalid base58 character: ${ch}`);
    let carry = idx;
    for (let i = 0; i < digits.length; i++) {
      carry += digits[i] * 58;
      digits[i] = carry & 0xff;
      carry >>= 8;
    }
    while (carry > 0) {
      digits.push(carry & 0xff);
      carry >>= 8;
    }
  }

  const result = new Uint8Array(leadingZeros + digits.length);
  digits.reverse().forEach((b, i) => {
    result[leadingZeros + i] = b;
  });
  return result;
}

/**
 * Hash arbitrary bytes with BLAKE3 and return a base58-encoded string.
 */
export function blake3Hash(data: Uint8Array | string): string {
  const input =
    typeof data === "string" ? new TextEncoder().encode(data) : data;
  const hash = blake3(input);
  return base58Encode(hash);
}

/**
 * Produce a stable canonical JSON string from an object.
 * Keys are sorted recursively so the same logical value always
 * produces the same byte sequence.
 */
export function canonicalJson(obj: unknown): string {
  if (obj === null || typeof obj !== "object") {
    return JSON.stringify(obj);
  }
  if (Array.isArray(obj)) {
    return "[" + obj.map(canonicalJson).join(",") + "]";
  }
  const sorted = Object.keys(obj as Record<string, unknown>)
    .sort()
    .map((k) => {
      const v = canonicalJson((obj as Record<string, unknown>)[k]);
      return `${JSON.stringify(k)}:${v}`;
    })
    .join(",");
  return "{" + sorted + "}";
}

/**
 * Hash a JSON-serialisable payload deterministically.
 * Returns base58-encoded BLAKE3 of canonical JSON.
 */
export function hashPayload(payload: unknown): string {
  return blake3Hash(canonicalJson(payload));
}
