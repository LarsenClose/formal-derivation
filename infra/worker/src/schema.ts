/**
 * Payload schema validation.
 *
 * The minimum valid deposit is { formal_ref, note, depth, compression_loss }.
 * All optional fields are accepted but never required.
 *
 * Unresolvable formal_refs are accepted and flagged pending_formal_verification
 * by the caller; this module does not perform R2 lookups.
 */

/** Full deposit payload as sent by the depositor. */
export interface DepositPayload {
  /** Lean declaration name, e.g. "Reception.DiamondPoint". */
  formal_ref: string;
  /** Human-readable note / description. */
  note: string;
  /** Epistemic depth in [1, 10]. */
  depth: number;
  /** Compression loss in [1, 10]. */
  compression_loss: number;

  // Optional fields.
  /** Slug-style identifier for the semantic entry. Generated from formal_ref if absent. */
  id?: string;
  /** Human-readable title. */
  title?: string;
  /** Free-form tags. */
  tags?: string[];
  /**
   * Monotone version counter.  If omitted the worker reads the current
   * version from R2 and uses N+1.  If provided it must be > current version.
   */
  version?: number;
  /** Reference to a previous version this deposit supersedes. */
  improved_over?: string;
}

/** The signed envelope posted to POST /deposit. */
export interface DepositEnvelope {
  payload: DepositPayload;
  /** Base64 or base64url Ed25519 signature over blake3(canonical_json(payload)). */
  sig: string;
  /** Base64 or base64url Ed25519 public key (32 bytes). */
  pubkey: string;
}

/** Structured validation error. */
export interface ValidationError {
  field: string;
  message: string;
}

/** Result of validating an envelope. */
export type ValidationResult =
  | { ok: true; envelope: DepositEnvelope }
  | { ok: false; errors: ValidationError[] };

/**
 * Validate a raw JSON body as a DepositEnvelope.
 *
 * Returns the typed envelope on success or a list of field-level errors
 * on failure.  Does NOT verify the Ed25519 signature — that is the
 * caller's responsibility after validation.
 */
export function validateEnvelope(raw: unknown): ValidationResult {
  const errors: ValidationError[] = [];

  if (raw === null || typeof raw !== "object" || Array.isArray(raw)) {
    return {
      ok: false,
      errors: [{ field: "root", message: "body must be a JSON object" }],
    };
  }

  const body = raw as Record<string, unknown>;

  // Top-level required fields.
  if (typeof body["sig"] !== "string" || body["sig"].trim() === "") {
    errors.push({ field: "sig", message: "required string" });
  }
  if (typeof body["pubkey"] !== "string" || body["pubkey"].trim() === "") {
    errors.push({ field: "pubkey", message: "required string" });
  }
  if (body["payload"] === null || typeof body["payload"] !== "object") {
    errors.push({ field: "payload", message: "required object" });
    // Cannot continue without a payload object.
    return { ok: false, errors };
  }

  const p = body["payload"] as Record<string, unknown>;

  // Required payload fields.
  if (typeof p["formal_ref"] !== "string" || p["formal_ref"].trim() === "") {
    errors.push({ field: "payload.formal_ref", message: "required string" });
  }
  if (typeof p["note"] !== "string" || p["note"].trim() === "") {
    errors.push({ field: "payload.note", message: "required string" });
  }

  // depth: integer in [1, 10].
  if (typeof p["depth"] !== "number" || !Number.isInteger(p["depth"])) {
    errors.push({ field: "payload.depth", message: "required integer" });
  } else if (p["depth"] < 1 || p["depth"] > 10) {
    errors.push({
      field: "payload.depth",
      message: "must be between 1 and 10 inclusive",
    });
  }

  // compression_loss: integer in [1, 10].
  if (
    typeof p["compression_loss"] !== "number" ||
    !Number.isInteger(p["compression_loss"])
  ) {
    errors.push({
      field: "payload.compression_loss",
      message: "required integer",
    });
  } else if (p["compression_loss"] < 1 || p["compression_loss"] > 10) {
    errors.push({
      field: "payload.compression_loss",
      message: "must be between 1 and 10 inclusive",
    });
  }

  // Optional: id (string slug).
  if (p["id"] !== undefined) {
    if (typeof p["id"] !== "string" || p["id"].trim() === "") {
      errors.push({
        field: "payload.id",
        message: "if provided, must be a non-empty string",
      });
    } else if (!/^[a-z0-9-]+$/.test(p["id"])) {
      errors.push({
        field: "payload.id",
        message: "must contain only lowercase letters, digits, and hyphens",
      });
    }
  }

  // Optional: title (string).
  if (p["title"] !== undefined && typeof p["title"] !== "string") {
    errors.push({
      field: "payload.title",
      message: "if provided, must be a string",
    });
  }

  // Optional: tags (array of strings).
  if (p["tags"] !== undefined) {
    if (!Array.isArray(p["tags"])) {
      errors.push({
        field: "payload.tags",
        message: "if provided, must be an array of strings",
      });
    } else if (p["tags"].some((t) => typeof t !== "string")) {
      errors.push({
        field: "payload.tags",
        message: "all tag values must be strings",
      });
    }
  }

  // Optional: version (positive integer).
  if (p["version"] !== undefined) {
    if (
      typeof p["version"] !== "number" ||
      !Number.isInteger(p["version"]) ||
      p["version"] < 1
    ) {
      errors.push({
        field: "payload.version",
        message: "if provided, must be a positive integer",
      });
    }
  }

  // Optional: improved_over (string).
  if (
    p["improved_over"] !== undefined &&
    typeof p["improved_over"] !== "string"
  ) {
    errors.push({
      field: "payload.improved_over",
      message: "if provided, must be a string",
    });
  }

  if (errors.length > 0) {
    return { ok: false, errors };
  }

  return {
    ok: true,
    envelope: body as unknown as DepositEnvelope,
  };
}

/**
 * Derive a URL-safe slug from a formal_ref or explicit id.
 * "Reception.DiamondPoint" -> "reception-diamond-point"
 */
export function slugFromRef(ref: string): string {
  return ref
    .replace(/\./g, "-")
    .replace(/([a-z])([A-Z])/g, "$1-$2")
    .toLowerCase()
    .replace(/[^a-z0-9-]/g, "-")
    .replace(/-+/g, "-")
    .replace(/^-|-$/g, "");
}
