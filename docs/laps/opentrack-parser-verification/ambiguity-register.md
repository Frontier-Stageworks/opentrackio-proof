# Ambiguity Register — OpenTrackIO Parser Verification

Ambiguities that are unresolved as of 2026-05-17. Each entry records what is
unknown, why it blocks progress, and what resolution is needed before the
affected slice can open.

---

## A1 — JSON numeric representation for rational values

**Status:** UNRESOLVED  
**Blocks:** Slice 5 (Rational Decoder)

**What is unknown:**  
How are rational-typed fields (e.g., `sampleRate`, `focalLength`) encoded in
the OpenTrackIO JSON? Options include:
- JSON number (decimal or integer literal)
- JSON object `{ "num": ..., "den": ... }`
- JSON string `"num/den"`
- JSON integer only (for integer-valued rationals)

**Why it matters:**  
`decodePositiveRational` must pattern-match on a specific JSON constructor.
A wrong assumption here means the decoder and its soundness theorem describe
a format that the real protocol does not use.

**Resolution needed:**  
Inspect the canonical OpenTrackIO schema / camdkit Python source for at least
one rational-typed field and confirm which JSON form it uses.

---

## A2 — Duplicate object key semantics

**Status:** RESOLVED (2026-05-17)  
**Blocks:** Slice 2 (`JsonValue.lookup?`) — unblocked. Slice 12 (completeness) — still open.

**Policy:** OpenTrackIO-conforming JSON objects must have unique member names.
Duplicate keys are a **decoding error**, not first-wins or last-wins.

**Implementation:**
- `JsonValue.object` holds a raw `List (String × JsonValue)` that may contain
  duplicate keys. The raw model does not enforce uniqueness.
- `JsonValue.lookup?` is a first-match scan utility on this raw list.
  It is **not** presented as normative: the module comment and proof capsule
  explicitly state that normative field access requires a `NoDupKeys` proof,
  deferred to a later slice.
- Duplicate-key validation (checker + soundness theorem) is a future slice.

---

## A3 — Unknown-field policy

**Status:** UNRESOLVED  
**Blocks:** Slice 12 (completeness), Slice 16 (normalization)

**What is unknown:**  
Does the decoder silently ignore unrecognized fields, or reject them with an
error?

**Why it matters:**  
Completeness requires knowing whether extra fields cause rejection. Soundness
is not blocked (extra fields cannot make an accepted value invalid), but the
decoder implementation depends on this policy.

**Resolution needed:**  
Check OpenTrackIO spec language on forward compatibility / unknown-field
handling. If unspecified, pick a policy and document it.

---

## A4 — Optional and default field behavior

**Status:** UNRESOLVED  
**Blocks:** Slices 9–11 (Camera, Lens, Sample)

**What is unknown:**  
Which fields are required vs. optional? For optional fields: is a missing
field represented as `Option.none`, a protocol-specified default, or an error?

**Why it matters:**  
`ValidCamera`, `ValidLens`, and `ValidSample` must encode which fields are
required. If the decoder silently defaults a missing optional field, the
soundness theorem must characterize that default.

**Resolution needed:**  
For each protocol record (Camera, Lens, Transform, Sample), enumerate which
fields are normatively required and what the default is for each optional field.

---

## A5 — Enum spelling and canonicalization

**Status:** UNRESOLVED  
**Blocks:** Slice 7 (Enum-Like Fields)

**What is unknown:**  
What are the normative string values for each enum field? Examples:
- coordinate system: `"opencv"` vs `"OpenCV"` vs `"OPENCV"`
- projection type: `"pinhole"` vs `"perspective"`
- distortion model name: exact string

Is case folding applied? Are unknown enum values rejected or passed through?

**Why it matters:**  
`decodeCoordinateSystem` must match exact strings. Any canonicalization must
be proved correct.

**Resolution needed:**  
List the exact normative strings for each enum from the spec. Record whether
case folding is applied.

---

## A6 — Exact array lengths for lens coefficient arrays

**Status:** UNRESOLVED  
**Blocks:** Slice 6 (Fixed-Length Array Decoder), Slice 10 (Lens Model)

**What is unknown:**  
OpenCV uses up to 6 radial coefficients (k1–k6) and 2 tangential (p1, p2).
OpenTrackIO uses l1, l3, l5, l2, l4, l6 and q1, q2.
Questions:
- Are all 8 coefficients always required, or is a shorter array allowed?
- Is an array of exactly 3 radial numerator coefficients required?
- Are the arrays indexed positionally?

**Why it matters:**  
`decodeVec3` or a specialized `decodeRadialCoeffs` must check the exact length.
The soundness theorem must state the length invariant.

**Resolution needed:**  
Check the spec for array-length constraints on `radialDistortion` and
`tangentialDistortion` fields.

---

## A7 — Rational representation: types vs. `ValidX` predicates

**Status:** DESIGN DECISION (not a spec question)  
**Blocks:** Slice 1 (Rational Value Wrappers)

**What is unknown:**  
Should invariants (denominator > 0, numerator > 0) live in the Lean type
constructor or in a `ValidX : X → Prop`?

**Why it matters:**  
- Invariants in the type: constructors enforce them; decoder returns a value
  that is already valid by construction; soundness theorem proves a semantic
  fact (e.g., `0 < r.toReal`).
- `ValidX` predicate: more flexible; decoder returns a plain value plus a
  proof of `ValidX`.

**Resolution needed:**  
Decision: **prefer invariants in types** (per project guardrails in the plan).
`PositiveRational` carries `num_pos : num > 0` and `den_pos : den > 0` as
struct fields. This is the approach for Slice 1.

**Status:** RESOLVED (design decision) — invariants in types.

---

## A8 — Protocol field names and version policy

**Status:** UNRESOLVED  
**Blocks:** Slices 4, 9, 10, 11, 12

**What is unknown:**  
- What are the exact JSON key names for each field? (e.g., is it `"camera"`,
  `"Camera"`, or something else? Is it `"lens.focalLength"` or `"focalLength"`
  under a `"lens"` object?)
- Does the decoder need to validate the protocol version field before decoding
  the rest?
- Are field names stable across protocol versions?

**Why it matters:**  
Every `requireField key j` call embeds a string literal. Wrong key names
produce a decoder that accepts the wrong JSON.

**Resolution needed:**  
Extract the normative field name table from the OpenTrackIO schema and the
camdkit Python source. Lock down the key strings before Slice 4.

---

## A9 — Quaternion normalization requirement

**Status:** UNRESOLVED  
**Blocks:** Slice 8 (Transform Model)

**What is unknown:**  
Does the protocol require that rotation quaternions have unit norm? Is
normalization checked by the decoder or assumed by the consumer?

**Why it matters:**  
`ValidTransform` may or may not include a normalization predicate. If it does,
the decoder must either enforce it (and prove the check) or document that
normalization is a consumer responsibility.

**Resolution needed:**  
Check the OpenTrackIO spec for quaternion constraints.

---

## A10 — Executable/differential harness relationship

**Status:** OUT OF SCOPE FOR PROOF SLICES  
**Blocks:** Nothing in Slices 1–15

**What is unknown:**  
The battery-tester harness (`battery-tester/`) compares Python and C++
implementations. How does the proved Lean decoder relate to it? Options:
- Lean decoder is a reference oracle for the harness
- Harness is purely empirical; Lean proofs are separate correctness argument
- A future Lean executable is extracted and used as the harness reference

**Why it matters:**  
The harness is currently not proved correct. The divergence on
`lens.pinholeFocalLength` in the May 2026 battery runs is an empirical finding,
not a proof failure.

**Resolution needed:**  
Treat this as a **future packaging slice** (Slice 16+). No Lean code for the
harness should appear in Slices 1–15. Record the decision here and do not
revisit it during implementation slices.

**Status:** DEFERRED — explicit packaging slice to be added to the work queue
after Slice 12.
