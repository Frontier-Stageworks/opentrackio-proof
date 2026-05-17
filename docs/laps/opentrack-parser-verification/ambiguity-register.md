# Ambiguity Register — OpenTrackIO Parser Verification

Ambiguities that are unresolved as of 2026-05-17. Each entry records what is
unknown, why it blocks progress, and what resolution is needed before the
affected slice can open.

---

## A1 — JSON numeric representation for rational values

**Status:** RESOLVED (2026-05-17)  
**Blocks:** Slice 5 — unblocked.

**Resolution:**  
Rational-typed fields are JSON objects with exactly two required fields:

```json
{ "num": 24000, "denom": 1001 }
```

Normative key names: `"num"` and `"denom"` (not `"den"`, not `"denominator"`).

Schema constraints per field:
- `num`: integer, minimum 1, maximum 2147483647
- `denom`: integer, minimum 1, maximum 4294967295
- `required: ["num", "denom"]`, `additionalProperties: false`

Fields using this shape: `static.duration`, `static.camera.captureFrameRate`,
`static.camera.anamorphicSqueeze`, `timing.sampleRate`,
`timing.synchronization.frequency`, `timing.timecode.frameRate`.

**Important clarification:** focal length fields (`lens.pinholeFocalLength`,
`static.lens.nominalFocalLength`) are plain JSON numbers (not rational objects).
They have `exclusiveMinimum: 0.0` and are handled separately (Slice 10).

**Lean impact:**  
`decodePositiveRational` pattern-matches on `.object _`, looks up `"num"` and
`"denom"`, parses each as a `Nat` via `s.toNat?`, and checks `0 < n` and
`0 < d` to satisfy `PositiveRational.num_pos` and `PositiveRational.den_pos`.
The maximum bounds (2147483647 / 4294967295) are not encoded in the decoder
for Slice 5 — they are a future constraint if needed.

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

**Status:** PARTIALLY RESOLVED (2026-05-17) — protocol sub-tree resolved; remaining top-level fields still open.  
**Blocks:** Slice 4C — unblocked. Slices 9, 10, 11, 12 — still blocked on remaining fields.

**Resolved: protocol sub-tree**

Normative key names confirmed from the OpenTrackIO schema:

```
protocol               (top-level object; optional for consumers; required sub-fields when present)
  protocol.name        (string; "OpenTrackIO" in practice; no value constraint imposed by decoder)
  protocol.version     (array of exactly 3 integers, each 0..9; decoded by VersionDecoder)
```

Notes:
- `protocol.name` and `protocol.version` are the exact key strings.
- Both sub-fields are required when the `protocol` object is present.
- Dynamic lens focal length is `lens.pinholeFocalLength`; static is `static.lens.nominalFocalLength`.
- Top-level fields are camelCase: `sampleId`, `sourceId`, `sourceNumber`, `relatedSampleIds`, `globalStage`, `transforms`.
- The schema states all described fields should be considered optional by consumers, but sub-fields within an object are required once the object is present.

**Still unresolved: broader field tree**

The full field tree has been provided and is recorded for reference, but the following
fields are not yet locked down for Lean decoder use (sub-tree required by Slices 9–12):

```
static.camera.*        (captureFrameRate, activeSensorResolution, make, model, ...)
static.lens.*          (nominalFocalLength, make, model, ...)
lens.*                 (pinholeFocalLength, focusDistance, distortion, ...)
timing.*               (sampleRate, sampleTimestamp, timecode, ...)
transforms[]           (translation, rotation, scale, id)
globalStage            (E, N, U, lat0, lon0, h0)
tracker.*              (make, model, serialNumber, ...)
```

These will be resolved per slice as needed.

---

## A11 — Version arity: major/minor vs. major/minor/patch

**Status:** RESOLVED (2026-05-17)  
**Blocks:** Slice 4A, 4B — unblocked.

**Decision:** Version arity is exactly **3** (major, minor, patch).

The normative OpenTrackIO schema defines `protocol.version` as an array with
`minItems: 3`, `maxItems: 3`, each item an integer with `minimum: 0`,
`maximum: 9`. The fixture `[1, 0, 1]` is consistent with the schema.

**Lean representation:** Use `Fin 10` for each component so the digit bound
`[0, 9]` is encoded in the type:

```lean
abbrev VersionDigit := Fin 10

structure ProtocolVersion where
  major : VersionDigit
  minor : VersionDigit
  patch : VersionDigit
```

**Constraint NOT encoded in 4A:** The specific current-documentation value
`[1, 0, 1]` is not constrained — the schema does not restrict consumers to
reject other triples. `ValidVersion` expresses the digit-bound invariant,
not the current-version value.

---

## A12 — Version JSON shape: array vs. object vs. string

**Status:** RESOLVED (2026-05-17)  
**Blocks:** Slice 4B, 4C — unblocked.

**Decision:** `protocol.version` is a **JSON array of exactly three integers**.

Schema: `type: "array"`, integer items, `minItems: 3`, `maxItems: 3`.
Not an object, not a string.

`decodeVersion` (Slice 4B) must pattern-match on `JsonValue.array` and
check that the list has exactly 3 `JsonValue.number` elements whose string
values parse as integers in `[0, 9]`.

---

## A13 — `ValidVersion` protocol constraints

**Status:** RESOLVED (2026-05-17)  
**Blocks:** Slice 4A — unblocked.

**Decision:** `ValidVersion` must not be `True`. It must encode the published
schema constraint that each component is a digit in `[0, 9]`.

**Chosen form:**

```lean
def ValidVersion (v : ProtocolVersion) : Prop :=
  v.major.val ≤ 9 ∧ v.minor.val ≤ 9 ∧ v.patch.val ≤ 9
```

With `VersionDigit := Fin 10`, each field already carries `isLt : val < 10`,
making `ValidVersion v` provable for any `v : ProtocolVersion` via
`Nat.le_of_lt`. This is non-vacuous: the proof has real content (converting
`< 10` to `≤ 9`) and the predicate expresses the normative schema bound.

**Not encoded:** The specific value `[1, 0, 1]` is not constrained.
The schema does not require consumers to reject other version triples.

**4A theorem target:**

```lean
theorem protocolVersion_valid (v : ProtocolVersion) : ValidVersion v
```

This is the soundness lemma that any constructed `ProtocolVersion` satisfies
the digit-bound invariant — a prerequisite for decoder soundness in 4B.

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
