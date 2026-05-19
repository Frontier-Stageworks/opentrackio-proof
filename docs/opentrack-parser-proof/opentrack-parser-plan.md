# OpenTrackIO Parser Verification Plan

This plan breaks the OpenTrackIO decoding/validation verification project into small, LAPS-sized chunks.

Project frame:

> Prove that OpenTrackIO decoding/validation is correct with respect to a formal protocol model.

The goal is **not** to prove that a parser accepts raw bytes. The goal is:

> Given a JSON value, the decoder either rejects it for a valid protocol reason, or returns a well-formed OpenTrackIO value satisfying all required invariants.

Primary long-term theorem shape:

```lean
theorem decode_sample_sound :
  decodeSample j = Except.ok s →
  ValidSample s
```

Meaning:

> If the decoder accepts some JSON, the resulting sample is semantically valid.

Later, where practical:

```lean
theorem decode_sample_complete :
  JsonConformsToOpenTrackIO j →
  ∃ s, decodeSample j = Except.ok s
```

Meaning:

> If the JSON really conforms to the spec, the decoder does not reject it incorrectly.

Do not start with the top-level theorem. Build it by small soundness layers.

---

## LAPS Strategy

Each slice should be small enough to complete without proof spirals.

For every slice:

1. Use LAPS.
2. Create theorem-scoped or task-scoped artifacts under `docs/laps/<slice-slug>/`.
3. State the intended model or theorem before implementation.
4. Keep raw JSON and semantic protocol values separate.
5. Prefer invariants in types where obvious.
6. Prove local soundness before composing top-level soundness.
7. Stop and create a work queue if the slice expands beyond its stated scope.

---

## Slice 1 — Rational Value Wrappers

### Goal

Define rational-like protocol value types whose constructors encode denominator and sign invariants.

### Scope

Create only:

```lean
structure RationalWithPositiveDenominator where
  num : Int
  den : Nat
  den_pos : den > 0

structure NonnegativeRational where
  num : Nat
  den : Nat
  den_pos : den > 0

structure PositiveRational where
  num : Nat
  den : Nat
  num_pos : num > 0
  den_pos : den > 0
```

Optional evaluation functions:

```lean
def RationalWithPositiveDenominator.toRat : RationalWithPositiveDenominator → ℚ
def NonnegativeRational.toRat : NonnegativeRational → ℚ
def PositiveRational.toRat : PositiveRational → ℚ
```

or, if the project prefers real-valued semantics:

```lean
def RationalWithPositiveDenominator.toReal : RationalWithPositiveDenominator → ℝ
def NonnegativeRational.toReal : NonnegativeRational → ℝ
def PositiveRational.toReal : PositiveRational → ℝ
```

### Theorems

Examples:

```lean
theorem rational_with_positive_denominator_den_ne_zero ...
theorem nonnegative_rational_den_ne_zero ...
theorem positive_rational_den_ne_zero ...
theorem positive_rational_num_ne_zero ...
theorem positive_rational_toRat_pos ...
```

### LAPS classification

Small.

### Forbidden

- No JSON.
- No protocol records.
- No decoder.
- No parser.
- No OpenTrackIO schema.
- No serialization.
- No roundtrip theorem.

---

## Slice 2 — Tiny Raw JSON Model

### Goal

Define a raw JSON-facing syntax type that can contain invalid data.

The raw layer may contain nonsense. The semantic layer should not.

### Scope

```lean
inductive JsonValue
  | null
  | bool : Bool → JsonValue
  | number : String → JsonValue
  | string : String → JsonValue
  | array : List JsonValue → JsonValue
  | object : List (String × JsonValue) → JsonValue
```

Add basic lookup helpers:

```lean
def JsonValue.lookup? : JsonValue → String → Option JsonValue
def JsonValue.hasField : JsonValue → String → Prop
```

### Theorems

Keep tiny:

```lean
theorem lookup?_some_implies_field_present ...
theorem lookup?_none_implies_no_matching_field ...
```

Only prove what is needed for decoders.

### LAPS classification

Small.

### Forbidden

- No full JSON parser.
- No duplicate-key policy unless explicitly modeled.
- No protocol schema.
- No decoder beyond lookup helpers.

---

## Slice 3 — Decode Error Vocabulary

### Goal

Define structured reasons a decoder can reject input.

### Scope

```lean
inductive DecodeError
  | expectedObject
  | expectedArray
  | expectedString
  | expectedNumber
  | missingField : String → DecodeError
  | invalidRational : String → DecodeError
  | invalidEnum : String → String → DecodeError
  | invalidLength : String → Nat → Nat → DecodeError
```

The exact constructors should track the protocol and implementation needs, but this slice should only establish the error vocabulary.

### Theorems

Probably none required yet, except maybe simple discriminators or equality facts if useful.

### LAPS classification

Small.

### Forbidden

- No decoder implementation beyond helper constructors.
- No top-level soundness theorem.
- No protocol model.

---

## Slice 4 — Version Model and Decoder

### Goal

Create the first real decoder, but for a very small protocol object.

### Semantic model

```lean
structure Version where
  major : Nat
  minor : Nat
```

Possibly:

```lean
def ValidVersion (v : Version) : Prop := ...
```

If version validity is fully encoded in the type, `ValidVersion` can be simple. If the protocol has a fixed major version or range constraints, record them here.

### Decoder

```lean
def decodeVersion : JsonValue → Except DecodeError Version
```

### Soundness theorem

```lean
theorem decode_version_sound :
  decodeVersion j = Except.ok v →
  ValidVersion v
```

### LAPS classification

Small.

### Forbidden

- No Sample.
- No Camera.
- No Lens.
- No completeness theorem.
- No error correctness unless trivial.

---

## Slice 5 — Rational Decoder

### Goal

Decode raw JSON rational-like values into invariant-carrying rational types.

### Key ambiguity

Decide the JSON representation first:

- JSON number string?
- object `{ "num": ..., "den": ... }`?
- string rational?
- decimal?
- integer-only representation?

This is a key ambiguity. LAPS should stop if the concrete JSON representation is not fixed.

### Decoder examples

```lean
def decodePositiveRational : JsonValue → Except DecodeError PositiveRational
def decodeNonnegativeRational : JsonValue → Except DecodeError NonnegativeRational
```

### Soundness

If the invariants are in the type, avoid proving only `True`. Instead prove a semantic fact:

```lean
theorem decode_positive_rational_returns_positive :
  decodePositiveRational j = Except.ok r →
  0 < r.toRat
```

or:

```lean
theorem decode_nonnegative_rational_returns_nonnegative :
  decodeNonnegativeRational j = Except.ok r →
  0 ≤ r.toRat
```

### LAPS classification

Medium, because numeric parsing can spiral.

### Forbidden

- No full sample decoder.
- No schema-wide validation.
- No completeness unless representation is fully fixed and simple.

---

## Slice 6 — Fixed-Length Arrays / Vector Decoder

### Goal

Decode protocol arrays whose length is fixed by the spec.

Examples:

- 2D point
- 3D vector
- transform matrix row
- quaternion
- lens coefficient arrays

### Model options

Concrete structures:

```lean
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ
```

or stronger indexing:

```lean
def Vec (n : Nat) := Fin n → ℝ
```

Prefer the simplest model that supports the protocol invariants.

### Decoder

```lean
def decodeVec3 : JsonValue → Except DecodeError Vec3
```

### Soundness

```lean
theorem decode_vec3_sound :
  decodeVec3 j = Except.ok v →
  ValidVec3 v
```

If `Vec3` itself guarantees dimensionality, `ValidVec3` may be simple. The theorem should still document that only exact-length arrays decode.

### LAPS classification

Small-to-medium.

### Forbidden

- No camera/lens model yet.
- No transform semantics yet.
- No matrix/quaternion equivalence theorem yet.

---

## Slice 7 — Enum-Like Fields

### Goal

Model legal enum/string fields.

Examples:

- coordinate system
- units
- projection type
- distortion model name
- protocol version tag

### Model

```lean
inductive CoordinateSystem
  | opencv
  | opentrackio
  | screen
```

### Decoder

```lean
def decodeCoordinateSystem : JsonValue → Except DecodeError CoordinateSystem
```

### Soundness

If validity is by construction, prove a more useful theorem than `True`:

```lean
theorem decode_coordinate_system_known_string :
  decodeCoordinateSystem j = Except.ok c →
  ∃ s, j = JsonValue.string s ∧ stringNamesCoordinateSystem s c
```

or:

```lean
theorem decode_coordinate_system_sound :
  decodeCoordinateSystem j = Except.ok c →
  ValidCoordinateSystem c
```

### LAPS classification

Small.

### Forbidden

- No Sample.
- No full schema.
- No unknown-field policy unless needed for this decoder.

---

## Slice 8 — Transform Model

### Goal

Define transform values with dimensionality invariants.

### Model

Start concrete:

```lean
structure Transform where
  translation : Vec3
  rotation : Quaternion
```

Then separately decide whether quaternion normalization is required:

```lean
def ValidQuaternion (q : Quaternion) : Prop := ...
def ValidTransform (t : Transform) : Prop := ...
```

### Decoder

```lean
def decodeTransform : JsonValue → Except DecodeError Transform
```

### Soundness

```lean
theorem decode_transform_sound :
  decodeTransform j = Except.ok t →
  ValidTransform t
```

### Ambiguities to expose

- Is quaternion normalization required by spec or merely recommended?
- Are matrices allowed?
- Are absent transforms defaulted or rejected?
- Are coordinate-system fields required here or at the sample level?

### LAPS classification

Medium.

### Forbidden

- No Camera.
- No Lens.
- No Sample.
- No full pipeline theorem.

---

## Slice 9 — Camera Model

### Goal

Define the semantic camera record and decoder.

### Model sketch

```lean
structure Camera where
  width : PositiveRational
  height : PositiveRational
  principalPoint : Point2
  focalLength : PositiveRational
```

Actual fields depend on the spec.

### Validity

Prefer invariants in types where obvious. Use `ValidCamera` only for cross-field invariants.

```lean
def ValidCamera (c : Camera) : Prop :=
  ...
```

### Decoder

```lean
def decodeCamera : JsonValue → Except DecodeError Camera
```

### Soundness

```lean
theorem decode_camera_sound :
  decodeCamera j = Except.ok c →
  ValidCamera c
```

### Ambiguities to expose

- Are width and height integer pixels, rationals, or positive reals?
- Is principal point allowed outside the image bounds?
- Are focal lengths required positive?
- Does the protocol allow separate `fx` and `fy`, or a single scalar `F`?
- Are missing fields rejected or defaulted?

### LAPS classification

Medium-to-large. If it grows, split by field group.

### Forbidden

- No Lens.
- No Sample.
- No roundtrip.
- No full OpenTrackIO schema.

---

## Slice 10 — Lens Model

### Goal

Define lens parameters and decoder.

### Model sketch

```lean
structure Lens where
  focalLength : PositiveRational
  principalPoint : Point2
  radial : Option RadialDistortion
  tangential : Option TangentialDistortion
```

Actual fields depend on the spec.

### Decoder

```lean
def decodeLens : JsonValue → Except DecodeError Lens
```

### Soundness

```lean
theorem decode_lens_sound :
  decodeLens j = Except.ok l →
  ValidLens l
```

### Ambiguities to expose

- Which focal-length key is normative?
- What defaults exist for missing distortion?
- Are coefficient arrays exact-length?
- Are units fixed?
- Are distortion coefficients rationals, decimals, or arbitrary real-valued numeric fields?
- Are OpenCV/OpenTrackIO conversion formulas part of this model or a separate theorem layer?

### LAPS classification

Medium-to-large; likely needs a work queue.

### Forbidden

- No Sample.
- No full pixel equivalence theorem.
- No roundtrip.

---

## Slice 11 — Sample Model Shell

### Goal

Define the top-level semantic sample record, but do not prove decoder soundness yet.

### Model

```lean
structure Sample where
  version : Version
  camera : Camera
  lens : Lens
  transform : Option Transform
```

### Validity

```lean
def ValidSample (s : Sample) : Prop :=
  ValidVersion s.version ∧
  ValidCamera s.camera ∧
  ValidLens s.lens ∧
  ...
```

### Theorems

Just prove decomposition lemmas:

```lean
theorem valid_sample_camera :
  ValidSample s → ValidCamera s.camera

theorem valid_sample_lens :
  ValidSample s → ValidLens s.lens
```

### LAPS classification

Small-to-medium.

### Forbidden

- No `decodeSample` yet.
- No roundtrip.
- No completeness.
- No unknown-field policy unless already modeled.

---

## Slice 12 — Compose Decoder Soundness

### Goal

Define `decodeSample` using already-proven sub-decoders.

### Decoder

```lean
def decodeSample : JsonValue → Except DecodeError Sample
```

### Main soundness theorem

```lean
theorem decode_sample_sound :
  decodeSample j = Except.ok s →
  ValidSample s
```

### Proof strategy

Compose local soundness theorems:

```lean
decode_version_sound
decode_camera_sound
decode_lens_sound
decode_transform_sound
```

### LAPS classification

Medium.

This is the first time the original top-level soundness theorem should be attempted.

### Forbidden

- No completeness.
- No error correctness.
- No roundtrip.
- No new field semantics unless missing from earlier slices.
- No JSON parser.

---

## Slice 13 — Error Correctness for Required Fields

### Goal

Prove that missing required fields produce the correct error.

### Start tiny

```lean
theorem decode_sample_missing_camera :
  MissingRequiredField "camera" j →
  decodeSample j = Except.error (.missingField "camera")
```

### Better local shape

Prove helper-level errors first:

```lean
theorem lookup_required_missing :
  JsonValue.lookup? j key = none →
  requireField key j = Except.error (.missingField key)
```

### LAPS classification

Small if helper-level; large if top-level.

### Forbidden

- No complete error taxonomy.
- No roundtrip.
- No completeness theorem.

---

## Slice 14 — Encoder for One Small Type

### Goal

Add encoding only after decoding soundness exists.

Start with:

```lean
def encodeVersion : Version → JsonValue
```

### Roundtrip

```lean
theorem decode_encode_version_roundtrip :
  decodeVersion (encodeVersion v) = Except.ok v
```

### LAPS classification

Small.

### Forbidden

- No Sample encoder.
- No JSON normalization.
- No schema-wide roundtrip.

---

## Slice 15 — Encode/Decode Roundtrip by Component

### Goal

Add roundtrips component by component.

Suggested order:

1. Version
2. Rational wrappers
3. Vec2 / Vec3
4. Transform
5. Camera
6. Lens
7. Sample

The top-level theorem comes last:

```lean
theorem encode_decode_sample_roundtrip :
  ValidSample s →
  decodeSample (encodeSample s) = Except.ok s
```

### LAPS classification

Medium-to-large; split by component.

### Forbidden

- No decode/encode normalization theorem yet.
- No duplicate-key theorem yet.
- No field-ordering theorem yet.

---

## Slice 16 — Decode/Encode Normalization

### Goal

Only after canonical encoding is defined.

### Theorem

```lean
theorem decode_encode_normalizes :
  decodeSample j = Except.ok s →
  encodeSample s = normalizeJson j
```

### Requires decisions

- duplicate object key semantics;
- field ordering;
- optional default fields;
- numeric spelling normalization;
- ignored unknown fields;
- canonical enum spelling.

### LAPS classification

Large.

This requires a work queue and should not be attempted until the decoder and encoder are stable.

---

# Recommended First Five LAPS Tasks

Start here:

1. `rational-value-wrappers`
2. `json-raw-model`
3. `decode-error-vocabulary`
4. `version-decoder-soundness`
5. `rational-decoder-soundness`

Do not start with `Sample`.

---

# Suggested Prompt for First Task

```md
Use LAPS for this Lean modeling task.

Task: Define invariant-carrying rational value wrappers for protocol modeling.

Scope:
- Define `RationalWithPositiveDenominator`
- Define `NonnegativeRational`
- Define `PositiveRational`
- Add simple evaluation functions to `ℚ` or `ℝ`
- Prove basic invariant lemmas such as denominator nonzero and positive value for `PositiveRational`

Forbidden:
- No JSON model
- No decoder
- No parser
- No OpenTrackIO schema records
- No Sample, Camera, Lens, or Transform
- No serialization
- No roundtrip theorem

LAPS requirements:
- Classify the task size
- Create artifacts under `docs/laps/rational-value-wrappers/`
- Produce a proof capsule, statement audit, proof plan, and proof review
- If the task grows beyond rational wrappers, stop and create a work queue

Output:
- A small Lean file for rational wrappers
- The LAPS artifacts
- A final Lean check result
```

---

# Project Guardrails

## Keep Raw and Semantic Layers Separate

Raw JSON values can be invalid. Semantic protocol records should be well-formed by construction where possible.

Do not collapse these layers.

## Prefer Invariants in Types

Use types such as `PositiveRational`, exact-length vectors, and enum inductives to make invalid states hard or impossible to construct.

Use `ValidX : X → Prop` for cross-field or semantic invariants that cannot conveniently live in the type.

## Soundness Before Completeness

Prove accepted values are valid before proving valid JSON is accepted.

Order:

1. decoder soundness;
2. error correctness;
3. encode/decode roundtrip;
4. decoder completeness;
5. normalization.

## Local Soundness First

Every decoder should get a local soundness theorem before being used in a top-level decoder.

Examples:

```lean
theorem decode_rational_sound :
  decodeRational j = Except.ok r →
  ValidRational r

theorem decode_transform_sound :
  decodeTransform j = Except.ok t →
  ValidTransform t
```

Then compose:

```lean
theorem decode_sample_sound :
  decodeSample j = Except.ok s →
  ValidSample s
```

## Avoid Parser-Byte Scope Creep

This project is about semantic decoding/validation from a JSON AST, not proving a byte parser correct.

A future byte-parser verification layer may be added later, but it is not part of this plan.

## Expose Ambiguity Early

Stop and record ambiguity when the spec does not define:

- duplicate object key handling;
- unknown field policy;
- numeric representation;
- optional/default field behavior;
- enum spelling;
- coordinate-system conventions;
- units;
- exact array lengths;
- version compatibility;
- lens/camera key names.

## Do Not Start with Top-Level `Sample`

The `Sample` theorem will pull in the whole protocol. Build it only after local models and local decoder soundness theorems exist.
