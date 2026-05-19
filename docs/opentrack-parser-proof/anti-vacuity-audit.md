# Anti-Vacuity Audit — OpenTrackIO Parser Verification
# Slices 1–18

**Date:** 2026-05-19  
**Status:** Reference document; does not open new proof obligations

---

## 1. Purpose

Lean's kernel accepting a proof is necessary but not sufficient for that proof to be useful.
A theorem can typecheck while proving nothing meaningful — by carrying a `True` conclusion,
by having a validity predicate that is definitionally `True`, or by using a decoder that
always returns error and therefore has vacuously sound soundness theorems.

This audit answers the question:

> **How do we know these proofs are useful, and not merely trivially true or vacuous?**

For each major artifact, it classifies the proof strength, identifies where real invariants
are enforced, and honestly labels what is intentionally deferred or intentionally weak.

---

## 2. Classification scheme

| Class | Meaning |
|---|---|
| **Strong semantic** | Directly rules out a bad protocol state, or proves decoder/encoder agreement on a nontrivial claim |
| **Type-carried** | The theorem may look short, but the invariant is stored in the returned type; construction is the real proof obligation |
| **Executable witness** | A smoke test or harness showing that decoders have successful paths and are not vacuously sound because they always fail |
| **Infrastructure / shell** | Useful for model composition, but weak as semantic validation |
| **Deferred / out of scope** | Explicitly not proved; labeled as such |

---

## 3. Anti-vacuity questions

For each artifact, ask:

1. Does the theorem mention the real decoder or encoder?
2. Can the decoder actually succeed on representative inputs?
3. Does the output type prevent the bad state?
4. Is the predicate nontrivial, or is it `True`?
5. If the proof is short, is it short because the invariant is type-carried?
6. Are there executable examples showing successful decoder paths?
7. Are any assumptions/hypotheses doing real work?
8. Are deferred claims clearly labeled?

---

## 4. Artifact audit table

### Slice 1 — `RationalValueWrappers.lean`

**Artifacts:**
`PositiveRational`, `NonnegativeRational`, `RationalWithPositiveDenominator`;
theorems `rational_with_positive_denominator_den_nat_ne_zero`,
`nonnegative_rational_den_nat_ne_zero`, `positive_rational_den_nat_ne_zero`,
`rational_with_positive_denominator_den_ne_zero`, `nonnegative_rational_den_ne_zero`,
`positive_rational_den_ne_zero`, `positive_rational_num_ne_zero`,
`positive_rational_toReal_pos`, `nonnegative_rational_toReal_nonneg`.

| Question | Assessment |
|---|---|
| Output type prevents bad state? | Yes. `PositiveRational` carries `num_pos : 0 < num` and `den_pos : 0 < den` as struct fields; a zero numerator or denominator cannot be constructed |
| Predicate nontrivial? | Yes. `positive_rational_toReal_pos` proves `0 < (r.num : ℝ) / r.den`, which is false for zero numerator or zero denominator |
| Proof short because type-carried? | Yes; but this is the point — downstream proofs inherit the invariant without re-checking |
| Can bad state be constructed? | No. Lean's kernel enforces the proof fields at construction time |

**Classification:** Type-carried with strong semantic grounding. The `toReal_pos` theorem
connects the integer struct fields to real-number positivity, bridging the protocol claim
("sample rates and capture frame rates must be positive") to the formal model.

**What it actually proves:** A `PositiveRational` value cannot represent `0/1`, `1/0`, `0/0`,
or any negative rational. The theorems confirm the real-valued interpretation is positive.

**Deferred:** Float/decimal precision bounds; specific rational ranges (e.g., frame rates
between 1 and 240); rational arithmetic correctness.

---

### Slice 2 — `JsonRawModel.lean`

**Artifacts:** `JsonValue` algebraic type; `lookup?` utility.

**Classification:** Infrastructure. The model is necessary but itself proves nothing.
The `lookup?` semantics is used in all downstream proofs — correctness of `lookup?`
is inherited from the Lean standard library, not proved separately here.

**What it actually proves:** The model compiles and the utility function elaborates.

**Deferred:** Byte-level JSON parsing; duplicate-key semantics are modeled but the
policy (first-key-wins) is not separately theorem-proved.

---

### Slice 3 — `DecodeError.lean`

**Artifacts:** `DecodeError` inductive type.

**Classification:** Infrastructure. Defines the error vocabulary used in all decoder
return types; no theorems.

---

### Slices 4A–4C — `ProtocolVersion.lean`, `VersionDecoder.lean`, `ProtocolDecoder.lean`

**Artifacts:**
`VersionDigit := Fin 10`, `ProtocolVersion`, `ValidVersion`,
`protocolVersion_valid`, `decodeVersionDigit`, `decodeVersionValue`,
`decodeVersionValue_sound`, `decodeProtocol`, `decodeProtocol_sound`.

| Question | Assessment |
|---|---|
| Output type prevents bad state? | Yes. `VersionDigit := Fin 10` makes it impossible to construct a digit value ≥ 10 |
| `ValidVersion` predicate nontrivial? | **Conditionally.** `ValidVersion v := v.major.val ≤ 9 ∧ v.minor.val ≤ 9 ∧ v.patch.val ≤ 9`. For `Fin 10`, this is always true and `protocolVersion_valid` proves it trivially by `omega`. If the type had been `Nat` instead of `Fin 10`, a proof of `ValidVersion v` could have been false for `v.major = 255` |
| Decoder hypothesis used? | The `_h` prefix in `decodeVersionValue_sound` and `decodeProtocol_sound` indicates the hypothesis is unused; the conclusion follows from the type alone |
| Would `ValidVersion := True` have been vacuous? | Yes — this was the precise risk. The project avoided it by using `Fin 10` |

**Classification:** Type-carried; meaningful because `Fin 10` is a genuine bound.

**What it actually proves:** Any `ProtocolVersion` decoded by `decodeVersionDigit` has
each component in `[0, 9]` by type construction, not by a separate theorem. The soundness
theorems confirm the type invariant holds after decoding, but their value is that the
decoder uses `decodeVersionDigit` — which produces `Fin 10`, not `Nat` — for each field.

**Known short-proof pattern:** `_h` is unused in these soundness theorems because the
invariant is entirely in the return type. This is acceptable and expected.

**Deferred:** Semantic version compatibility (that `1.0.1` is backward-compatible with
`1.0.0`); allowed version ranges.

---

### Slice 5 — `RationalDecoder.lean`

**Artifacts:** `decodePositiveRational`, `decodePositiveRational_sound`.

| Question | Assessment |
|---|---|
| Decoder mentions real decoder? | Yes: `decodePositiveRational_sound` mentions `decodePositiveRational` in its hypothesis |
| Decoder can succeed? | Yes: confirmed by `#eval` in `IntegrationSmoke.lean` (see Slice 11.5) |
| Proof checks? | The decoder guards `0 < n` and `0 < d` with `if hn :` / `if hd :` decision proofs, which become the `num_pos` and `den_pos` struct fields |
| `_h` used? | No: `decodePositiveRational_sound` concludes `0 < r.toReal` using `positive_rational_toReal_pos r`, which works on any `PositiveRational`. The decoder hypothesis is unused because the invariant is type-carried |

**Classification:** Strong. The value is not in the soundness theorem itself but in
the decoder: it is the only place where the decision proofs `hn : 0 < n` and `hd : 0 < d`
are constructed. A decoder that accepted any `{"num": 0, "denom": 1}` would fail to
build the `PositiveRational` struct at all — the Lean kernel would reject it.

**What it actually proves:** A `PositiveRational` can only be decoded from a JSON object
where both fields parse as positive natural numbers. Zero or negative values cannot pass
through the decoder.

**Deferred:** Numeric bounds beyond positivity; rational arithmetic precision;
overflow behavior for very large numerators.

---

### Slice 6 — `NonemptyArrayDecoder.lean`

**Artifacts:** `NonemptyArray`, `decodeNonemptyArray`, `decodeNonemptyArray_sound`.

| Question | Assessment |
|---|---|
| Output type prevents empty array? | Yes. `NonemptyArray` carries `nonempty : values ≠ []` |
| Decoder can succeed? | Yes: the decoder takes the successful (non-nil) branch only when the array has at least one element |
| Soundness conclusion? | `decodeNonemptyArray_sound` concludes `na.values ≠ []`, which is `na.nonempty` |

**Classification:** Type-carried with strong semantic grounding. Used downstream in
`Distortion.radial` (distortion coefficient arrays must be nonempty) and `transforms`
(at least one transform required).

---

### Slice 7 — `TimingEnumDecoders.lean`

**Artifacts:** `TimingMode`, `SyncSource`, `PtpProfile`, `PtpLeaderSource`;
decoders `decodeTimingMode`, `decodeSyncSource`, `decodePtpProfile`, `decodePtpLeaderSource`;
soundness theorems `decodeTimingMode_sound`, `decodeSyncSource_sound`,
`decodePtpProfile_sound`, `decodePtpLeaderSource_sound`.

| Question | Assessment |
|---|---|
| Closed-world decoding? | Yes. Each decoder matches exact string literals and rejects anything unknown |
| Predicate nontrivial? | Yes. The soundness theorems prove `m.toStr = s` — that decoding string `s` as enum value `m` implies `m.toStr` roundtrips back to the same string |
| Does this prevent anything? | Yes: strings outside the enum set cannot decode; an implementation reading an unknown mode string will get an error |

**Classification:** Strong closed-world decoding. These are among the most precise semantic
guarantees in the project: only the exact strings specified by the OpenTrackIO v1.0.1 schema
are accepted.

**What it actually proves:** `decodeTimingMode` accepts exactly `"internal"` and `"external"`;
`decodeSyncSource` accepts exactly `"genlock"`, `"videoIn"`, `"ptp"`, `"ntp"`;
`decodePtpProfile` and `decodePtpLeaderSource` accept their respective enum strings.
Any other string returns an error.

---

### Slices 8A–8B — `TransformModel.lean`, `TransformDecoder.lean`

**Artifacts:** `NonemptyString`, `Transform`, `decodeIdField`, `decodeTransform`,
`decodeTransform_sound`.

| Question | Assessment |
|---|---|
| `NonemptyString` prevents bad state? | Yes. Carries `nonempty : val ≠ ""` at construction time |
| `decodeIdField` gatekeeps? | Yes: `if h : s ≠ ""` is the guard; the `NonemptyString` is constructed only in the true branch |
| `decodeTransform_sound` uses decoder hypothesis? | No (`_h`). The conclusion `ns.nonempty` follows from the type |
| Quaternion? | Not applicable — OpenTrackIO uses Euler pan/tilt/roll, not quaternions. No quaternion normalization is proved or needed |

**Classification:** Type-carried; meaningful because `decodeIdField` enforces nonemptiness
at the boundary, not in a separate theorem.

**What it actually proves:** A decoded `Transform.id`, if present, is guaranteed to be a
nonempty string. An empty string `""` as the transform id causes decode failure.

---

### Slice 9 — `CameraModel.lean`, `CameraDecoder.lean`

**Artifacts:** `SensorResolution`, `SensorPhysicalDimensions`, `Camera`,
`decodeSensorResolution`, `decodeSensorPhysicalDimensions`, `decodeCamera`,
`decodeCamera_sound`.

| Question | Assessment |
|---|---|
| `decodeCamera_sound` conclusion? | `fun r _ => positive_rational_toReal_pos r` — confirms `captureFrameRate`, if present, is a positive rational |
| Sensor resolution? | `SensorResolution.height` and `.width` are `Nat`, so nonnegativity is type-guaranteed; the decoder checks they parse as natural numbers |
| Decoder hypothesis used? | No (`_h`) — type invariants carry the claim |

**Classification:** Partial semantic proof. Strong for `PositiveRational` and `NonemptyString`
fields. The sensor dimension `Nat` type guarantees non-negativity but not upper-bound limits
(pixel dimensions could be 2^63 in the model).

**Deferred:** Pixel count bounds; physical dimension ranges; make/model string length limits;
regex patterns (e.g., `fdlLink` as a URN).

---

### Slice 10 — `LensModel.lean`, `LensDecoder.lean`

**Artifacts:** `FizOptions`, `Distortion`, `StaticLens`, `Lens`,
`decodeFizOptions`, `decodeDistortion`, `decodeLens`, `decodeLens_sound`.

| Question | Assessment |
|---|---|
| `FizOptions.anyPresent` is real? | Yes. `anyPresent : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none` is a real disjunctive constraint; a `FizOptions` with all three absent cannot be constructed |
| `Distortion.radial` nonempty? | Yes — it is `NonemptyArray String`, with the type carrying the nonemptiness |
| `decodeLens_sound` conclusion? | `fun fiz _ => fiz.anyPresent` — confirms that decoded `encoders`/`rawEncoders`, if present, satisfy the at-least-one-present invariant |
| `pinholeFocalLength` vs `focalLength`? | `decodeLens` reads the `"pinholeFocalLength"` key. There is no `"focalLength"` in the decoder. The Lean model has `Lens.pinholeFocalLength : Option String` — wrong-key access is structurally impossible |

**Classification:** Strong for structural presence invariants. The `FizOptions.anyPresent`
claim is the most precise field-presence constraint in the project.

**What it actually proves:** A decoded `FizOptions` cannot have focus, iris, and zoom all
absent — the schema's `anyOf` requirement is enforced in the type. The correct focal length
key (`pinholeFocalLength`) is the only key the decoder reads.

**Deferred:** Numeric bounds on encoder values; distortion coefficient count bounds;
overscan range; `tStop`/`fStop` positivity.

---

### Slice 11 — `SampleModel.lean`

**Artifacts:** `Timestamp`, `SyncOffsets`, `LeaderPriorities`, `PtpInfo`,
`Synchronization`, `Timecode`, `Timing`, `StaticTracker`, `StaticInfo`, `Tracker`,
`GlobalStage`, `Sample`.

**Classification:** Infrastructure / shell. The model composes all sub-models into the
full `Sample` struct and fixes all field names and types. This is necessary for any
downstream proof, but is not itself a semantic guarantee. No `ValidSample` predicate
exists that could be `True` — there is no such predicate.

**What it actually proves:** The `Sample` struct type compiles with correct field names,
`«static»` guillemet escaping, and correct types (e.g., `Option Bool` for `recording`,
not `Option String`).

---

### Slice 11.5 — `IntegrationSmoke.lean`

**Artifacts:** Five `#eval` expressions; `smokeSample : Sample`.

| Question | Assessment |
|---|---|
| Shows decoder success paths? | Yes — this is the sole purpose |
| Prevents always-failing decoder vacuity? | Yes — a decoder that always returns `.error` would have all five `#eval` lines evaluate to `false` |

```lean
#eval decodeProtocol (...).isOk               -- true
#eval decodePositiveRational (...).isOk        -- true
#eval decodeTransform (...).isOk               -- true
#eval decodeCamera (...).isOk                  -- true
#eval decodeLens (...).isOk                    -- true
def smokeSample : Sample := ...               -- elaborates
```

**Classification:** Executable witness. Not a theorem, but essential for ruling out the
failure mode where soundness theorems hold vacuously because the decoder never accepts input.

**What it actually proves:** Each of the five decoders has at least one valid input path.
The `smokeSample` construction confirms that decoder outputs compose into a valid `Sample`
without elaboration error.

---

### Slices 12A–12B — `SampleDecoder.lean` (composed soundness theorems)

**Artifacts:** `decodeSample`, `decodeSample_transforms_sound`,
`decodeSample_protocol_sound`, `decodeSample_lens_encoders_sound`,
`decodeSample_static_duration_sound`, `decodeSample_static_camera_sound`.

The five theorems:

```lean
theorem decodeSample_transforms_sound   ... : ts.values ≠ []
theorem decodeSample_protocol_sound     ... : ValidVersion p.version
theorem decodeSample_lens_encoders_sound... : fiz.focus ≠ none ∨ fiz.iris ≠ none ∨ fiz.zoom ≠ none
theorem decodeSample_static_duration_sound : 0 < r.toReal
theorem decodeSample_static_camera_sound   : 0 < r.toReal
```

| Question | Assessment |
|---|---|
| Decoder hypothesis `_h` used? | No — all five theorems mark the decoder hypothesis with `_`. The conclusions follow from the respective struct fields |
| Is this acceptable? | Yes — the decoder hypothesis is unused because the invariants are type-carried; constructing the value through the decoder is the enforcement point |
| Do theorems mention `decodeSample`? | Yes — all five take `decodeSample j = .ok s` as a hypothesis. The theorems lift component invariants to the full-sample level |

**Classification:** Type-carried composed soundness. The proofs are short because all the
real work happens in the sub-decoders. These theorems confirm that top-level decoding
preserves the component invariants — they do not add new claims.

**What it actually proves:** Any `Sample` decoded from valid JSON retains: nonempty
transform arrays, valid protocol version digits, lens encoder presence invariants, and
positive rational frame rates.

**Limitation:** The theorems cover only the specific sub-components listed. They do not
prove end-to-end completeness, that all fields are accessible, or that no silent field loss
occurs during decoding.

---

### Slice 13 — `ErrorCorrectness.lean`

**Artifacts:** `decodeProtocol_missing_name`, `decodeProtocol_missing_version`,
`decodeTransform_missing_translation`, `decodeTransform_missing_rotation`,
`decodePositiveRational_missing_num`.

| Question | Assessment |
|---|---|
| Theorems mention real decoders? | Yes — all five name `decodeProtocol`, `decodeTransform`, or `decodePositiveRational` directly |
| Prove rejection behavior? | Yes — each proves a specific missing-field input produces a specific `.error (.missingField "fieldname")` |
| Could a decoder that always fails satisfy these? | Yes — but it would fail Slice 11.5's executable witnesses |

**Classification:** Strong in the error direction. These are the project's explicit
rejection guarantees. They prove that decoders do not silently swallow missing required
fields — a specific error tag is returned.

**What it actually proves:** Missing `"name"` in the protocol object → `missingField "name"` error;
missing `"version"` when `"name"` is present → `missingField "version"` error;
missing `"translation"` in a transform → `missingField "translation"` error;
missing `"rotation"` when `"translation"` is present → `missingField "rotation"` error;
missing `"num"` in a rational object → `missingField "num"` error.

**Limitation:** Only five specific missing-field cases are covered. Missing field errors
for camera, lens, timing, and sample sub-fields are not separately proved (they are
present in the decoders but not theorem-covered).

---

### Slices 14–15 — Encoder and encode/decode roundtrip

**Artifacts across multiple files:** `encodePositiveRational`, `encodeTimecode`,
`encodeSynchronization`, `encodeTiming`, `encodeCamera`, `encodeLens`, `encodeStaticInfo`,
`encodeSample`; roundtrip theorem `encodeSample_roundtrip`.

The top-level roundtrip theorem:

```lean
theorem encodeSample_roundtrip (s : Sample) :
    decodeSample (encodeSample s) = .ok s
```

| Question | Assessment |
|---|---|
| Mentions real encoder and decoder? | Yes — both `encodeSample` and `decodeSample` appear directly |
| Can this be faked by a trivial encoder? | No. A trivial encoder (e.g., always returning `.object []`) would produce a Sample where all fields are absent, not `= .ok s` for a sample with populated fields |
| Can this be faked by a trivial decoder? | No. A trivial decoder (e.g., always returning `.ok defaultSample`) would fail for any `s` that differs from `defaultSample` |
| What does the proof case-split on? | Every optional field in `Sample` — 11 fields × 2 branches = 2048 goal branches |
| Numeric bridge? | `nat_repr_toNat?_some (n : Nat) : n.repr.toNat? = some n` — proved by strong induction; required because encoded `Nat` fields must parse back through `String.toNat?` |

**Classification:** Strongest semantic artifacts in the project.
`encodeSample_roundtrip` is the closest thing to an end-to-end correctness guarantee:
for any `Sample` value constructible by the model, encoding it and decoding the result
recovers the original value. This rules out encoder field-name bugs, missing-field bugs,
and key-spelling bugs.

**What it actually proves:** `encodeSample` is a right inverse of `decodeSample` on
the image of `encodeSample`. Equivalently: every `Sample` value has a JSON representation
that the decoder accepts and roundtrips correctly.

**Strongest sub-claim:** `nat_repr_toNat?_some` is a nontrivial standalone obligation.
It proves that Lean's decimal number renderer and `String.toNat?` are inverse for all
natural numbers. This was not trivial: it required strong induction and character-level
digit manipulation. The roundtrip theorem depends on this bridge because encoded rational
numerators and denominators are stored as decimal strings.

**Deferred:** The roundtrip only covers `encodeSample` → `decodeSample`. It does not
prove that every JSON document that `decodeSample` accepts roundtrips back (i.e.,
`encodeSample (decodeSample j).get! = j` for well-formed `j`) — this is the
normalization direction, covered separately in Slice 16.

---

### Slice 16A — `WellFormedSampleJson.lean`

**Artifacts:** `WellFormedSampleJson : JsonValue → Prop`.

```lean
def WellFormedSampleJson (j : JsonValue) : Prop :=
  j.NoDupKeys ∧
  (∀ vj, j.lookup? "globalStage" = some vj → WellFormedGlobalStage vj) ∧
  (∀ vj, j.lookup? "lens"        = some vj → WellFormedLens vj) ∧
  ...
```

| Question | Assessment |
|---|---|
| Predicate nontrivial? | Yes — `NoDupKeys` is recursive over the whole JSON tree; each `WellFormed*` predicate checks key membership and required-field presence |
| Could this be `True`? | It would be if `NoDupKeys` were omitted and `WellFormedLens := True`; it is not |
| What does it rule out? | Duplicate keys anywhere in the tree; unknown fields inside schema-defined nested objects (`lens`, `timing.synchronization`, etc.); missing required sub-fields when the parent is present |
| Unknown top-level fields? | Allowed — per A3 policy, `Sample` is extension-tolerant. No `allKeysIn` on the top-level object |

**Classification:** Meaningful predicate; strength depends on which nested objects are
checked. The predicate is genuinely nontrivial for `WellFormedLens`, `WellFormedTiming`,
and `WellFormedSynchronization`, which impose field-membership constraints on nested objects.

**Limitation:** `WellFormedSampleJson` is not proved to hold for any specific fixture.
It is a hypothesis in the normalization theorems, not a conclusion. Whether a given
real-world JSON sample satisfies it is not verified by Lean.

---

### Slice 16B — `NormalizationTheorems.lean`

**Artifacts:** `sampleNormalize`, `sampleNormalize_idempotent`, `encodedSample_stable`,
`sampleNormalize_encodeSample`, `wellFormed_normalize_eq_encode`,
`normalization_under_wellFormed`.

Key theorems:

```lean
theorem sampleNormalize_idempotent (j : JsonValue) :
    sampleNormalize (sampleNormalize j) = sampleNormalize j

theorem normalization_under_wellFormed (j : JsonValue) (s : Sample)
    (_ : WellFormedSampleJson j) (hd : decodeSample j = .ok s) :
    decodeSample (sampleNormalize j) = .ok s
```

| Question | Assessment |
|---|---|
| `sampleNormalize_idempotent` real? | Yes — it follows from `encodeSample_roundtrip` via `cases h : decodeSample j`. On the `.ok s` branch: `sampleNormalize (encodeSample s) = encodeSample s` uses the roundtrip; on `.error`: normalization is the identity |
| `normalization_under_wellFormed` hypothesis doing real work? | Yes — `WellFormedSampleJson j` and `hd : decodeSample j = .ok s` are both used (via `hd`) |
| Without `WellFormedSampleJson`, would the theorem overclaim? | The `WellFormedSampleJson` hypothesis is structurally required but actually unused in the proof body (the conclusion follows from `hd` and `encodeSample_roundtrip`). It is present to mark the domain of intended application. Technically `normalization_under_wellFormed` would hold without it — it follows from `hd` alone. This is a slight overclaim on the hypothesis's necessity, but not a vacuity problem |
| `WellFormedSampleJson (encodeSample s)` proved? | **No — intentionally out of scope.** The private predicates in `WellFormedSampleJson.lean` cannot be accessed from `NormalizationTheorems.lean`. This gap means the "image of `encodeSample` is well-formed" claim is not proved |

**Classification:** Meaningful under stated conditions. `sampleNormalize_idempotent` is the
strongest theorem — it derives nontrivially from `encodeSample_roundtrip`. The
`normalization_under_wellFormed` cluster would be strengthened if `WellFormedSampleJson
(encodeSample s)` were proved (showing encoder output is always well-formed), but that
obligation was deferred due to the private-predicate access boundary.

**What it actually proves:** Normalization is idempotent. Normalized samples roundtrip
through the decoder. Encoding a sample and then normalizing it is a no-op.

---

### Slice 17 — `HarnessMain.lean` (executable harness)

**Classification:** Packaging / executable witness.

All 10 checks pass under `lake env lean --run`, confirming that the verified components
are runnable and produce correct outputs on representative inputs. This is a stronger
executable witness than Slice 11.5 because it exercises the full `Sample` decoder,
encoder, and normalizer end-to-end.

**Not a proof.** The harness does not add new theorems. It confirms the proof machinery
is executable and produces the expected results on fixed inputs.

---

### Slice 18 — `HarnessAdapter.lean` (battery-tester integration)

**Classification:** Executable witness + differential oracle.

The Lean adapter runs as a third column in the `battery-tester` differential harness.
The key semantic observation: Lean reads `lens.pinholeFocalLength` because the verified
decoder hardcodes that key. It cannot read `lens.focalLength` — there is no code path
for that.

**Not a proof.** The adapter demonstrates that the verified decoder's key choices differ
from a buggy Python implementation. The "proof" value is indirect: the roundtrip theorem
`encodeSample_roundtrip` would fail if the decoder used the wrong key, because encoding
writes `pinholeFocalLength` and decoding would then miss it.

---

## 5. Known deferred limitations

The following properties are **not proved** by this project. Each is labeled clearly
in the relevant slice capsules.

| Limitation | Status |
|---|---|
| Byte-level JSON parsing | Not verified. Python's `json.load` converts fixture bytes before the Lean model sees them |
| Duplicate-key rejection | Modeled by `NoDupKeys` in `WellFormedSampleJson`, but no theorem proves that `decodeSample` itself enforces or rejects duplicates — `lookup?` takes the first match |
| Unknown top-level fields | Allowed per A3. Unknown nested fields require `WellFormedSampleJson` |
| Numeric bounds beyond positivity | `PositiveRational` enforces `0 < num` and `0 < den`; upper bounds (e.g., frame rate ≤ 240) are deferred |
| Regex/pattern constraints | UUID URNs, MAC-like PTP leader identities, firmware version strings — stored as raw `String`, patterns not checked |
| Max string lengths | Not proved |
| `WellFormedSampleJson (encodeSample s)` | Not proved. The private access boundary between Slice 16A and 16B prevents this |
| Lens distortion mathematical correctness | The distortion conversion proofs are in `opencv_opentrackio_proofs/`, a separate module. The parser slices prove decoding/encoding, not coefficient semantics |
| Coordinate transform semantics | Pan/tilt/roll Euler correctness not proved; angle range not bounded |
| Full differential testing | Slice 18 exercises one fixture interactively; automated regression across all fixtures requires external CI |
| `decodeSample j` → `encodeSample (decodeSample j).get! = j` for all well-formed `j` | Only the `encodeSample` → `decodeSample` direction is proved (roundtrip). The inverse direction (decode then re-encode) is covered by `sampleNormalize_idempotent` but only after a first normalize |

---

## 6. Strongest evidence summary

The useful proof value in this project comes from five sources, in decreasing strength:

**1. Encode/decode roundtrip (`encodeSample_roundtrip`).**
The strongest single artifact. Rules out encoder field-name bugs, missing-field bugs,
and key-spelling bugs end-to-end. Requires the numeric literal roundtrip bridge
(`nat_repr_toNat?_some`) as a nontrivial subgoal.

**2. Error-correctness theorems (`ErrorCorrectness.lean`).**
Five theorems proving specific missing-field inputs produce specific error tags.
Rules out decoders that silently swallow missing required fields.

**3. Type-carried invariants at construction.**
`PositiveRational`, `NonemptyString`, `FizOptions.anyPresent`, `NonemptyArray`,
`Fin 10`/`VersionDigit`. Invalid states cannot be constructed — the Lean kernel enforces
the proof fields. Short downstream soundness theorems are short because the invariant is
already established.

**4. Closed-world enum decoders (Slice 7).**
Only the exact schema-specified strings are accepted. Unknown mode/source/profile strings
cause decode failure. The decoder and its `toStr` roundtrip theorems prove this precisely.

**5. Executable witnesses (Slices 11.5, 17, 18).**
`#eval` expressions and harness runs confirm decoders have successful paths and are not
vacuously sound due to universal failure.

---

## 7. Red flags checklist

Use this checklist when reviewing future slices or auditing existing ones.

- [ ] Does any theorem conclude `True`?
- [ ] Is any validity predicate definitionally equal to `True`?
- [ ] Does any decoder return `.error` on all inputs? (Ruled out by executable witnesses)
- [ ] Does any theorem fail to mention the real decoder or encoder?
- [ ] Is any `_h`-prefixed hypothesis doing no work where the type does **not** carry the claimed invariant? (Unused hypotheses are acceptable when type-carried; they are a red flag otherwise)
- [ ] Does any roundtrip theorem omit `decode (encode x)` from its statement?
- [ ] Does any normalization theorem ignore the unknown-field policy?
- [ ] Is `sorry`, `admit`, `axiom`, `unsafe`, or `partial` present anywhere in the verified module files?
- [ ] Is any deferred property presented as proved?

Current status: all red flags are **absent** in Slices 1–18 as delivered.

---

## 8. Conclusion

This project is not uniformly strong. The classification breaks down as:

| Class | Examples |
|---|---|
| **Strong semantic** | `encodeSample_roundtrip`, error-correctness theorems, closed enum decoders |
| **Type-carried** | `PositiveRational`, `NonemptyString`, `FizOptions.anyPresent`, `NonemptyArray`, `Fin 10` |
| **Executable witness** | Integration smoke (`#eval` × 5), harness checks (×10), battery-tester Lean adapter |
| **Infrastructure / shell** | `SampleModel.lean`, `DecodeError.lean`, `JsonRawModel.lean` |
| **Deferred** | Byte-level parsing, numeric bounds, regex constraints, `WellFormedSampleJson (encodeSample s)` |

The project should not be described as "a verified JSON parser." It is more precisely:

> A verified model of the OpenTrackIO Sample data model, with proved decoder/encoder
> soundness for structural invariants (positivity, nonemptiness, enum membership, id
> nonemptiness), proved error rejection for required-field absence, proved encode/decode
> roundtrip for all sample fields, proved normalization idempotency, and executable harness
> evidence that the verified components are runnable and produce expected outputs.
> Byte-level JSON parsing, numeric bounds, regex constraints, and some cross-module
> invariants are explicitly deferred.

This characterization is honest and useful. The roundtrip theorem is hard to fake. The
error-correctness theorems are hard to fake. The type-carried invariants prevent the most
common class of silent decoder bugs. The audit's purpose is to prevent future contributors
from presenting infrastructure checks as semantic verification — the distinction is
documented here, not papered over.
