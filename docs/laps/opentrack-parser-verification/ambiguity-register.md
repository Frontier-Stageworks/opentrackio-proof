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

**Status:** PARTIALLY RESOLVED (2026-05-17) — camera resolved; lens resolved (2026-05-17); sample still open.  
**Blocks:** Slice 9 — unblocked. Slice 10 — unblocked. Slice 11 — still open.

**Camera resolution:**  
All `static.camera` fields are optional for consumers. The OpenTrackIO docs
state all described fields should be considered optional by the Consumer.
Missing fields decode to `none`; there are no schema defaults.

When a nested object IS present, its internal fields are required:
- `captureFrameRate` (if present): `num`, `denom` required
- `activeSensorPhysicalDimensions` (if present): `height`, `width` required
- `activeSensorResolution` (if present): `height`, `width` required
- `anamorphicSqueeze` (if present): `num`, `denom` required

**Lean impact — Camera:**  
All top-level camera fields are `Option _`. No `ValidCamera` predicate is
needed beyond what the field types themselves carry. Missing fields produce
`none`, not an error and not a default value.

**Lens resolution (2026-05-17):**  
`static.lens` and `lens` are optional for consumers. All immediate child
fields inside both are optional. Missing optional fields decode to `none`,
with one exception: `distortion.model` missing decodes to the string default
`"Brown-Conrady D-U"` (not `none`).

When a nested object IS present, its internal required-field constraints apply:
- `distortion[i]` (if present): `radial` required and nonempty
- `distortionOffset` (if present): `x`, `y` required
- `projectionOffset` (if present): `x`, `y` required
- `encoders` (if present): at least one of `focus`, `iris`, `zoom` required
- `rawEncoders` (if present): at least one of `focus`, `iris`, `zoom` required
- `exposureFalloff` (if present): `a1` required; `a2`, `a3` optional

**Lean impact — Lens:**  
All top-level `static.lens` and `lens` fields are `Option _`. The
`distortion.model` default is handled at decode time (absent → `"Brown-Conrady D-U"`).
The `anyOf` constraint for `encoders`/`rawEncoders` is carried by `FizOptions`
(an invariant-carrying type with `anyPresent` proof field). No `ValidLens`
predicate is needed beyond what the field types carry.

**Still unresolved:** sample-level field optionality.

---

## A5 — Enum spelling and canonicalization

**Status:** RESOLVED (2026-05-17) — with important corrections to scope.  
**Blocks:** Slice 7 — unblocked (scope corrected; see below).

**Resolution:**  
The schema has exactly four enum fields. All use exact string match; no case
folding is specified. Unknown values are rejected.

```
timing.mode:
  "internal"
  "external"

timing.synchronization.source:
  "genlock"
  "videoIn"
  "ptp"
  "ntp"

timing.synchronization.ptp.profile:
  "IEEE Std 1588-2019"
  "IEEE Std 802.1AS-2020"
  "SMPTE ST2059-2:2021"

timing.synchronization.ptp.leaderTimeSource:
  "GNSS"
  "Atomic clock"
  "NTP"
```

**Scope corrections (fields that are NOT enums):**
- Coordinate system: no JSON enum field. Fixed by protocol text (right-handed,
  Z up, Y forward). Not decoded from JSON.
- Projection type: no JSON enum field. Protocol uses `lens.pinholeFocalLength`
  and `projectionOffset` fields, not a projection-type enum.
- `distortion.model`: not a closed enum. It is an optional string
  (`minLength: 1`, `maxLength: 1023`). Typical values are `"Brown-Conrady D-U"`
  and `"Brown-Conrady U-D"`, but these are not the only legal values. Default
  when omitted: `"Brown-Conrady D-U"`. Must be decoded as a plain string.

**Lean impact — Slice 7 rescoped:**  
`decodeTimingMode`, `decodeSyncSource`, `decodePtpProfile`, and
`decodePtpLeaderTimeSource` are the four enum decoders. Each pattern-matches
on exact strings. `distortion.model` is decoded as `Option String` in a later
slice, not here.

---

## A6 — Lens coefficient array lengths

**Status:** RESOLVED (2026-05-17)  
**Blocks:** Slice 6 — unblocked (but slice is renamed; see below). Slice 10 — partially unblocked.

**Resolution:**  
There is no fixed length in the OpenTrackIO JSON schema. Schema constraints:

```
lens.distortion[*]:
  radial     : required, array of numbers, minItems = 1, no maxItems
  tangential : optional, array of numbers, minItems = 1 if present, no maxItems
  overscan   : optional number, minimum = 1.0
  model      : optional string
```

The distortion list itself has `minItems: 1`. Inside each distortion object,
only `radial` is required. `tangential` is optional.

**Lean impact — Slice 6 renamed:**  
Slice 6 is reframed from "fixed-length array decoder" to "nonempty numeric-array
decoder". The normative Lean model is:

```lean
structure NonemptyArray (α : Type) where
  values  : List α
  nonempty : values ≠ []

structure Distortion where
  radial     : NonemptyArray RealValue
  tangential : Option (NonemptyArray RealValue)
```

**Not encoded:** The OpenLensIO rendering convention (6 radial + 2 tangential
coefficients, alternating numerator/denominator) is a semantic layer above the
schema. A future OpenLensIO-specific slice may add a `decodeOpenLensDistortion`
that enforces exact lengths, but that is out of scope for Slices 6 and 10.

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

**Status:** PARTIALLY RESOLVED — protocol resolved (2026-05-17); camera resolved (2026-05-17); lens resolved (2026-05-17); timing, globalStage, tracker still open.  
**Blocks:** Slice 4C — unblocked. Slice 9 — unblocked. Slice 10 — unblocked. Slices 11, 12 — still blocked on remaining fields.

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

**Resolved: static.camera field tree (2026-05-17)**

Normative keys under `static.camera` (`additionalProperties: false`):

```
captureFrameRate                  : rational { num, denom }; optional
activeSensorPhysicalDimensions    : object; optional
  height                          : JSON number, minimum 0.0; required if parent present
  width                           : JSON number, minimum 0.0; required if parent present
activeSensorResolution            : object; optional
  height                          : integer, min 0, max 2147483647; required if parent present
  width                           : integer, min 0, max 2147483647; required if parent present
make                              : string; optional
model                             : string; optional
serialNumber                      : string; optional
firmwareVersion                   : string; optional
label                             : string; optional
anamorphicSqueeze                 : rational { num, denom }; optional
isoSpeed                          : integer; optional (bounded wrapper deferred)
fdlLink                           : string; optional (regex proof deferred)
shutterAngle                      : number; optional (bounded real wrapper deferred)
```

Rational fields (`captureFrameRate`, `anamorphicSqueeze`) use the
`{ "num": ..., "denom": ... }` shape from A1 (not "den").

**Lean model for Camera (Slice 9):**

```lean
structure SensorPhysicalDimensions where
  height : String   -- raw JSON number string, minimum 0.0
  width  : String

structure SensorResolution where
  height : Nat      -- integer [0, 2147483647]
  width  : Nat

structure Camera where
  captureFrameRate               : Option PositiveRational
  activeSensorPhysicalDimensions : Option SensorPhysicalDimensions
  activeSensorResolution         : Option SensorResolution
  make                           : Option NonemptyString
  model                          : Option NonemptyString
  serialNumber                   : Option NonemptyString
  firmwareVersion                : Option NonemptyString
  label                          : Option NonemptyString
  anamorphicSqueeze              : Option PositiveRational
  isoSpeed                       : Option String
  fdlLink                        : Option String
  shutterAngle                   : Option String
```

**Resolved: static.lens field tree (2026-05-17)**

Normative keys under `static.lens`; all optional:

```
distortionOverscanMax     : JSON number, minimum 1.0; optional (bound deferred)
undistortionOverscanMax   : JSON number, minimum 1.0; optional (bound deferred)
make                      : string; optional
model                     : string; optional
serialNumber              : string; optional
firmwareVersion           : string; optional
nominalFocalLength        : plain JSON number (not rational); optional
calibrationHistory        : array of nonempty strings; optional; empty array allowed
```

**Lean model for StaticLens (Slice 10):**

```lean
structure StaticLens where
  distortionOverscanMax   : Option String   -- raw JSON number; bound deferred
  undistortionOverscanMax : Option String   -- raw JSON number; bound deferred
  make                    : Option NonemptyString
  model                   : Option NonemptyString
  serialNumber            : Option NonemptyString
  firmwareVersion         : Option NonemptyString
  nominalFocalLength      : Option String   -- raw JSON number; bound deferred
  calibrationHistory      : Option (List NonemptyString)
```

**Resolved: dynamic lens field tree (2026-05-17)**

Normative keys under `lens`; all optional for consumers. Present nested
objects must satisfy their own required-field constraints.

```
custom              : array of JSON numbers; optional; empty array allowed
distortion          : nonempty array of distortion objects; optional
  radial            : nonempty array of JSON numbers; required if distortion object present
  tangential        : nonempty array of JSON numbers; optional
  overscan          : JSON number, minimum 1.0; optional (bound deferred)
  model             : string; optional; default "Brown-Conrady D-U" when absent
distortionOffset    : object; optional
  x                 : JSON number; required if parent present
  y                 : JSON number; required if parent present
encoders            : object; optional; at least one of focus/iris/zoom required
  focus             : JSON number [0.0, 1.0]; optional (bound deferred)
  iris              : JSON number [0.0, 1.0]; optional (bound deferred)
  zoom              : JSON number [0.0, 1.0]; optional (bound deferred)
entrancePupilOffset : plain JSON number; optional
exposureFalloff     : object; optional
  a1                : JSON number; required if parent present
  a2                : JSON number; optional
  a3                : JSON number; optional
fStop               : plain JSON number, exclusiveMinimum 0.0; optional (bound deferred)
focusDistance       : plain JSON number; optional
pinholeFocalLength  : plain JSON number (not rational), exclusiveMinimum 0.0; optional
projectionOffset    : object; optional
  x                 : JSON number; required if parent present
  y                 : JSON number; required if parent present
rawEncoders         : object; optional; at least one of focus/iris/zoom required
  focus             : JSON integer [0, 4294967295]; optional (bound deferred)
  iris              : JSON integer [0, 4294967295]; optional (bound deferred)
  zoom              : JSON integer [0, 4294967295]; optional (bound deferred)
tStop               : plain JSON number, exclusiveMinimum 0.0; optional (bound deferred)
```

**Lean model for Lens (Slice 10):**

```lean
structure FizOptions where
  focus      : Option String
  iris       : Option String
  zoom       : Option String
  anyPresent : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none

structure DistortionOffset where
  x : String
  y : String

structure ProjectionOffset where
  x : String
  y : String

structure ExposureFalloff where
  a1 : String
  a2 : Option String
  a3 : Option String

structure Distortion where
  radial     : NonemptyArray String
  tangential : Option (NonemptyArray String)
  overscan   : Option String
  model      : String              -- default "Brown-Conrady D-U" when absent in JSON

structure Lens where
  custom              : Option (List String)
  distortion          : Option (NonemptyArray Distortion)
  distortionOffset    : Option DistortionOffset
  encoders            : Option FizOptions
  entrancePupilOffset : Option String
  exposureFalloff     : Option ExposureFalloff
  fStop               : Option String
  focusDistance       : Option String
  pinholeFocalLength  : Option String
  projectionOffset    : Option ProjectionOffset
  rawEncoders         : Option FizOptions
  tStop               : Option String
```

**Guardrail for Slice 10:**  
The soundness theorem must not overclaim numeric bounds, integer-vs-number
distinctions, or max string lengths that are not enforced by the current types.
`FizOptions.anyPresent` is the only structural invariant proved in this slice.

**Still unresolved: broader field tree**

```
timing.*               (sampleRate, sampleTimestamp, timecode, ...)
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

## A9 — Transform rotation representation

**Status:** RESOLVED (2026-05-17)  
**Blocks:** Slice 8 — unblocked.

**Resolution:**  
Transform rotation is **Euler pan/tilt/roll in degrees**, not quaternions.
There is no quaternion unit-norm requirement. `ValidTransform` must not
include any quaternion predicate.

**Transform structure (normative):**

```
translation   : required object
  .x          : required JSON number
  .y          : required JSON number
  .z          : required JSON number

rotation      : required object
  .pan        : required JSON number
  .tilt       : required JSON number
  .roll       : required JSON number

scale         : optional object
  .x          : required JSON number (when scale is present)
  .y          : required JSON number (when scale is present)
  .z          : required JSON number (when scale is present)

id            : optional string, nonempty, maxLength 1023
```

**Angle bounds:** Angles are NOT bounded to [0, 360). The prose explicitly
allows values > 360 and < 0. `ValidTransform` must not constrain pan, tilt,
or roll.

**Lean impact:**  
- `Vec3` (or inline triple): `x y z : String` (raw JSON number strings;
  semantic parsing of floats is deferred to a later slice).
- `Rotation`: `pan tilt roll : String`.
- `ValidTransform`: expresses structural invariants only (e.g., `id` is
  nonempty when present), not angle bounds.
- `transforms` field at the sample level: decoded as a `NonemptyArray Transform`
  (using Slice 6) when the key is present.

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
