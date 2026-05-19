# Slice 16A — Proof Capsule
# wellformed-predicate

**Status:** Capsule (Stop 1)
**Date:** 2026-05-19

---

## Goal

Define `WellFormedSampleJson : JsonValue → Prop` — a predicate characterizing the subset of
JSON inputs that are schema-clean for normalization purposes. The predicate implements the
A3 policy exactly:

- Duplicate keys rejected globally (recursive tree check)
- Unknown top-level custom fields allowed (no `allKeysIn` on Sample itself)
- Unknown fields inside schema-defined nested objects rejected
- Nested required fields asserted present when parent object is present
- Optional fields may be absent
- No regex/numeric-bound claims beyond what current wrappers enforce

This slice defines predicates only. No theorems. Theorems are Slice 16B.

---

## Output

| Item | Value |
|---|---|
| File | `opentrackio_parser/WellFormedSampleJson.lean` |
| Lake lib | `WellFormedSampleJson` |
| Imports | `SampleDecoder` (transitively imports all decoders and models) |
| Public surface | `WellFormedSampleJson` only; all helpers `private` |

---

## Infrastructure predicates

### `JsonValue.NoDupKeys`

Recursive tree predicate. Holds when every `JsonValue.object` node in the tree has distinct
field keys.

```lean
private def JsonValue.NoDupKeys : JsonValue → Prop
  | .object fields =>
      List.Nodup (fields.map Prod.fst) ∧
      ∀ p ∈ fields, p.2.NoDupKeys
  | .array elems   => ∀ e ∈ elems, e.NoDupKeys
  | _              => True
```

`List.Nodup` from Mathlib; `p.2.NoDupKeys` recurses on values.

### `JsonValue.allKeysIn`

Holds when every key in an `object` constructor is in the allowed list. Non-object values
vacuously satisfy it.

```lean
private def JsonValue.allKeysIn (allowed : List String) : JsonValue → Prop
  | .object fields => ∀ p ∈ fields, p.1 ∈ allowed
  | _              => True
```

---

## Schema-defined object types

26 object types have `additionalProperties: false` in the OpenTrackIO schema and require
`WellFormed*` predicates. Listed bottom-up (leaves first, composites after).

### Leaf types (no schema-object sub-fields)

| Predicate | Field keys | Required keys |
|---|---|---|
| `WellFormedPositiveRational` | `num`, `denom` | both |
| `WellFormedGlobalStage` | `E`, `N`, `U`, `lat0`, `lon0`, `h0` | all |
| `WellFormedSensorPhysDims` | `height`, `width` | both |
| `WellFormedSensorResolution` | `height`, `width` | both |
| `WellFormedVec3` | `x`, `y`, `z` | all |
| `WellFormedRotation` | `pan`, `tilt`, `roll` | all |
| `WellFormedDistortionOffset` | `x`, `y` | both |
| `WellFormedProjectionOffset` | `x`, `y` | both |
| `WellFormedLeaderPriorities` | `priority1`, `priority2` | both |
| `WellFormedSyncOffsets` | `translation`, `rotation`, `lensEncoders` | none |
| `WellFormedFizOptions` | `focus`, `iris`, `zoom` | none |
| `WellFormedStaticTracker` | `make`, `model`, `serialNumber`, `firmwareVersion` | none |
| `WellFormedTracker` | `notes`, `recording`, `slate`, `status` | none |

"Required" means the field must be present for the decoder to return `.ok`; optional fields
may be absent.

### Composite types (contain schema-object sub-fields)

**`WellFormedExposureFalloff`**: keys `a1`, `a2`, `a3`; `a1` required; no sub-objects.

**`WellFormedDistortion`**: keys `radial`, `tangential`, `overscan`, `model`; `radial`
required. Sub-object: none (radial/tangential are number arrays).

**`WellFormedTimestamp`**: keys `seconds`, `nanoseconds`; both required. No sub-objects
(both values are number-strings).

**`WellFormedProtocol`**: keys `name`, `version`; both required. `version` value is a
3-element JSON array (not a schema object), so no sub-predicate for it.

**`WellFormedCamera`**: keys `captureFrameRate`, `activeSensorPhysicalDimensions`,
`activeSensorResolution`, `make`, `model`, `serialNumber`, `firmwareVersion`, `label`,
`anamorphicSqueeze`, `isoSpeed`, `fdlLink`, `shutterAngle`; all optional. Sub-objects:
`activeSensorPhysicalDimensions` → `WellFormedSensorPhysDims`;
`activeSensorResolution` → `WellFormedSensorResolution`.

**`WellFormedStaticLens`**: keys `distortionOverscanMax`, `undistortionOverscanMax`, `make`,
`model`, `serialNumber`, `firmwareVersion`, `nominalFocalLength`, `calibrationHistory`; all
optional. No sub-objects (calibrationHistory is a string array, not a schema object).

**`WellFormedStaticInfo`**: keys `duration`, `camera`, `lens`, `tracker`; all optional.
Sub-objects: `duration` → `WellFormedPositiveRational`; `camera` → `WellFormedCamera`;
`lens` → `WellFormedStaticLens`; `tracker` → `WellFormedStaticTracker`.

**`WellFormedTransform`**: keys `id`, `translation`, `rotation`, `scale`; `translation`
and `rotation` required. Sub-objects: `translation` → `WellFormedVec3`;
`rotation` → `WellFormedRotation`. `scale` and `id` are not sub-objects (number and string).

**`WellFormedLens`**: keys `custom`, `distortion`, `distortionOffset`, `encoders`,
`entrancePupilOffset`, `exposureFalloff`, `fStop`, `focusDistance`, `pinholeFocalLength`,
`projectionOffset`, `rawEncoders`, `tStop`; all optional. Sub-objects:
`distortionOffset` → `WellFormedDistortionOffset`;
`encoders` → `WellFormedFizOptions`; `rawEncoders` → `WellFormedFizOptions`;
`exposureFalloff` → `WellFormedExposureFalloff`;
`projectionOffset` → `WellFormedProjectionOffset`;
`distortion` → each element satisfies `WellFormedDistortion` (NonemptyArray).

**`WellFormedPtpInfo`**: keys `profile`, `domain`, `leaderIdentity`, `leaderPriorities`,
`leaderAccuracy`, `meanPathDelay`, `leaderTimeSource`, `vlan`; first 6 required, last 2
optional. Sub-objects: `leaderPriorities` → `WellFormedLeaderPriorities`.

**`WellFormedSynchronization`**: keys `locked`, `source`, `frequency`, `offsets`, `present`,
`ptp`; `locked` and `source` required. Sub-objects: `offsets` → `WellFormedSyncOffsets`;
`frequency` → `WellFormedPositiveRational`; `ptp` → `WellFormedPtpInfo`.

**`WellFormedTimecode`**: keys `hours`, `minutes`, `seconds`, `frames`, `frameRate`,
`subFrame`, `dropFrame`; first 5 required. Sub-object: `frameRate` → `WellFormedPositiveRational`.

**`WellFormedTiming`**: keys `mode`, `recordedTimestamp`, `sampleRate`, `sampleTimestamp`,
`sequenceNumber`, `synchronization`, `timecode`; all optional. Sub-objects:
`recordedTimestamp` → `WellFormedTimestamp`; `sampleTimestamp` → `WellFormedTimestamp`;
`sampleRate` → `WellFormedPositiveRational`;
`synchronization` → `WellFormedSynchronization`; `timecode` → `WellFormedTimecode`.

---

## Predicate sketch

Each `WellFormed*` predicate follows this template:

```lean
private def WellFormedFoo (j : JsonValue) : Prop :=
  j.allKeysIn ["key1", "key2", ...]         -- no unknown fields
  ∧ j.hasField "requiredKey1"               -- required fields present
  ∧ j.hasField "requiredKey2"               -- (omit for all-optional types)
  ∧ (∀ vj, j.lookup? "subField" = some vj → WellFormedBar vj)  -- sub-objects
```

For arrays of sub-objects (e.g., `distortion` in Lens):
```lean
  ∧ (∀ arr, j.lookup? "distortion" = some (.array arr) →
       ∀ e ∈ arr, WellFormedDistortion e)
```

---

## Top-level predicate

```lean
def WellFormedSampleJson (j : JsonValue) : Prop :=
  j.NoDupKeys                                   -- recursive dup-key check
  ∧ (∀ vj, j.lookup? "globalStage" = some vj → WellFormedGlobalStage vj)
  ∧ (∀ vj, j.lookup? "lens"        = some vj → WellFormedLens vj)
  ∧ (∀ vj, j.lookup? "protocol"    = some vj → WellFormedProtocol vj)
  ∧ (∀ vj, j.lookup? "static"      = some vj → WellFormedStaticInfo vj)
  ∧ (∀ vj, j.lookup? "timing"      = some vj → WellFormedTiming vj)
  ∧ (∀ vj, j.lookup? "tracker"     = some vj → WellFormedTracker vj)
  ∧ (∀ vj, j.lookup? "transforms"  = some vj →
       ∀ arr, vj = .array arr → ∀ e ∈ arr, WellFormedTransform e)
  -- relatedSampleIds: array of strings — no schema-object sub-predicate
  -- sampleId, sourceId, sourceNumber: scalars — no sub-predicate
  -- No allKeysIn on Sample itself (extension-tolerant per A3)
```

`NoDupKeys` at the root covers all descendant object nodes, so no per-field NoDupKeys
assertions are needed inside the per-type predicates.

---

## Scope boundaries

**Included:**
- No-unknown-fields for all 26 schema-defined object types
- Required-fields-present for all object types with at least one required field
- Global `NoDupKeys` via root assertion
- Sub-object well-formedness (recursive, bottom-up)

**Not included:**
- No `allKeysIn` on Sample itself (extension-tolerant)
- No regex validation (e.g., MAC address patterns, UUID formats)
- No numeric range bounds beyond what `PositiveRational` / `Fin 10` already enforce
- No minimum-field counts beyond what required-field assertions cover
- No decidability instances (predicate is a `Prop`, not `Decidable`)

---

## Stop 2 checklist (preview)

- [ ] All 26 `WellFormed*` helpers defined and compile
- [ ] `WellFormedSampleJson` defined
- [ ] All helpers `private`, `WellFormedSampleJson` public
- [ ] No `sorry`, `admit`, `axiom`, `unsafe`, `partial`
- [ ] `lake build WellFormedSampleJson` exits 0, no warnings
