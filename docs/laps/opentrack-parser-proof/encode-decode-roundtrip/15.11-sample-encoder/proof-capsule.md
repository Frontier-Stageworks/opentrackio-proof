# Slice 15.11 — Proof Capsule
# sample-encoder

**Date:** 2026-05-19  
**Depends on:** 15.2, 15.3, 15.4, 15.8, 15.9, 15.10B  
**Output file:** `opentrackio_parser/SampleEncoder.lean`  
**Lake lib name:** `SampleEncoder`

---

## Scope decision

Single slice. All required proof patterns are established in prior slices.
No new techniques required. Not split.

---

## Structures to encode

### StaticInfo (4 optional fields — helper, private)

| Field | Type | Encoding |
|---|---|---|
| `duration` | `Option PositiveRational` | via `encodePositiveRational` |
| `camera` | `Option Camera` | via `encodeCamera` |
| `lens` | `Option StaticLens` | via `encodeStaticLens` |
| `tracker` | `Option StaticTracker` | via `encodeStaticTracker` |

### Sample (11 optional fields — public)

| Field | Type | Encoding |
|---|---|---|
| `globalStage` | `Option GlobalStage` | via `encodeGlobalStage` |
| `lens` | `Option Lens` | via `encodeLens` |
| `protocol` | `Option ProtocolInfo` | via `encodeProtocol` |
| `relatedSampleIds` | `Option (List String)` | `.array` of `.string` (inlined) |
| `sampleId` | `Option String` | `.string` |
| `sourceId` | `Option String` | `.string` |
| `sourceNumber` | `Option String` | `.number` |
| `«static»` | `Option StaticInfo` | via `encodeStaticInfo` |
| `timing` | `Option Timing` | via `encodeTiming` |
| `tracker` | `Option Tracker` | via `encodeTracker` |
| `transforms` | `Option (NonemptyArray Transform)` | `.array` via `encodeTransform` (inlined) |

---

## Encoders to define

```
private encodeStaticInfo  : StaticInfo → JsonValue
        encodeSample      : Sample → JsonValue
```

`relatedSampleIds` and `transforms` arrays are inlined in `encodeSample` (no named
helper) to avoid the pre-expansion trap: simp must see the encoded value as a concrete
`.array` form so that decoder-roundtrip lemmas can match.

---

## Private infrastructure required

### Local decoder copies

Two private helpers in `SampleDecoder` are invisible to simp:

| Local copy | Mirrors |
|---|---|
| `decodeRelId'` | `decodeRelatedId` |
| `decodeStaticInfo'` | `decodeStaticInfo` |

Unfold theorem:
```
decodeSample_unfold : decodeSample = fun j => ... decodeRelId' ... decodeStaticInfo' ... := rfl
```

`decodeStaticInfo'` itself calls only public decoders (`decodeCamera`, `decodeStaticLens`,
`decodeStaticTracker`, `decodePositiveRational`), so no further unfold is needed.

### Infrastructure lemmas

`list_mapM_ok'` and `decodeNonemptyArray_roundtrip'` are private in both `LensSubEncoders`
and `LensEncoder`. Reprove locally (identical statements and proofs, 10 lines total).

### Helper roundtrip lemmas

```
encodeRelatedIds_rt  : ∀ rs, (rs.map JsonValue.string).mapM decodeRelId' = .ok rs
encodeTransformArr_rt: ∀ ctx ta, decodeNonemptyArray decodeTransform ctx
                         (.array (ta.values.map encodeTransform)) = .ok ta
encodeStaticInfo_rt  : ∀ si, decodeStaticInfo' (encodeStaticInfo si) = .ok si
```

`encodeRelatedIds_rt`: from `list_mapM_ok'` with per-element `rfl`.

`encodeTransformArr_rt`: from `decodeNonemptyArray_roundtrip'` with `encodeTransform_roundtrip`.

`encodeStaticInfo_rt`: 16 goals (2^4); `rcases` all 4 fields; simp with sub-encoder
roundtrip lemmas as rules.

---

## Roundtrip theorem

### `encodeSample_roundtrip` (2048 goals, 2^11)

1. `rw [decodeSample_unfold]`
2. `obtain` all 11 fields; `rcases` each as `_ | val`
3. `simp [encodeSample, encodeStaticInfo_rt, encodeRelatedIds_rt, encodeTransformArr_rt,
          encodeGlobalStage_roundtrip, encodeLens_roundtrip, encodeProtocol_roundtrip,
          encodeTiming_roundtrip, encodeTracker_roundtrip,
          JsonValue.lookup?, Except.map]`
4. `<;> rfl`

`encodeStaticInfo_rt` used as simp rule (not `decodeStaticInfo'`) — same pre-expansion
discipline as prior slices.

Expect `set_option maxHeartbeats 40000000`.

---

## Imports

```
import Mathlib
import SampleDecoder
import VersionEncoder
import GlobalStageEncoder
import TransformEncoder
import TrackerEncoder
import CameraEncoder
import LensEncoder
import TimingEncoder
```

(`TimecodeEncoder` and `LensSubEncoders` are transitively imported via the above.)

---

## Goal count estimate

| Theorem | Goals |
|---|---|
| `encodeStaticInfo_rt` | 2^4 = 16 |
| `encodeSample_roundtrip` | 2^11 = 2048 |

---

## Risk

**Low–Medium.** All patterns established. Main risks:
- `decodeSample_unfold` body is long (11-field do-block); transcription must be exact
- `relatedSampleIds` uses a 3-way match in the decoder (`none | some (.array elems) | some _`);
  the `some (.array elems)` arm fires when encoder produces `.array`; simp handles this
  since the encoded form is concrete `.array (rs.map .string)` after `encodeSample` unfolds
