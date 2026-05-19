# Slice 15.10B — Proof Capsule
# lens-staticlens-lens-encoders

**Date:** 2026-05-19  
**Depends on:** 15.10A (LensSubEncoders)  
**Output file:** `opentrackio_parser/LensEncoder.lean`  
**Lake lib name:** `LensEncoder`

---

## Scope

Encoders and encode-decode roundtrip theorems for `StaticLens` and `Lens`.
The sub-object encoders (FizOptions, DistortionOffset, ProjectionOffset,
ExposureFalloff, Distortion) were completed in Slice 15.10A and are imported
via `LensSubEncoders`.

---

## Structures to encode

### StaticLens (8 optional fields)

| Field | Type | Encoding |
|---|---|---|
| `distortionOverscanMax` | `Option String` | `.number` |
| `undistortionOverscanMax` | `Option String` | `.number` |
| `make` | `Option NonemptyString` | `.string ns.val` |
| `model` | `Option NonemptyString` | `.string ns.val` |
| `serialNumber` | `Option NonemptyString` | `.string ns.val` |
| `firmwareVersion` | `Option NonemptyString` | `.string ns.val` |
| `nominalFocalLength` | `Option String` | `.number` |
| `calibrationHistory` | `Option (List NonemptyString)` | `.array` of `.string` |

### Lens (12 optional fields)

| Field | Type | Encoding |
|---|---|---|
| `custom` | `Option (List String)` | `.array` of `.number` |
| `distortion` | `Option (NonemptyArray Distortion)` | `.array` via `encodeDistortion` |
| `distortionOffset` | `Option DistortionOffset` | via `encodeDistortionOffset` |
| `encoders` | `Option FizOptions` | via `encodeFizOptions` |
| `entrancePupilOffset` | `Option String` | `.number` |
| `exposureFalloff` | `Option ExposureFalloff` | via `encodeExposureFalloff` |
| `fStop` | `Option String` | `.number` |
| `focusDistance` | `Option String` | `.number` |
| `pinholeFocalLength` | `Option String` | `.number` |
| `projectionOffset` | `Option ProjectionOffset` | via `encodeProjectionOffset` |
| `rawEncoders` | `Option FizOptions` | via `encodeFizOptions` |
| `tStop` | `Option String` | `.number` |

---

## Encoders to define

```
encodeCalibrationHistory : List NonemptyString → JsonValue   -- private helper
encodeCustom             : List String → JsonValue            -- private helper
encodeDistortionArray    : NonemptyArray Distortion → JsonValue  -- private helper
encodeStaticLens         : StaticLens → JsonValue
encodeLens               : Lens → JsonValue
```

---

## Private infrastructure required

### Local decoder copies

Three private helpers in `LensDecoder` are not visible to simp:
`decodeOptionalString`, `decodeCalibrationHistory`, `decodeCustom`.

Define local copies with identical bodies:
- `decodeOptStr` (mirrors `decodeOptionalString`)
- `decodeCalHist` (mirrors `decodeCalibrationHistory`)
- `decodeCustom'` (mirrors `decodeCustom`)

Prove:
```
decodeStaticLens_unfold : decodeStaticLens = fun j => ... decodeOptStr ... decodeCalHist ... := rfl
decodeLens_unfold       : decodeLens       = fun j => ... decodeCustom' ...                  := rfl
```

### Infrastructure lemmas

`list_mapM_ok` and `decodeNonemptyArray_roundtrip` are private in
`LensSubEncoders` and cannot be imported. Reprove both locally (identical
statements and proofs — they are short).

### Helper roundtrip lemmas

```
encodeCalibrationHistory_rt : ∀ hist, decodeCalHist (encodeCalibrationHistory hist) = .ok hist
encodeCustom_rt             : ∀ cs, decodeCustom' (encodeCustom cs) = .ok cs
encodeDistortionArray_rt    : ∀ da, decodeNonemptyArray decodeDistortion ctx (encodeDistortionArray da) = .ok da
```

`encodeCalibrationHistory_rt` requires `list_mapM_ok` with the per-element
lemma: `obtain ⟨v, hv⟩ := ns; simp [dif_pos hv]; rfl`.

`encodeCustom_rt` is trivial: per-element roundtrip is `rfl`.

`encodeDistortionArray_rt` follows directly from `decodeNonemptyArray_roundtrip`
using `encodeDistortion_roundtrip` (public from `LensSubEncoders`) as the
per-element proof.

---

## Roundtrip proof strategy

### `encodeStaticLens_roundtrip` (256 goals, 2^8)

1. `rw [decodeStaticLens_unfold]`
2. `obtain` all 8 fields; `rcases` each NonemptyString field as `_ | ⟨v, h⟩`
3. `rcases calibrationHistory` as `_ | ch`
4. `simp [encodeStaticLens, decodeOptStr, encodeCalibrationHistory_rt, JsonValue.lookup?, Except.map, *]`
5. Residual `do`-bind goals closed by `<;> rfl`

NonemptyString proof hypothesis `h : v ≠ ""` enters the simp context via
`rcases`, allowing `dif_pos h` to fire inside `decodeOptStr`.

### `encodeLens_roundtrip` (4096 goals, 2^12)

1. `rw [decodeLens_unfold]`
2. `obtain` all 12 fields; `rcases` FizOptions fields as `_ | fiz`
3. `rcases custom` as `_ | cs`; `rcases distortion` as `_ | da`
4. `simp [encodeLens, encodeCustom_rt, encodeDistortionArray_rt,
          encodeFizOptions_roundtrip, encodeDistortionOffset_roundtrip,
          encodeExposureFalloff_roundtrip, encodeProjectionOffset_roundtrip,
          JsonValue.lookup?, Except.map, *]`
5. Residual goals closed by `<;> rfl`

Expect `set_option maxHeartbeats 40000000` for `encodeLens_roundtrip`
(same 4096-goal cost as `encodeCamera_roundtrip`).

---

## Goal count estimate

| Theorem | Goals |
|---|---|
| `encodeStaticLens_roundtrip` | 2^8 = 256 |
| `encodeLens_roundtrip` | 2^12 = 4096 |

---

## Risk

**Medium.** The `do`-block in both `decodeStaticLens` and `decodeLens` means
goals will contain partially-reduced `do` expressions. The private-copy +
`rfl`-unfold pattern from 15.10A (Distortion) and 15.4 (TrackerEncoder) is
proven to work for this. The `Option (List ...)` and `Option (NonemptyArray ...)`
fields are the main novelty — handled by helper roundtrip lemmas as simp rules,
which keeps simp from having to expand list/array reduction inline.
