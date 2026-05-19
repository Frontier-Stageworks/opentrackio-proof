# Proof Capsule — lens-encoder (Slice 15.10) — SPLIT

> **Decision**: Slice 15.10 was split into 15.10A and 15.10B before any code was written.
> Two risks justified the split:
> 1. `decodeNonemptyArray_roundtrip` is new proof machinery (rcases on nonempty list +
>    `List.mapM` over `Except`) not previously proved in this project — isolated risk.
> 2. Private helper re-exposure (`decodeNumberString`, `decodeCalibrationHistory`,
>    `decodeCustom`) requires verbose `_unfold` theorems for both decoders; combining
>    with 4096-goal Lens proof in one slice is unsafe.
>
> See `15.10A-lens-sub-object-encoders/proof-capsule.md` and
> `15.10B-lens-staticlens-lens-encoders/proof-capsule.md` for active contracts.

---

## Scope

Seven encoders and seven roundtrip theorems:

| Artifact | Status |
|---|---|
| `encodeFizOptions` | NEW |
| `encodeDistortionOffset` | NEW |
| `encodeProjectionOffset` | NEW |
| `encodeExposureFalloff` | NEW |
| `encodeDistortion` | NEW |
| `encodeStaticLens` | NEW |
| `encodeLens` | NEW |
| `encodeFizOptions_roundtrip` | NEW |
| `encodeDistortionOffset_roundtrip` | NEW |
| `encodeProjectionOffset_roundtrip` | NEW |
| `encodeExposureFalloff_roundtrip` | NEW |
| `encodeDistortion_roundtrip` | NEW |
| `encodeStaticLens_roundtrip` | NEW |
| `encodeLens_roundtrip` | NEW |

File: `opentrackio_parser/LensEncoder.lean`
Library name: `LensEncoder`
Lakefile entry: after `CameraEncoder`

---

## Dependencies

| Import | Provides |
|---|---|
| `Mathlib` | tactics |
| `LensDecoder` | all public decoders and `NonemptyArray` |
| `CameraEncoder` | `encodeCamera_roundtrip` (not used here — listed for ordering) |
| `TimecodeEncoder` | `encodePositiveRational`, `encodePositiveRational_roundtrip` |
| `NumericLiteralRoundtrip` | `nat_repr_toNat?_some` |

`LensDecoder` transitively imports `NonemptyArrayDecoder`, making `decodeNonemptyArray`
and the `NonemptyArray` structure available.

---

## New proof machinery (not seen in prior slices)

### 1. `decodeNonemptyArray_roundtrip` — general helper

`decodeNonemptyArray` takes `(hd :: tl)` from the array and does:
```
let v  ← decodeElem hd
let vs ← tl.mapM decodeElem
return { values := v :: vs, nonempty := List.cons_ne_nil v vs }
```

The general roundtrip helper:
```lean
private theorem decodeNonemptyArray_roundtrip
    {α : Type} (enc : α → JsonValue) (dec : JsonValue → Except DecodeError α)
    (hrt : ∀ a, dec (enc a) = .ok a) (ctx : String) (arr : NonemptyArray α) :
    decodeNonemptyArray dec ctx (.array (arr.values.map enc)) = .ok arr
```

**Proof strategy**: destructure `arr.values` into `hd :: tl` via `arr.nonempty`, then `simp`
with `decodeNonemptyArray`, `hrt`, and `List.mapM_map` / `List.mapM_pure` to reduce
`(tl.map enc).mapM dec = .ok tl`. The `nonempty` field equality closes by proof irrelevance.

### 2. `List.mapM` pure lemma

Required sub-lemma for the `NonemptyArray` roundtrip:
```lean
private theorem list_mapM_ok {α : Type} (dec : JsonValue → Except DecodeError α)
    (enc : α → JsonValue) (hrt : ∀ a, dec (enc a) = .ok a) :
    ∀ xs : List α, xs.mapM (fun a => dec (enc a)) = .ok xs
```
Proved by induction on `xs`. Base: `.ok []`. Step: `simp [hrt, List.mapM_cons]`.

### 3. Private helper access

`LensDecoder.lean` defines three **private** helpers used by `decodeStaticLens` and `decodeLens`:
- `decodeNumberString` (used inside `decodeDistortion` via `decodeNonemptyArray`)
- `decodeCalibrationHistory` (used by `decodeStaticLens`)
- `decodeCustom` (used by `decodeLens`)

Since these are private, they are not accessible from `LensEncoder.lean`. Strategy (established
in `TrackerEncoder.lean`):
1. Re-define each as a local copy with the same body.
2. Prove `decodeStaticLens_unfold` and `decodeLens_unfold` as `rfl` equations rewriting
   the public decoder in terms of the local copies.
3. Begin proofs with `rw [decodeStaticLens_unfold]` / `rw [decodeLens_unfold]`.

`decodeDistortion` IS public, so `encodeDistortion_roundtrip` can be used as a simp rule
in `encodeLens_roundtrip` without needing to unfold its internals.

### 4. `FizOptions.anyPresent` — proof irrelevance (established pattern)

`decodeFizOptions` does `if h : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none then .ok { ..., anyPresent := h }`.
After encoding a `FizOptions fiz`, the decoded result has `anyPresent := witness_h` which
equals `fiz.anyPresent` by proof irrelevance (`∨`-propositions are `Prop`).
Pattern: `rcases fiz.focus; rcases fiz.iris; rcases fiz.zoom` to make fields concrete,
then `simp [decodeFizOptions, *]` fires `dif_pos`.

---

## Frozen formal statements

### Simple sub-objects

```lean
def encodeDistortionOffset (d : DistortionOffset) : JsonValue :=
  .object [("x", .number d.x), ("y", .number d.y)]

def encodeProjectionOffset (p : ProjectionOffset) : JsonValue :=
  .object [("x", .number p.x), ("y", .number p.y)]

def encodeExposureFalloff (ef : ExposureFalloff) : JsonValue :=
  .object (
    [("a1", .number ef.a1)] ++
    (ef.a2.map fun s => ("a2", .number s)).toList ++
    (ef.a3.map fun s => ("a3", .number s)).toList)
```

### FizOptions

```lean
def encodeFizOptions (fiz : FizOptions) : JsonValue :=
  .object (
    (fiz.focus.map fun s => ("focus", .number s)).toList ++
    (fiz.iris.map  fun s => ("iris",  .number s)).toList ++
    (fiz.zoom.map  fun s => ("zoom",  .number s)).toList)
```

### Distortion

```lean
def encodeNonemptyStringArray (arr : NonemptyArray String) : JsonValue :=
  .array (arr.values.map .number)

def encodeDistortion (d : Distortion) : JsonValue :=
  .object (
    [("radial", encodeNonemptyStringArray d.radial),
     ("model",  .string d.model)] ++
    (d.tangential.map fun arr => ("tangential", encodeNonemptyStringArray arr)).toList ++
    (d.overscan.map   fun s   => ("overscan",   .number s)).toList)
```

Note: `model` is always encoded (even when "Brown-Conrady D-U") so the decoder's
`some (.string s) => .ok s` arm fires and the roundtrip holds.

### StaticLens

```lean
def encodeCalibHistElem (ns : NonemptyString) : JsonValue := .string ns.val

def encodeStaticLens (sl : StaticLens) : JsonValue :=
  .object (
    (sl.distortionOverscanMax.map   fun s  => ("distortionOverscanMax",   .number s)).toList ++
    (sl.undistortionOverscanMax.map fun s  => ("undistortionOverscanMax", .number s)).toList ++
    (sl.make.map            fun ns => ("make",            .string ns.val)).toList ++
    (sl.model.map           fun ns => ("model",           .string ns.val)).toList ++
    (sl.serialNumber.map    fun ns => ("serialNumber",    .string ns.val)).toList ++
    (sl.firmwareVersion.map fun ns => ("firmwareVersion", .string ns.val)).toList ++
    (sl.nominalFocalLength.map fun s => ("nominalFocalLength", .number s)).toList ++
    (sl.calibrationHistory.map fun xs =>
      ("calibrationHistory", .array (xs.map encodeCalibHistElem))).toList)
```

### Lens

```lean
def encodeLens (l : Lens) : JsonValue :=
  .object (
    (l.custom.map fun xs =>
      ("custom", .array (xs.map .number))).toList ++
    (l.distortion.map fun arr =>
      ("distortion", .array (arr.values.map encodeDistortion))).toList ++
    (l.distortionOffset.map fun d =>
      ("distortionOffset", encodeDistortionOffset d)).toList ++
    (l.encoders.map fun fiz =>
      ("encoders", encodeFizOptions fiz)).toList ++
    (l.entrancePupilOffset.map fun s => ("entrancePupilOffset", .number s)).toList ++
    (l.exposureFalloff.map fun ef =>
      ("exposureFalloff", encodeExposureFalloff ef)).toList ++
    (l.fStop.map         fun s => ("fStop",         .number s)).toList ++
    (l.focusDistance.map fun s => ("focusDistance", .number s)).toList ++
    (l.pinholeFocalLength.map fun s => ("pinholeFocalLength", .number s)).toList ++
    (l.projectionOffset.map fun p =>
      ("projectionOffset", encodeProjectionOffset p)).toList ++
    (l.rawEncoders.map fun fiz =>
      ("rawEncoders", encodeFizOptions fiz)).toList ++
    (l.tStop.map fun s => ("tStop", .number s)).toList)
```

---

## Goal counts and heartbeat estimates

| Theorem | Goals | Estimate |
|---|---|---|
| `encodeFizOptions_roundtrip` | 8 (2^3 fields) | default |
| `encodeDistortionOffset_roundtrip` | 1 | default |
| `encodeProjectionOffset_roundtrip` | 1 | default |
| `encodeExposureFalloff_roundtrip` | 4 (2^2 optional) | default |
| `encodeDistortion_roundtrip` | 4 (2^2 optional, radial concrete) | default |
| `encodeStaticLens_roundtrip` | 256 (2^8) | ~800000 |
| `encodeLens_roundtrip` | 4096 (2^12) | ~40000000 |

---

## Out of scope

- Encoding `Lens` or `StaticLens` inside a `Sample` — handled by `SampleEncoder` (15.11).
- No changes to any completed slice.
- No changes to `LensDecoder.lean`.

---

## Stop rule

This capsule is complete. Do NOT proceed to the proof plan until the user signs off.
