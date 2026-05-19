# Slice 15.10B — Proof Plan
# lens-staticlens-lens-encoders

**Status:** VERIFIED — `lake build LensEncoder` exits 0, no warnings, 561s  
**Date:** 2026-05-19

---

## Encoders implemented

| Encoder | Type | Visibility |
|---|---|---|
| `encodeCalibrationHistory` | `List NonemptyString → JsonValue` | private helper |
| `encodeCustom` | `List String → JsonValue` | private helper |
| `encodeDistortionArray` | `NonemptyArray Distortion → JsonValue` | private helper |
| `encodeStaticLens` | `StaticLens → JsonValue` | public |
| `encodeLens` | `Lens → JsonValue` | public |

---

## Infrastructure

### Local private copies

Three helpers in `LensDecoder` are private and invisible to simp:

| Local copy | Mirrors |
|---|---|
| `decodeOptStr` | `decodeOptionalString` |
| `decodeCalHist` | `decodeCalibrationHistory` |
| `decodeCustom'` | `decodeCustom` |

Unfold theorems by `rfl`:
```
decodeStaticLens_unfold : decodeStaticLens = fun j => ... decodeOptStr ... decodeCalHist ...
decodeLens_unfold       : decodeLens       = fun j => ... decodeCustom' ...
```

`rfl` holds because each local copy has an identical body to its original — definitional equality.

### Infrastructure lemmas (reproved locally)

`list_mapM_ok'` and `decodeNonemptyArray_roundtrip'` are private in `LensSubEncoders`.
Both are reproved locally with identical statements and proofs.

The `list_mapM_ok'` cons case has a do-bind residual closed by `rfl` (definitional,
`Except.bind_ok` does not exist in Lean 4).

The `decodeNonemptyArray_roundtrip'` final `rfl` covers monad laws + proof irrelevance
simultaneously (both definitional in Lean 4's kernel).

### Helper roundtrip lemmas

**`encodeCalibrationHistory_rt`**: After `simp only [encodeCalibrationHistory, decodeCalHist]`
reduces to a `list_mapM_ok'` goal. Must provide fully explicit types for `enc` and `dec`
(type inference infers wrong `α` with underscores). Per-element proof:
`obtain ⟨v, hv⟩ := ns; simp [dif_pos hv]` — `dif_pos hv` selects the `then` branch;
result is definitionally equal to original by proof irrelevance.

**`encodeCustom_rt`**: Same explicit-type pattern. Per-element proof is `rfl` (`.number s`
decodes directly to `.ok s`).

**`encodeDistortionArray_rt`**: Direct application of `decodeNonemptyArray_roundtrip'`
with `encodeDistortion_roundtrip` (public from `LensSubEncoders`) as the per-element proof.

---

## Roundtrip theorems

### `encodeStaticLens_roundtrip` (256 goals, 2^8)

1. `rw [decodeStaticLens_unfold]`
2. `obtain ⟨dom, udom, mk, mdl, sn, fw, nfl, ch⟩ := sl`
3. `rcases mk/mdl/sn/fw with _ | ⟨v, h⟩` (4 NonemptyString fields)
4. `rcases ch with _ | ch` (calibrationHistory)
5. `rcases dom/udom/nfl with _ | s` (3 plain Option String fields)
6. `simp [encodeStaticLens, decodeOptStr, encodeCalibrationHistory_rt, JsonValue.lookup?, Except.map, *]`
7. `<;> rfl` for do-bind and proof irrelevance residuals

`decodeOptStr` is in the simp set so simp unfolds it directly. With `h : v ≠ ""` in
context via `rcases` + `*`, `dif_pos h` fires automatically for each NonemptyString field.

**Heartbeats:** `set_option maxHeartbeats 10000000` (50× default) — 256 goals with
`decodeOptStr` unfolding plus proof discharge is non-trivial.

### `encodeLens_roundtrip` (4096 goals, 2^12)

1. `rw [decodeLens_unfold]`
2. `obtain` all 12 fields; `rcases` each as `_ | val`
3. `simp [encodeLens, encodeCustom_rt, encodeDistortionArray_rt, encodeFizOptions_roundtrip, encodeDistortionOffset_roundtrip, encodeExposureFalloff_roundtrip, encodeProjectionOffset_roundtrip, JsonValue.lookup?, Except.map]`
4. `<;> rfl`

**Critical:** `decodeCustom'` must NOT be in the simp set. If it is, simp expands
`decodeCustom' (encodeCustom cu)` to a `match (encodeCustom cu) with ...` form, and
`encodeCustom_rt` — which matches `decodeCustom' (encodeCustom cu)` — no longer fires.
Removing `decodeCustom'` keeps the expression in a form `encodeCustom_rt` can rewrite.

Same principle applies to `encodeDistortionArray` — it is NOT in the simp set, so
`encodeDistortionArray_rt` can match `decodeNonemptyArray decodeDistortion ctx (encodeDistortionArray da)`.

**Heartbeats:** `set_option maxHeartbeats 40000000` (200× default) — same 4096-goal
cost as `encodeCamera_roundtrip`.

---

## Deviations from capsule

1. **Explicit types required for `list_mapM_ok'`** — the capsule said `_ _` underscores
   would work; in practice, Lean inferred `α = JsonValue` (wrong). Fix: provide
   `enc` and `dec` explicitly with type annotations.

2. **`decodeCustom'` must be absent from `encodeLens_roundtrip` simp set** — capsule
   listed it; removing it is required to prevent pre-expansion of the custom field decoder
   before `encodeCustom_rt` can match. Same pattern as `encodeNonemptyStringArray` in 15.10A.

3. **`encodeStaticLens_roundtrip` needs `set_option maxHeartbeats 10000000`** — capsule
   predicted default heartbeats sufficient for 256 goals; incorrect. 50× needed.

---

## Stop 2 checklist

- [x] All encoders defined
- [x] Both roundtrip theorems proved
- [x] `lake build LensEncoder` exits 0
- [x] No warnings
- [x] No `sorry`, `admit`, `axiom`, `unsafe`, or `partial`
- [x] Critical simp-ordering constraint (no `decodeCustom'` in `encodeLens` simp) documented
- [x] Explicit types for `list_mapM_ok'` documented
