# Slice 15.11 — Proof Plan
# sample-encoder

**Status:** VERIFIED — `lake build SampleEncoder` exits 0, no warnings, 229s  
**Date:** 2026-05-19

---

## Encoders implemented

| Encoder | Visibility |
|---|---|
| `encodeStaticInfo` | private helper |
| `encodeSample` | public |

`relatedSampleIds` and `transforms` arrays inlined in `encodeSample` (no named helper),
to avoid the pre-expansion trap.

---

## Infrastructure

### Local decoder copies

| Local copy | Mirrors (private in SampleDecoder) |
|---|---|
| `decodeRelId'` | `decodeRelatedId` |
| `decodeStaticInfo'` | `decodeStaticInfo` |

Unfold theorem proved by `rfl`:
```
decodeSample_unfold : decodeSample = fun j => ... decodeRelId' ... decodeStaticInfo' ...
```

`decodeStaticInfo'` calls only public decoders (`decodeCamera`, `decodeStaticLens`,
`decodeStaticTracker`, `decodePositiveRational`) — no further unfold required.

### Infrastructure lemmas

`list_mapM_ok'` and `decodeNonemptyArray_roundtrip'` reproved locally (private in prior slices).

### Helper roundtrip lemmas

**`encodeRelatedIds_rt`:**
```
rs.mapM (decodeRelId' ∘ JsonValue.string) = .ok rs
```

Key deviation: capsule stated the lemma as `(rs.map JsonValue.string).mapM decodeRelId' = .ok rs`.
Simp applies `List.mapM_map` (a Mathlib lemma) to fuse the `map` + `mapM` into a single
`mapM` with composed function `decodeRelId' ∘ JsonValue.string`. The original statement
no longer matches the post-simp goal. Fix: state the lemma in the composed form and
prove by induction with `simp only [List.mapM_cons, Function.comp, decodeRelId', ih]; rfl`.

**`encodeTransformArr_rt`:**
```
∀ ctx ta, decodeNonemptyArray decodeTransform ctx (.array (ta.values.map encodeTransform)) = .ok ta
```
Direct application of `decodeNonemptyArray_roundtrip'` with `encodeTransform_roundtrip`.

**`encodeStaticInfo_rt`:**
```
∀ si, decodeStaticInfo' (encodeStaticInfo si) = .ok si
```
16 goals (2^4); rcases all 4 StaticInfo fields; simp with sub-encoder roundtrip lemmas.
Default heartbeats sufficient.

---

## Roundtrip theorem

### `encodeSample_roundtrip` (2048 goals, 2^11)

1. `rw [decodeSample_unfold]`
2. `obtain` all 11 fields; `rcases` each as `_ | val`
3. `simp [encodeSample, encodeStaticInfo_rt, encodeRelatedIds_rt, encodeTransformArr_rt, encodeGlobalStage_roundtrip, encodeLens_roundtrip, encodeProtocol_roundtrip, encodeTiming_roundtrip, encodeTracker_roundtrip, JsonValue.lookup?, Except.map]`
4. `<;> rfl`

`encodeStaticInfo` NOT in simp set — only `encodeStaticInfo_rt` — to prevent
pre-expansion before the roundtrip lemma can match `decodeStaticInfo' (encodeStaticInfo si)`.

`set_option maxHeartbeats 40000000` — 2048 goals.

---

## Deviations from capsule

**`encodeRelatedIds_rt` form:** Capsule predicted the map-then-mapM form. Simp applies
`List.mapM_map` to fuse them into composed-function form. Lemma must be stated as
`rs.mapM (decodeRelId' ∘ JsonValue.string) = .ok rs` and proved by induction.

---

## Stop 2 checklist

- [x] Both encoders defined
- [x] `encodeSample_roundtrip` proved
- [x] `lake build SampleEncoder` exits 0
- [x] No warnings
- [x] No `sorry`, `admit`, `axiom`, `unsafe`, or `partial`
- [x] Composed-mapM form for `encodeRelatedIds_rt` documented
