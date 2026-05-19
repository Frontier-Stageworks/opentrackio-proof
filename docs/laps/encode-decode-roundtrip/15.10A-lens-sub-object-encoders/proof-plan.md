# Slice 15.10A — Proof Plan
# lens-sub-object-encoders

**Status:** VERIFIED — `lake build LensSubEncoders` exits 0, no warnings, 8.2s  
**Date:** 2026-05-19

---

## Encoders implemented

| Encoder | Input type | Output |
|---|---|---|
| `encodeFizOptions` | `FizOptions` | `.object` with 0–3 fields |
| `encodeDistortionOffset` | `DistortionOffset` | `.object [x, y]` |
| `encodeProjectionOffset` | `ProjectionOffset` | `.object [x, y]` |
| `encodeExposureFalloff` | `ExposureFalloff` | `.object` with 1–3 fields |
| `encodeNonemptyStringArray` | `NonemptyArray String` | `.array` (elements as `.number`) |
| `encodeDistortion` | `Distortion` | `.object` with 2–4 fields |

---

## Infrastructure lemmas

### `list_mapM_ok`

```
∀ xs : List α, (xs.map enc).mapM dec = .ok xs
```

Proved by induction. The cons case residual after `simp [List.mapM_cons, hrt hd, ih]` is:

```
(do let __do_lift ← Except.ok hd; Except.ok (__do_lift :: tl)) = Except.ok (hd :: tl)
```

This is definitionally true — `Except.bind (.ok a) f = f a` by the monad definition, not a named lemma. Closed by `rfl`.

**Key insight:** `Except.bind_ok` does not exist in Lean 4. Do not add it to the simp set.

### `decodeNonemptyArray_roundtrip`

```
decodeNonemptyArray dec ctx (.array (arr.values.map enc)) = .ok arr
```

Proof:
1. Destruct `arr` as `⟨vals, hne⟩`, then `rcases List.exists_cons_of_ne_nil hne` to get `hd, tl, rfl` — gives Lean a concrete cons list to unfold `decodeNonemptyArray` on.
2. `simp only [List.map_cons, decodeNonemptyArray, show dec (enc hd) = .ok hd from hrt hd, show (tl.map enc).mapM dec = .ok tl from list_mapM_ok enc dec hrt tl]`
3. Close with `rfl`.

The final `rfl` covers two things simultaneously:
- Monad laws: `Except.bind (.ok x) f = f x` is definitional.
- Proof irrelevance: the `nonempty : values ≠ []` field of `NonemptyArray` is a `Prop`; Lean 4's kernel treats all proofs of the same `Prop` as definitionally equal, so the reconstructed `NonemptyArray.mk` with a new proof equals the original.

---

## Roundtrip theorems

### `encodeFizOptions_roundtrip`

Destructs `⟨fo, ir, zo, hap⟩`. Case-splits `fo`, `ir`, `zo` each as `none | some`. The `none/none/none` case has a false hypothesis (`hap : ¬(none = none ∧ none = none ∧ none = none)`) — closed by `simp_all` after the main `simp`.

### `encodeDistortionOffset_roundtrip` / `encodeProjectionOffset_roundtrip`

Trivial: destructs `⟨x, y⟩`, closes with `simp [encoder, decoder, JsonValue.lookup?]`.

### `encodeExposureFalloff_roundtrip`

Case-splits `a2` and `a3` (2 × 2 = 4 goals). All goals closed by `simp [encodeExposureFalloff, decodeExposureFalloff, JsonValue.lookup?]` — no residual.

### `encodeDistortion_roundtrip`

**Critical pattern:** `decodeDistortion` calls `decodeNonemptyArray` which calls a *private* `decodeNumberString` that simp cannot see. The approach:

1. Define local `decodeNumStr` with the same body.
2. Prove `decodeDistortion_unfold : decodeDistortion = fun j => ... decodeNumStr ...` by `rfl` (definitional equality of private/local copies).
3. Prove `encodeNonemptyStringArray_rt` using `decodeNonemptyArray_roundtrip`.
4. In the main proof: `rw [decodeDistortion_unfold]`, then case-split `tangential` and `overscan` (2 × 2 = 4 goals).
5. `simp [encodeDistortion, encodeNonemptyStringArray_rt, JsonValue.lookup?, Except.map]`

**Critical constraint:** Do NOT include `encodeNonemptyStringArray` in the simp set alongside `encodeNonemptyStringArray_rt`. If simp expands `encodeNonemptyStringArray` before `encodeNonemptyStringArray_rt` can match, the roundtrip lemma's LHS no longer appears in the goal and the lemma becomes unused.

The `<;> rfl` residual closes remaining do-bind goals definitionally.

---

## Deviations from capsule

None. The capsule correctly identified all required infrastructure and the private-copy pattern for `decodeDistortion`. The only discovery during implementation was the `Except.bind_ok` non-existence (closed by `rfl` instead) and the simp-ordering constraint on `encodeNonemptyStringArray_rt`.

---

## Heartbeat notes

No `set_option maxHeartbeats` override required. Default heartbeats (200,000) sufficient — largest proof is `encodeFizOptions_roundtrip` (8 goals) and `encodeDistortion_roundtrip` (4 goals). Build time: 8.2s.

---

## Stop 2 checklist

- [x] All encoders defined
- [x] All roundtrip theorems proved
- [x] `lake build LensSubEncoders` exits 0
- [x] No warnings
- [x] No `sorry`, `admit`, `axiom`, `unsafe`, or `partial`
- [x] Infrastructure lemmas documented with rationale
- [x] Critical simp-ordering constraint documented
