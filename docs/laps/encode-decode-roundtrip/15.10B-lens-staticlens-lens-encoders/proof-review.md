# Proof Review — lens-staticlens-lens-encoders (Slice 15.10B)

## Acceptance checks

| Check | Result |
|---|---|
| `lake build LensEncoder` | exit 0, no warnings, 561s |
| `encodeStaticLens_roundtrip` public, no `sorry` | ✓ |
| `encodeLens_roundtrip` public, no `sorry` | ✓ |
| All helpers private, no `sorry` | ✓ |

## Deviations from plan

Three deviations discovered during implementation; all documented in proof-plan.md:

1. **Explicit types required for `list_mapM_ok'`** — type inference inferred `α = JsonValue`
   when underscores were used for `enc` and `dec`. Fix: annotate `enc` and `dec` explicitly.

2. **`decodeCustom'` absent from `encodeLens_roundtrip` simp set** — including it caused
   simp to expand `decodeCustom' (encodeCustom cu)` into a match form that `encodeCustom_rt`
   could no longer match against. Identical to the `encodeNonemptyStringArray` trap from 15.10A.

3. **`set_option maxHeartbeats 10000000` for `encodeStaticLens_roundtrip`** — 256 goals
   with four `decodeOptStr` unfolds and `dif_pos` discharges exceeded the 200,000 default.

## Key proof notes

**Private-copy + `rfl`-unfold pattern:** `decodeStaticLens` and `decodeLens` each call
private helpers invisible to simp. Local copies with identical bodies are defined; unfold
theorems are proved by `rfl` (definitional equality). `rw [decode*_unfold]` at the top of
each roundtrip proof makes the goal transparent before simp runs.

**`decodeOptStr` in simp for `encodeStaticLens_roundtrip`:** Unlike the `encodeLens`
pattern, here we DO want simp to unfold `decodeOptStr` so it can discharge the
`if h : v ≠ ""` guards via `*` (NonemptyString proof hypotheses from `rcases ⟨v, h⟩`).
The key distinction: `decodeOptStr` has no companion `_rt` lemma — it is the terminal
unfoldable form.

**`encodeCustom_rt`/`encodeDistortionArray_rt` as opaque simp rules:** For `encodeLens_roundtrip`,
the list and array helper decoders (`decodeCustom'`, `decodeNonemptyArray`) must stay
opaque in the simp set. Only their composed `_rt` roundtrip lemmas are added, which
rewrite `dec (enc x) ↦ .ok x` in one step.

**`list_mapM_ok'` per-element proofs:**
- `encodeCustom_rt`: per-element is `rfl` (`.number s` → `decodeCustom' elem` → `.ok s`)
- `encodeCalibrationHistory_rt`: per-element needs `obtain ⟨v, hv⟩ := ns; simp [dif_pos hv]`
  because `NonemptyString` carries a proof field; proof irrelevance closes the residual.

**`<;> rfl` residuals:** Both roundtrip proofs end with `<;> rfl` to close do-bind
expansions (`Except.bind (.ok a) f = f a` is definitional) and proof irrelevance goals
(`⟨v, h1⟩ = ⟨v, h2⟩` for `Prop` fields, definitional in Lean 4's kernel).

## Status: COMPLETE
