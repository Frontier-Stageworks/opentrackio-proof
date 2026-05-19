# Slice 16B — Proof Plan
# normalization-theorems

**Status:** VERIFIED — `lake build NormalizationTheorems` exits 0, no warnings, 15s
**Date:** 2026-05-19

---

## Definitions

| Name | Visibility |
|---|---|
| `sampleNormalize` | public |

## Theorems

| Name | Visibility |
|---|---|
| `sampleNormalize_idempotent` | public |
| `encodedSample_stable` | public |
| `sampleNormalize_encodeSample` | public |
| `wellFormed_normalize_eq_encode` | public |
| `normalization_under_wellFormed` | public |

---

## Proof techniques

### `sampleNormalize_idempotent`

Two-branch proof via `cases h : decodeSample j with`.

**`.ok s` branch:**
```lean
have heq : sampleNormalize j = encodeSample s := by simp only [sampleNormalize, h]
rw [heq]
simp only [sampleNormalize, encodeSample_roundtrip]
```
`rw [heq]` reduces goal to `sampleNormalize (encodeSample s) = encodeSample s`. `simp only`
unfolds `sampleNormalize` and rewrites `decodeSample (encodeSample s)` via
`encodeSample_roundtrip`, reducing the match to `encodeSample s`.

**`.error e` branch:**
```lean
have heq : sampleNormalize j = j := by simp only [sampleNormalize, h]
simp only [heq]
```
`simp only [heq]` iteratively replaces `sampleNormalize j` → `j`, closing
`sampleNormalize (sampleNormalize j) = sampleNormalize j` to `j = j`.

### Remaining theorems

All closed by `simp only [sampleNormalize, ...]` unfolding the definition and
`encodeSample_roundtrip` reducing the relevant `decodeSample (encodeSample s)` subterm.
`encodedSample_stable` is a one-line term-mode proof.

---

## Deviations from capsule

**`normalize` → `sampleNormalize`:** `normalize` is already defined in Mathlib; the name
clashes at the declaration site. Renamed `sampleNormalize` throughout.

**`simp only` throughout:** Bare `simp [...]` triggered Mathlib ring/algebra simp lemmas
that attempted to synthesize `CommMonoidWithZero JsonValue`, producing spurious goals. All
proofs use `simp only [...]` with explicit lemma lists to avoid this.

**`rcases` syntax not needed:** The capsule sketched `rcases h : decodeSample j with | ok s | error e`.
In practice `cases h : decodeSample j with | ok s => ... | error e => ...` is cleaner and correct.

---

## Stop 2 checklist

- [x] `sampleNormalize` defined
- [x] All 5 theorems proved
- [x] No `sorry`, `admit`, `axiom`, `unsafe`, `partial`
- [x] `lake build NormalizationTheorems` exits 0, no warnings, 15s
