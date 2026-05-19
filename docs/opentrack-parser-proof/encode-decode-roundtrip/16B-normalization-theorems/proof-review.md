# Proof Review — normalization-theorems (Slice 16B)

## Acceptance checks

| Check | Result |
|---|---|
| `lake build NormalizationTheorems` | exit 0, no warnings, 15s |
| All 5 theorems public, no `sorry` | ✓ |
| `sampleNormalize` public, no `sorry` | ✓ |

## Deviations from capsule

**`normalize` → `sampleNormalize`:** Mathlib already defines `normalize`; the declaration
fails with "has already been declared." Renamed throughout.

**`simp only` throughout:** Bare `simp [h, encodeSample_roundtrip s]` caused Mathlib to
attempt to synthesize `CommMonoidWithZero JsonValue`, producing spurious unrelated goals.
All proofs use `simp only [...]` with explicit lemma lists. Consistent with Mathlib import
discipline established in prior slices.

**`rcases` not needed:** Capsule sketched `rcases h : decodeSample j with | ok s | error e`.
The correct Lean 4 form is `cases h : decodeSample j with | ok s => ... | error e => ...`.

## Key proof notes

**`sampleNormalize_idempotent` structure:** The two-branch proof via `cases h :
decodeSample j` is the cleanest approach. In the `.ok s` branch, `rw [heq]` reduces the
goal to `sampleNormalize (encodeSample s) = encodeSample s`, then `simp only [sampleNormalize,
encodeSample_roundtrip]` closes it by unfolding the match and applying the roundtrip. In
the `.error e` branch, `simp only [heq]` iteratively rewrites `sampleNormalize j → j`
until `j = j` is reached.

**`encodeSample_roundtrip` as the primary engine:** All five theorems reduce to the
roundtrip fact. The `WellFormedSampleJson` hypothesis appears in two theorems
(`wellFormed_normalize_eq_encode`, `normalization_under_wellFormed`) as a domain constraint
but is not used in the proofs — the conclusions follow from roundtrip alone regardless of
well-formedness.

**Scope boundary held:** `WellFormedSampleJson (encodeSample s)` — showing the encoder
always produces schema-clean JSON — was excluded because it requires unfolding private
predicates from `WellFormedSampleJson.lean`. The five proved theorems give a complete
normalization story: `sampleNormalize` is idempotent, stable on encoded samples, and
maps well-formed inputs to the canonical encoded representative.

## Status: COMPLETE
