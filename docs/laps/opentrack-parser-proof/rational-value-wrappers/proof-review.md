# Proof Review — rational-value-wrappers

## Kernel status

`lake env lean opentrackio_parser/RationalValueWrappers.lean` — exit 0, no warnings.  
`lake build RationalValueWrappers` — exit 0, build complete (3286 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, or `partial`.
- No JSON, decoder, or protocol record definitions.
- No value-level positivity theorem for `RationalWithPositiveDenominator`.

## Noncomputable annotation

`toReal` functions are marked `noncomputable` because `ℝ` division depends on
`Real.instDivInvMonoid`, which is noncomputable. This is standard Lean 4 / Mathlib
behavior and does not affect proof correctness. The annotation was not in the
original contract template but is a necessary mechanical requirement; it does
not change the semantics of any definition or theorem.

## Statement audit

All 11 theorem statements match the first-slice-contract.md exactly.  
No theorem statement was changed during implementation.

## Semantic review

| Theorem | Intent | Captured? |
|---|---|---|
| `*_den_nat_ne_zero` | `den > 0` in ℕ implies `den ≠ 0` in ℕ | Yes — `omega` from `den_pos` |
| `*_den_ne_zero` | ℕ nonzero lifts to ℝ nonzero | Yes — `exact_mod_cast` + ℕ theorem |
| `positive_rational_num_ne_zero` | `num > 0` implies `(num : ℝ) ≠ 0` | Yes — `omega` then `exact_mod_cast` |
| `positive_rational_toReal_pos` | `num > 0`, `den > 0` implies `num/den > 0` in ℝ | Yes — `div_pos` + casts |
| `nonnegative_rational_toReal_nonneg` | `num, den : Nat` implies `num/den ≥ 0` in ℝ | Yes — `positivity` from Nat casts |

## Hard step identification

No theorem in this slice required a hard proof step. All proofs follow directly
from constructor invariants via:
- `omega` for ℕ arithmetic
- `exact_mod_cast` for ℕ → ℝ cast
- `div_pos` for ordered field positivity
- `positivity` for Nat-cast nonnegativity

The automation is bounded: no tactic closes a goal whose meaning is unclear.

## Hypothesis necessity

All theorems are parameter-only (no hypotheses beyond the struct value itself).
The invariants (`den_pos`, `num_pos`) are struct fields, not external hypotheses,
so vacuity is not possible: Lean enforces the invariants at construction time.

## Anti-pattern scan

- No broad `simp` without lemma list (all uses are `simp only [...]`).
- No `norm_cast` without a known cast goal.
- No `positivity` on a goal where intent is unclear.
- No proxy property proved instead of intended property.
- No global `@[simp]` or `@[grind]` annotations added.

## Excluded scope

- No JSON, decoder, or protocol record was introduced.
- No value-level theorem for `RationalWithPositiveDenominator` (signed `num`).

## Contract compliance

All completion conditions from first-slice-contract.md are met:

1. ✅ All three structures compile without `sorry`.
2. ✅ All 11 theorems compile without `sorry`.
3. ✅ `lake env lean opentrackio_parser/RationalValueWrappers.lean` exits 0.
4. ✅ `lake build RationalValueWrappers` succeeds (file is wired into package).
5. ✅ No excluded definitions or theorems introduced.
6. ✅ Proof review complete (this document).
7. ⬜ `work-queue.md` to be updated (next step).
8. ⬜ `statement-audit.md` Slice 1 section to be updated (next step).
