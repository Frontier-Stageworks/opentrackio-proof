# Proof Plan — rational-value-wrappers

## Goal shape

11 small theorems, all of the form: struct invariant → derived property.  
No induction, no case splits, no algebra beyond division-positivity.

## Proof strategy per group

### ℕ-level denominator nonzero (3 theorems)

Opening move: `have h := r.den_pos` (brings `0 < r.den` into context), then `omega`.

Hard step: none — `omega` closes `0 < n → n ≠ 0` immediately.

### ℝ-level denominator nonzero (3 theorems)

Opening move: delegate to the corresponding ℕ-level theorem, then `exact_mod_cast`.

Hard step: none — `norm_cast` framework handles `(n : ℝ) ≠ 0 ↔ n ≠ 0` for `n : ℕ`.

### ℝ-level numerator nonzero (1 theorem, PositiveRational only)

Opening move: `have h : r.num ≠ 0 := by have := r.num_pos; omega`, then `exact_mod_cast h`.

Hard step: none.

### Value-level positivity (2 theorems)

`positive_rational_toReal_pos`:
- Unfold with `simp only [PositiveRational.toReal]`.
- Apply `div_pos`.
- Close each branch with `exact_mod_cast r.num_pos` / `exact_mod_cast r.den_pos`.
- Hard step: none — `div_pos` + cast.

`nonnegative_rational_toReal_nonneg`:
- Unfold with `simp only [NonnegativeRational.toReal]`.
- Try `positivity` (Nat casts are nonneg, `div_nonneg` is in the `positivity` extension).
- Fallback if `positivity` fails: `apply div_nonneg; exact_mod_cast Nat.zero_le _; exact_mod_cast Nat.zero_le _`.

## Automation budget

| Goal | Primary tactic | Fallback |
|---|---|---|
| `r.den ≠ 0` (ℕ) | `omega` (with `have h := r.den_pos`) | — |
| `(r.den : ℝ) ≠ 0` | `exact_mod_cast` | `norm_cast` |
| `0 < r.toReal` | `div_pos` + `exact_mod_cast` | — |
| `0 ≤ r.toReal` | `positivity` | `div_nonneg` + `exact_mod_cast` |

## Definitions to unfold

- `PositiveRational.toReal` (via `simp only`)
- `NonnegativeRational.toReal` (via `simp only`)

## Theorems used from Mathlib

- `div_pos : 0 < a → 0 < b → 0 < a / b`
- `div_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a / b` (fallback)
- `Nat.cast_nonneg`, `Nat.cast_pos` (via `exact_mod_cast`)
- `positivity` extension for `Nat.cast` and division

## Helper lemmas

None exported. The ℕ-level `_nat_ne_zero` theorems serve as the bridge
to the ℝ-level theorems and are reused by all three ℝ-level denominator theorems.

## Stop conditions (from contract)

Stop if any theorem requires a Mathlib lemma that cannot be found within
two searches, or if `positivity` fails and `div_nonneg` also fails.
