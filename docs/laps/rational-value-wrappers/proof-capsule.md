# Proof Capsule — rational-value-wrappers

## Parent

Slice 1 of `opentrack-parser-verification`.  
Contract: [first-slice-contract.md](../opentrack-parser-verification/first-slice-contract.md)

## Task classification

**Small** — 3 structure definitions, 3 evaluation functions, 11 theorems.  
All proofs are direct consequences of constructor invariants; no Mathlib search required.

## Intent

Define three invariant-carrying rational wrapper types for use by downstream
decoder slices. The invariants (denominator nonzero, numerator positive) are
encoded in the type constructor so that any value of the type is valid by
construction.

## Formal statements (frozen)

```lean
-- Structures
structure RationalWithPositiveDenominator where
  num : Int;  den : Nat;  den_pos : 0 < den

structure NonnegativeRational where
  num : Nat;  den : Nat;  den_pos : 0 < den

structure PositiveRational where
  num : Nat;  den : Nat;  num_pos : 0 < num;  den_pos : 0 < den

-- Evaluation
def RationalWithPositiveDenominator.toReal (r : ...) : ℝ := (r.num : ℝ) / (r.den : ℝ)
def NonnegativeRational.toReal             (r : ...) : ℝ := (r.num : ℝ) / (r.den : ℝ)
def PositiveRational.toReal                (r : ...) : ℝ := (r.num : ℝ) / (r.den : ℝ)

-- ℕ-level denominator nonzero
theorem rational_with_positive_denominator_den_nat_ne_zero (r : ...) : r.den ≠ 0
theorem nonnegative_rational_den_nat_ne_zero               (r : ...) : r.den ≠ 0
theorem positive_rational_den_nat_ne_zero                  (r : ...) : r.den ≠ 0

-- ℝ-level denominator nonzero
theorem rational_with_positive_denominator_den_ne_zero (r : ...) : (r.den : ℝ) ≠ 0
theorem nonnegative_rational_den_ne_zero               (r : ...) : (r.den : ℝ) ≠ 0
theorem positive_rational_den_ne_zero                  (r : ...) : (r.den : ℝ) ≠ 0

-- ℝ-level numerator nonzero (PositiveRational only — num is signed in RWPD)
theorem positive_rational_num_ne_zero (r : PositiveRational) : (r.num : ℝ) ≠ 0

-- Value semantics
theorem positive_rational_toReal_pos         (r : PositiveRational)  : 0 < r.toReal
theorem nonnegative_rational_toReal_nonneg   (r : NonnegativeRational) : 0 ≤ r.toReal
```

## Allowed changes

- Internal proof terms (tactics) may be changed freely.

## Forbidden changes

- Theorem statements, structure field types, and definition return types are frozen.
- No JSON, decoder, or protocol record definitions in this file.
- No value-level positivity theorem for `RationalWithPositiveDenominator` (`num : Int` is signed).
