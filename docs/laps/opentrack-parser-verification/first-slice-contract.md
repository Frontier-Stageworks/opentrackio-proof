# First-Slice Contract

## Parent task

- Task slug: `opentrack-parser-verification`
- Work queue: [work-queue.md](work-queue.md)
- Selected slice: `rational-value-wrappers` (Slice 1 of 17)

## Slice objective

> Define three invariant-carrying rational value wrapper types whose
> constructors encode denominator-nonzero and positivity invariants,
> add real-valued evaluation functions, and prove the basic invariant
> lemmas (both ℕ-level and ℝ-level) that downstream decoders will use
> as hypotheses.

---

## Included work

- Define `RationalWithPositiveDenominator` with fields `num : Int`, `den : Nat`, `den_pos : den > 0`
- Define `NonnegativeRational` with fields `num : Nat`, `den : Nat`, `den_pos : den > 0`
- Define `PositiveRational` with fields `num : Nat`, `den : Nat`, `num_pos : num > 0`, `den_pos : den > 0`
- `RationalWithPositiveDenominator.toReal : RationalWithPositiveDenominator → ℝ`
- `NonnegativeRational.toReal : NonnegativeRational → ℝ`
- `PositiveRational.toReal : PositiveRational → ℝ`
- `theorem rational_with_positive_denominator_den_nat_ne_zero`  (ℕ-level)
- `theorem nonnegative_rational_den_nat_ne_zero`                (ℕ-level)
- `theorem positive_rational_den_nat_ne_zero`                   (ℕ-level)
- `theorem rational_with_positive_denominator_den_ne_zero`      (ℝ-level)
- `theorem nonnegative_rational_den_ne_zero`                    (ℝ-level)
- `theorem positive_rational_den_ne_zero`                       (ℝ-level)
- `theorem positive_rational_num_ne_zero`                       (ℝ-level)
- `theorem positive_rational_toReal_pos`
- `theorem nonnegative_rational_toReal_nonneg`

---

## Excluded work

These are intentionally deferred:

- JSON model of any kind
- Protocol records (Sample, Camera, Lens, Transform, Version)
- Any decoder (`decodeX`)
- OpenTrackIO schema
- Serialization or roundtrip
- Unknown-field policy
- Enum types
- Fixed-length array types
- Error vocabulary (`DecodeError`)
- Any theorem about acceptance or rejection of JSON input
- Any reference to camdkit Python or C++ implementations

---

## Allowed definitions

```lean
structure RationalWithPositiveDenominator where
  num : Int
  den : Nat
  den_pos : den > 0

structure NonnegativeRational where
  num : Nat
  den : Nat
  den_pos : den > 0

structure PositiveRational where
  num : Nat
  den : Nat
  num_pos : num > 0
  den_pos : den > 0

def RationalWithPositiveDenominator.toReal (r : RationalWithPositiveDenominator) : ℝ :=
  (r.num : ℝ) / (r.den : ℝ)

def NonnegativeRational.toReal (r : NonnegativeRational) : ℝ :=
  (r.num : ℝ) / (r.den : ℝ)

def PositiveRational.toReal (r : PositiveRational) : ℝ :=
  (r.num : ℝ) / (r.den : ℝ)
```

No other definitions are allowed in this slice.

---

## Allowed theorem shapes

```lean
-- ℕ-level denominator nonzero (used by coercion lemmas and omega-friendly contexts)
theorem rational_with_positive_denominator_den_nat_ne_zero
    (r : RationalWithPositiveDenominator) : r.den ≠ 0

theorem nonnegative_rational_den_nat_ne_zero
    (r : NonnegativeRational) : r.den ≠ 0

theorem positive_rational_den_nat_ne_zero
    (r : PositiveRational) : r.den ≠ 0

-- ℝ-level denominator and numerator nonzero (used by field_simp / div lemmas)
theorem rational_with_positive_denominator_den_ne_zero
    (r : RationalWithPositiveDenominator) : (r.den : ℝ) ≠ 0

theorem nonnegative_rational_den_ne_zero
    (r : NonnegativeRational) : (r.den : ℝ) ≠ 0

theorem positive_rational_den_ne_zero
    (r : PositiveRational) : (r.den : ℝ) ≠ 0

theorem positive_rational_num_ne_zero
    (r : PositiveRational) : (r.num : ℝ) ≠ 0

-- Value-level semantics
theorem positive_rational_toReal_pos
    (r : PositiveRational) : 0 < r.toReal

theorem nonnegative_rational_toReal_nonneg
    (r : NonnegativeRational) : 0 ≤ r.toReal
```

No value-level positivity or nonnegativity theorem for `RationalWithPositiveDenominator`:
its `num` is signed (`Int`), so no such fact holds in general.

Auxiliary `Nat.pos_iff_ne_zero`-style lemmas may be added inline if needed,
but not exported as named theorems unless they are reused by at least two
of the above.

---

## Existing definitions / theorems allowed

- All of Mathlib (imported via `import Mathlib.Tactic`)
- No imports from other files in this repo needed for Slice 1

---

## Forbidden scope

- `JsonValue` or any JSON type
- `DecodeError` or any error type
- `decodeSample`, `decodeCamera`, `decodeLens`, `decodeVersion`, or any decoder
- `ValidSample`, `ValidCamera`, `ValidLens`, `ValidVersion`, or any `ValidX` predicate
- `Sample`, `Camera`, `Lens`, `Transform`, `Version` struct definitions
- Roundtrip theorems
- Completeness theorems
- Any reference to OpenTrackIO JSON field names (string literals)
- Any reference to camdkit field names or key strings

---

## Ambiguities to resolve before implementation

| Ambiguity | Why it matters | Resolution |
|---|---|---|
| Invariants in types vs. `ValidX` predicates (A7) | Determines whether `PositiveRational` carries `num_pos` in the constructor or separately | **Resolved:** invariants in types. `num_pos` and `den_pos` are struct fields. |
| `toReal` vs. `toRat` | Determines whether evaluation maps to `ℝ` or `ℚ` | **Decision:** use `ℝ` to match the existing proof files. Both are acceptable; document choice. |

No unresolved ambiguities block this slice. All decisions are design decisions
that can be made without consulting the OpenTrackIO spec.

---

## Automation budget

- `simp`: allowed freely for unfolding struct projections and nat/int coercions
- `rw`: allowed for rewriting with specific lemmas
- `omega`: primary tactic for `den > 0 → den ≠ 0` and ℕ-level arithmetic
- `norm_cast`: for coercions between `Nat → ℝ` and `Int → ℝ`
- `exact_mod_cast`: preferred over `norm_cast` when the goal is a cast of a known fact
- `positivity`: for `toReal_pos` and `toReal_nonneg` (div of nonneg/pos parts)
- `linarith` / `nlinarith`: fallback for `toReal_pos` if `positivity` does not close the goal
- `ring` / `ring_nf`: not expected; allowed if useful
- `decide`: not expected for this slice
- No `native_decide`
- No custom tactics

---

## Stop conditions

Stop and record a blocker if:

- the slice expands to include any JSON, decoder, or protocol record work;
- a deferred slice (2–17) becomes necessary to complete a theorem here;
- a theorem statement requires changing the structure definitions in a way
  that would break downstream slices;
- the same proof goal fails twice under different tactic sequences;
- a Mathlib lemma for the required coercion cannot be found within two searches;
- a modeling ambiguity arises that is not covered by the resolved entries above.

---

## Completion conditions

This slice is complete only when:

1. All three structure definitions compile without `sorry`.
2. All listed theorems compile without `sorry`.
3. `lake env lean <new-file-path>` exits 0 with no errors or warnings on the new file.
4. `lake build` succeeds if the new file is wired into the package; otherwise step 3 is sufficient.
5. No excluded definitions or theorems were introduced.
6. Proof review accepts the result (no vacuous hypotheses, no trivial-True conclusions).
7. `work-queue.md` marks Slice 1 as **COMPLETE**.
8. `statement-audit.md` Slice 1 section is updated with final theorem signatures.
