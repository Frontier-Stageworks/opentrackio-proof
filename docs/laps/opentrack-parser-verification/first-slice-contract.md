# First-Slice Contract

## Parent task

- Task slug: `opentrack-parser-verification`
- Work queue: [work-queue.md](work-queue.md)
- Selected slice: `rational-value-wrappers` (Slice 1 of 17)

## Slice objective

> Define three invariant-carrying rational value wrapper types whose
> constructors encode denominator-nonzero and positivity invariants,
> add optional real-valued evaluation functions, and prove the basic
> invariant lemmas that downstream decoders will use as hypotheses.

---

## Included work

- Define `RationalWithPositiveDenominator` with fields `num : Int`, `den : Nat`, `den_pos : den > 0`
- Define `NonnegativeRational` with fields `num : Nat`, `den : Nat`, `den_pos : den > 0`
- Define `PositiveRational` with fields `num : Nat`, `den : Nat`, `num_pos : num > 0`, `den_pos : den > 0`
- Optional: `RationalWithPositiveDenominator.toReal : RationalWithPositiveDenominator → ℝ`
- Optional: `NonnegativeRational.toReal : NonnegativeRational → ℝ`
- Optional: `PositiveRational.toReal : PositiveRational → ℝ`
- `theorem rational_with_positive_denominator_den_ne_zero`
- `theorem nonnegative_rational_den_ne_zero`
- `theorem positive_rational_den_ne_zero`
- `theorem positive_rational_num_ne_zero`
- `theorem positive_rational_toReal_pos` (if `toReal` is defined)
- `theorem nonnegative_rational_toReal_nonneg` (if `toReal` is defined)

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

-- Optional evaluation functions
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
theorem rational_with_positive_denominator_den_ne_zero
    (r : RationalWithPositiveDenominator) : (r.den : ℝ) ≠ 0

theorem nonnegative_rational_den_ne_zero
    (r : NonnegativeRational) : (r.den : ℝ) ≠ 0

theorem positive_rational_den_ne_zero
    (r : PositiveRational) : (r.den : ℝ) ≠ 0

theorem positive_rational_num_ne_zero
    (r : PositiveRational) : (r.num : ℝ) ≠ 0

theorem positive_rational_toReal_pos
    (r : PositiveRational) : 0 < r.toReal

theorem nonnegative_rational_toReal_nonneg
    (r : NonnegativeRational) : 0 ≤ r.toReal
```

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
- `omega`: primary tactic for `den > 0 → den ≠ 0` and similar nat arithmetic
- `norm_cast`: for coercions between `Nat → ℝ` and `Int → ℝ`
- `linarith` / `nlinarith`: allowed for `toReal_pos` (division positivity from nonzero parts)
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
3. `lake build` succeeds with the new file included.
4. No excluded definitions or theorems were introduced.
5. Proof review accepts the result (no vacuous hypotheses, no trivial-True conclusions).
6. `work-queue.md` marks Slice 1 as **COMPLETE**.
7. `statement-audit.md` Slice 1 section is updated with final theorem signatures.
