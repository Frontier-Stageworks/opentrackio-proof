# Statement Audit — OpenTrackIO Parser Verification

## Audit scope

This audit covers the top-level and mid-level theorem shapes for the full
parser verification plan. Each slice's local theorems are audited in their own
slice-level artifacts when that slice opens.

---

## Top-level theorems

### T1 — Decoder soundness (primary goal)

```lean
theorem decode_sample_sound :
  decodeSample j = Except.ok s →
  ValidSample s
```

**Parameters:** `j : JsonValue`, `s : Sample`  
**Hypotheses:** decoder acceptance  
**Conclusion:** semantic validity of accepted value  
**Status:** Not yet stated in Lean. Guarded by Slices 1–11.

---

### T2 — Decoder completeness (conditional, future)

```lean
theorem decode_sample_complete :
  JsonConformsToOpenTrackIO j →
  ∃ s, decodeSample j = Except.ok s
```

**Status:** Blocked on spec decisions about unknown fields, duplicate keys,
optional defaults, and enum spellings. Do not attempt before Slice 12.

---

## Local decoder soundness shapes (per slice)

Each slice must produce a theorem of one of these shapes before the next
higher-level decoder may use it.

### Shape A — Type-invariant decoder

```lean
theorem decode_X_sound :
  decodeX j = Except.ok x →
  ValidX x
```

Used when `ValidX` is a `Prop` that is not encodable in the type constructor.

### Shape B — Constructor-invariant decoder (preferred)

When invariants are carried in the type (e.g., `PositiveRational`), the
soundness theorem proves a semantic fact about the value:

```lean
theorem decode_positive_rational_returns_positive :
  decodePositiveRational j = Except.ok r →
  0 < r.toReal
```

This is strictly stronger than `True` and must be preferred over Shape A
when the invariant can be expressed.

### Shape C — Required-field error correctness

```lean
theorem lookup_required_missing :
  JsonValue.lookup? j key = none →
  requireField key j = Except.error (.missingField key)
```

---

## Intermediate record decoder soundness shapes

```lean
theorem decode_version_sound :
  decodeVersion j = Except.ok v → ValidVersion v

theorem decode_camera_sound :
  decodeCamera j = Except.ok c → ValidCamera c

theorem decode_lens_sound :
  decodeLens j = Except.ok l → ValidLens l

theorem decode_transform_sound :
  decodeTransform j = Except.ok t → ValidTransform t
```

---

## Roundtrip shapes (Slices 14–15)

```lean
theorem decode_encode_version_roundtrip :
  decodeVersion (encodeVersion v) = Except.ok v

theorem encode_decode_sample_roundtrip :
  ValidSample s →
  decodeSample (encodeSample s) = Except.ok s
```

---

## Audit findings — current risks

| Risk | Severity | Notes |
|---|---|---|
| `ValidSample` definition not yet stated | High | Blocks T1 |
| JSON field names not fixed in Lean | High | Blocks Slices 4–12 |
| Numeric representation not decided | High | Blocks Slice 5 (Rational Decoder) |
| Duplicate-key semantics undefined | Medium | Blocks `lookup?` full spec |
| Unknown-field policy undefined | Medium | Blocks completeness |
| Enum spellings not canonical | Medium | Blocks Slice 7 |
| Array exact lengths not confirmed | Medium | Blocks Slice 6 |
| Quaternion normalization requirement unclear | Low | Blocks Slice 8 |

All risks are recorded in full in `ambiguity-register.md`.

---

## Slice 1 statement audit (`rational-value-wrappers`)

The first slice must produce theorems of Shape B only. Candidate statements:

```lean
theorem rational_with_positive_denominator_den_ne_zero
    (r : RationalWithPositiveDenominator) : r.den ≠ 0

theorem nonnegative_rational_den_ne_zero
    (r : NonnegativeRational) : r.den ≠ 0

theorem positive_rational_den_ne_zero
    (r : PositiveRational) : r.den ≠ 0

theorem positive_rational_num_ne_zero
    (r : PositiveRational) : r.num ≠ 0

theorem positive_rational_toReal_pos
    (r : PositiveRational) : 0 < r.toReal
```

These are all purely structural — they follow immediately from the
constructor invariant fields (`den_pos`, `num_pos`) using `omega` or `norm_cast`.
No Mathlib lemma hunting required.

**Verdict:** Slice 1 statements are well-scoped and safe to proceed.

**Final signatures (as compiled, 2026-05-17):**

```lean
theorem rational_with_positive_denominator_den_nat_ne_zero (r : RationalWithPositiveDenominator) : r.den ≠ 0
theorem nonnegative_rational_den_nat_ne_zero               (r : NonnegativeRational)              : r.den ≠ 0
theorem positive_rational_den_nat_ne_zero                  (r : PositiveRational)                 : r.den ≠ 0
theorem rational_with_positive_denominator_den_ne_zero     (r : RationalWithPositiveDenominator)  : (r.den : ℝ) ≠ 0
theorem nonnegative_rational_den_ne_zero                   (r : NonnegativeRational)              : (r.den : ℝ) ≠ 0
theorem positive_rational_den_ne_zero                      (r : PositiveRational)                 : (r.den : ℝ) ≠ 0
theorem positive_rational_num_ne_zero                      (r : PositiveRational)                 : (r.num : ℝ) ≠ 0
theorem positive_rational_toReal_pos                       (r : PositiveRational)                 : 0 < r.toReal
theorem nonnegative_rational_toReal_nonneg                 (r : NonnegativeRational)              : 0 ≤ r.toReal
```

Note: `toReal` functions are `noncomputable` (standard for `ℝ` division).  
Source: `opentrackio_parser/RationalValueWrappers.lean`
