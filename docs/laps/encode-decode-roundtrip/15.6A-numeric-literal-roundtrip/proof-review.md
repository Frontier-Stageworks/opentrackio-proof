# Proof Review — numeric-literal-roundtrip (Slice 15.6A)

## Acceptance checks

| Check | Result |
|---|---|
| `lake env lean opentrackio_parser/NumericLiteralRoundtrip.lean` | exit 0, no warnings |
| `lake build NumericLiteralRoundtrip` | exit 0 |
| `nat_repr_toNat?_some` is public, no `sorry` | ✓ |

## Deviations from proof plan

### H3 — `toDigitsCore_eq` induction strategy

Plan used induction on `fuel`. Implementation uses **strong induction on `n`** to avoid
fuel-irrelevance issues where two calls to `toDigitsCore` with different fuel values appear
in the same goal. The `rfl` unfolding fact for both `toDigitsCore` and `toDigits` is used
via `show` to expose the if-then-else structure directly.

### H6 — `foldl_toDigits` base case

Plan sketched `simp`+`omega`. Implementation uses `interval_cases n <;> simp [Nat.digitChar]`
after establishing `n < 10` via `omega` from `h0 : n / 10 = 0`. This is cleaner and more
robust than the arithmetic route.

### H6 — `foldl_toDigits` recursive case

`simp [digitChar_ne_underscore ...]` would reduce `'0'.toNat` to 48, blocking the
subsequent `rw [digitChar_toNat_inv ...]`. Fix: use `rw [if_neg ...]` (not simp) to
eliminate the underscore guard while keeping `'0'.toNat` in unreduced form. Then
`rw [digitChar_toNat_inv ...]` applies cleanly and `omega` closes `n/10 * 10 + n%10 = n`.

### H7 — `isNat_foldl_digit` strategy

Plan used `isNat_step` as a rewrite lemma. After `simp only [List.foldl_cons]`, Lean
beta/let-reduces the lambda, so the `rw [isNat_step ...]` pattern (with `let` bindings)
no longer matches the goal. Fix: split into two lemmas:
- `isNat_foldl_stable` — invariance of `(false, false, true, true)` for all-digit lists
  (proved by induction with `simp only` using concrete Bool lemmas)
- `isNat_foldl_digit` — calls `isNat_foldl_stable` after handling the first char
  (which transitions from the `isFirst=true` initial state)

`isNat_step` was removed as unused.

## Final lemma chain

```
digitChar_toNat_inv     H1: (Nat.digitChar d).toNat - '0'.toNat = d
digitChar_isDigit       H2: (Nat.digitChar d).isDigit = true
digitChar_ne_underscore H2b: Nat.digitChar d ≠ '_'
slice_foldl_ofList      Bridge: Slice.foldl ↔ List.foldl
toDigitsCore_eq         H3: toDigitsCore 10 fuel n acc = toDigits 10 n ++ acc
toDigits_ne_nil         H4: toDigits 10 n ≠ []
toDigits_all_isDigit    H5: all chars in toDigits 10 n are decimal digits
foldl_toDigits          H6: List.foldl parser 0 (toDigits 10 n) = n
isNat_foldl_stable      aux: invariant for (false, false, true, true) + digit list
isNat_foldl_digit       H7: nonempty digit list passes the isNat state machine
isNat_ofDigitList       H8: (String.ofList digit_list).toSlice.isNat = true
nat_repr_toNat?_some    Main: n.repr.toNat? = some n
```

## Status: COMPLETE
