# Proof Plan — numeric-literal-roundtrip (Slice 15.6A)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/NumericLiteralRoundtrip.lean` | `NumericLiteralRoundtrip` |

Appended after `PtpInfoEncoder` in `lakefile.toml`.

---

## Imports

```lean
import Mathlib
import DecodeError
import JsonRawModel
import RationalDecoder
```

---

## Verified lemma chain (all checked via `lake env lean --stdin`)

### Bridge 1 — `Slice.foldl` to `List.foldl`

```lean
-- VERIFIED: closes by simp
private lemma slice_foldl_ofList {α : Type*} (cs : List Char) (f : α → Char → α) (init : α) :
    String.Slice.foldl f init (String.ofList cs).toSlice = List.foldl f init cs := by
  simp only [String.Slice.foldl, ← Std.Iter.foldl_toList,
             String.Slice.toList_chars, String.copy_toSlice,
             String.toList_ofList]
```

Key lemmas used:
- `String.Slice.foldl` unfolds to `Std.Iter.fold f init s.chars`
- `Std.Iter.foldl_toList` (simp): `it.toList.foldl f init = it.fold f init`
- `String.Slice.toList_chars`: `s.chars.toList = s.copy.toList`
- `String.copy_toSlice`: `s.toSlice.copy = s`
- `String.toList_ofList`: `(String.ofList cs).toList = cs`

---

## Private helper lemmas

### H1 — `digitChar_toNat_inv`

```lean
private lemma digitChar_toNat_inv (d : Nat) (h : d < 10) :
    (Nat.digitChar d).toNat - '0'.toNat = d := by
  simp [Nat.digitChar]; interval_cases d <;> decide
```

### H2 — `digitChar_isDigit`

```lean
private lemma digitChar_isDigit (d : Nat) (h : d < 10) :
    (Nat.digitChar d).isDigit = true := by
  simp [Nat.digitChar]; interval_cases d <;> decide
```

### H3 — `toDigitsCore_eq`

The key structural lemma: `Nat.toDigitsCore 10 fuel n acc = Nat.toDigits 10 n ++ acc`
when `n < fuel`. This lets all later lemmas work purely on `Nat.toDigits 10 n`.

```lean
private lemma toDigitsCore_eq (fuel n : Nat) (acc : List Char) (hfuel : n < fuel) :
    Nat.toDigitsCore 10 fuel n acc = Nat.toDigits 10 n ++ acc := by
  induction fuel generalizing n acc with
  | zero => omega
  | succ f ih =>
    simp only [Nat.toDigits, Nat.toDigitsCore]
    split
    · -- n / 10 = 0: result is [(n % 10).digitChar] ++ acc
      simp [List.append]
    · -- n / 10 ≠ 0: recurse
      rename_i hne
      have hpos : 0 < n := by omega
      have hlt : n / 10 < f :=
        Nat.lt_of_lt_of_le (Nat.div_lt_self hpos (by omega)) (by omega)
      rw [ih (n / 10) ((n % 10).digitChar :: acc) hlt]
      rw [ih (n / 10) [] (Nat.lt_of_lt_of_le hlt (le_refl _))]
      simp [List.append_assoc]
```

Note: the `split` may need `rename_i` to name the `n / 10 = 0` hypothesis. If the
recursion unfolds differently, diagnose the exact `toDigitsCore` case structure and
adjust accordingly.

### H4 — `toDigits_ne_nil`

```lean
private lemma toDigits_ne_nil (n : Nat) : Nat.toDigits 10 n ≠ [] := by
  simp only [Nat.toDigits, Nat.toDigitsCore]
  split <;> simp
```

If `split` doesn't close, use `cases n` and handle `n = 0` by `decide`.

### H5 — `toDigits_all_isDigit`

```lean
private lemma toDigits_all_isDigit (n : Nat) :
    ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true := by
  intro c hc
  rw [show Nat.toDigits 10 n = Nat.toDigitsCore 10 (n + 1) n [] from rfl] at hc
  -- induction via toDigitsCore_eq will expose (n % 10).digitChar ∈ result
  -- use digitChar_isDigit (Nat.mod_lt n (by omega))
  sorry -- placeholder; fill during execution
```

Implementation path: use `toDigitsCore_eq` and `digitChar_isDigit`. All chars in
`Nat.toDigits 10 n` come from `(n' % 10).digitChar` for various `n'`, each `< 10`.

### H6 — `foldl_toDigits`

The core arithmetic lemma: the parser fold over `Nat.toDigits 10 n` returns `n`.

```lean
private lemma foldl_toDigits (n : Nat) :
    List.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
               (Nat.toDigits 10 n) = n := by
  induction n using Nat.strong_rec_on with
  | _ n ih => ...
```

Proof steps:
- Case `n < 10`: `Nat.toDigits 10 n = [(Nat.digitChar n)]` (from `toDigitsCore_eq` + split).
  `foldl f 0 [c] = 0 * 10 + (c.toNat - '0'.toNat) = n` by `digitChar_toNat_inv`.
  Close with `simp; interval_cases n <;> decide` or `omega`.
- Case `n ≥ 10` (i.e., `n / 10 ≠ 0`): use `toDigitsCore_eq` to get
  `Nat.toDigits 10 n = Nat.toDigits 10 (n / 10) ++ [(n % 10).digitChar]`.
  Then `foldl f 0 (digits(n/10) ++ [last]) = foldl f (foldl f 0 digits(n/10)) [last]`.
  By IH: `foldl f 0 digits(n/10) = n / 10`.
  Then `n/10 * 10 + (n % 10).digitChar.toNat - '0'.toNat = n/10 * 10 + n % 10 = n`.

### H7 — `isNat_ofDigitList`

```lean
private lemma isNat_ofDigitList (cs : List Char)
    (hne : cs ≠ [])
    (hall : ∀ c ∈ cs, c.isDigit = true) :
    (String.ofList cs).toSlice.isNat = true := by
  simp only [String.Slice.isNat]
  -- isEmpty: String.ofList cs is nonempty since cs ≠ []
  -- then use slice_foldl_ofList to reduce the state-machine foldl to List.foldl
  -- then induction on cs (nonempty, all-digit): state machine always ends in valid=true, lastWasDigit=true
  sorry -- fill during execution
```

This is the second hard helper. The `String.Slice.isNat` definition unfolds to an
`if isEmpty then false else foldl (state machine)`. After applying `slice_foldl_ofList`,
the goal is a List.foldl of the state machine over `cs`. Prove by list induction using
`hall` and `hne`.

---

## Main theorem

```lean
theorem nat_repr_toNat?_some (n : Nat) :
    n.repr.toNat? = some n := by
  simp only [Nat.repr, String.toNat?, String.Slice.toNat?]
  -- Goal shape:
  -- if (String.ofList (Nat.toDigits 10 n)).toSlice.isNat = true then
  --   some (String.Slice.foldl parser 0 ...)
  -- else none  = some n
  rw [isNat_ofDigitList (Nat.toDigits 10 n) (toDigits_ne_nil n) (toDigits_all_isDigit n)]
  simp only [ite_true]
  rw [slice_foldl_ofList]
  exact foldl_toDigits n
```

---

## Stop rules during execution

1. If `toDigitsCore_eq` induction fails, stop and report the exact `toDigitsCore` unfolded goal.
2. If `isNat_ofDigitList` expands into the `isEmpty` or `String.Slice` internals in an unexpected way, stop and report.
3. If the main theorem's `simp only` produces a goal different from the expected shape, stop before any `rw`.

## Acceptance criteria

1. `lake env lean opentrackio_parser/NumericLiteralRoundtrip.lean` — exit 0, no warnings, no `sorry`.
2. `lake build NumericLiteralRoundtrip` — exit 0.
3. `nat_repr_toNat?_some` is a public theorem with no `sorry`.
