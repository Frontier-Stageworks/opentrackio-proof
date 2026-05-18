/-
  NumericLiteralRoundtrip.lean — Slice 15.6A: numeric-literal-roundtrip

  Bridge theorem: n.repr.toNat? = some n
  Used by encodePositiveRational_roundtrip and every Nat field encoder.

  Ref: docs/laps/encode-decode-roundtrip/15.6A-numeric-literal-roundtrip/proof-capsule.md
-/

import Mathlib
import RationalDecoder

-- H1: recovering digit value from digitChar
private lemma digitChar_toNat_inv (d : Nat) (h : d < 10) :
    (Nat.digitChar d).toNat - '0'.toNat = d := by
  simp [Nat.digitChar]; interval_cases d <;> decide

-- H2: digitChar d is a decimal digit
private lemma digitChar_isDigit (d : Nat) (h : d < 10) :
    (Nat.digitChar d).isDigit = true := by
  simp [Nat.digitChar]; interval_cases d <;> decide

-- H2b: digitChar d is not an underscore
private lemma digitChar_ne_underscore (d : Nat) (h : d < 10) :
    Nat.digitChar d ≠ '_' := by
  simp [Nat.digitChar]; interval_cases d <;> decide

-- Bridge: String.Slice.foldl over (String.ofList cs).toSlice = List.foldl over cs
private lemma slice_foldl_ofList {α : Type*} (cs : List Char) (f : α → Char → α) (init : α) :
    String.Slice.foldl f init (String.ofList cs).toSlice = List.foldl f init cs := by
  simp only [String.Slice.foldl, ← Std.Iter.foldl_toList,
             String.Slice.toList_chars, String.copy_toSlice,
             String.toList_ofList]

-- H3: toDigitsCore 10 fuel n acc = toDigits 10 n ++ acc  (when n < fuel)
private lemma toDigitsCore_eq : ∀ (n fuel : Nat) (acc : List Char),
    n < fuel → Nat.toDigitsCore 10 fuel n acc = Nat.toDigits 10 n ++ acc := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro fuel acc hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      show (if n / 10 = 0 then (n % 10).digitChar :: acc
            else Nat.toDigitsCore 10 f (n / 10) ((n % 10).digitChar :: acc)) =
           Nat.toDigits 10 n ++ acc
      have hdig_n : Nat.toDigits 10 n =
          if n / 10 = 0 then [(n % 10).digitChar]
          else Nat.toDigitsCore 10 n (n / 10) [(n % 10).digitChar] := rfl
      split
      · rw [hdig_n]; simp [*]
      · rename_i hne
        have hpos : 0 < n := Nat.pos_of_div_pos (Nat.pos_of_ne_zero hne)
        have hlt : n / 10 < n := Nat.div_lt_self hpos (by omega)
        have hflt : n / 10 < f :=
          Nat.lt_of_lt_of_le hlt (Nat.lt_succ_iff.mp hfuel)
        rw [ih (n / 10) hlt f ((n % 10).digitChar :: acc) hflt]
        rw [hdig_n, if_neg hne, ih (n / 10) hlt n [(n % 10).digitChar] hlt]
        simp [List.append_assoc]

-- H4: toDigits 10 n is never empty
private lemma toDigits_ne_nil (n : Nat) : Nat.toDigits 10 n ≠ [] := by
  have h : Nat.toDigits 10 n =
      if n / 10 = 0 then [(n % 10).digitChar]
      else Nat.toDigitsCore 10 n (n / 10) [(n % 10).digitChar] := rfl
  rw [h]
  split
  · simp
  · rename_i hne
    have hpos : 0 < n := Nat.pos_of_div_pos (Nat.pos_of_ne_zero hne)
    have hlt : n / 10 < n := Nat.div_lt_self hpos (by omega)
    rw [toDigitsCore_eq (n / 10) n [(n % 10).digitChar] hlt]
    simp

-- H5: every char in toDigits 10 n is a decimal digit
private lemma toDigits_all_isDigit (n : Nat) :
    ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have h : Nat.toDigits 10 n =
        if n / 10 = 0 then [(n % 10).digitChar]
        else Nat.toDigitsCore 10 n (n / 10) [(n % 10).digitChar] := rfl
    rw [h]
    split
    · intro c hc; simp at hc; rw [hc]
      exact digitChar_isDigit _ (Nat.mod_lt _ (by omega))
    · rename_i hne
      have hpos : 0 < n := Nat.pos_of_div_pos (Nat.pos_of_ne_zero hne)
      have hlt : n / 10 < n := Nat.div_lt_self hpos (by omega)
      rw [toDigitsCore_eq (n / 10) n [(n % 10).digitChar] hlt]
      intro c hc
      simp at hc
      rcases hc with hc | rfl
      · exact ih (n / 10) hlt c hc
      · exact digitChar_isDigit _ (Nat.mod_lt _ (by omega))

-- H6: the parser foldl over toDigits 10 n recovers n
private lemma foldl_toDigits (n : Nat) :
    List.foldl (fun acc c => if c = '_' then acc else acc * 10 + (c.toNat - '0'.toNat)) 0
               (Nat.toDigits 10 n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have h : Nat.toDigits 10 n =
        if n / 10 = 0 then [(n % 10).digitChar]
        else Nat.toDigitsCore 10 n (n / 10) [(n % 10).digitChar] := rfl
    rw [h]
    split
    · -- BASE CASE: n / 10 = 0, so n < 10; enumerate n = 0..9
      rename_i h0
      have hn10 : n < 10 := by omega
      interval_cases n <;> simp [Nat.digitChar]
    · -- RECURSIVE CASE
      rename_i hne
      have hpos : 0 < n := Nat.pos_of_div_pos (Nat.pos_of_ne_zero hne)
      have hlt : n / 10 < n := Nat.div_lt_self hpos (by omega)
      rw [toDigitsCore_eq (n / 10) n [(n % 10).digitChar] hlt]
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (n / 10) hlt]
      -- use rw (not simp) so '0'.toNat stays unreduced for the next rw
      rw [if_neg (digitChar_ne_underscore _ (Nat.mod_lt _ (by omega)))]
      rw [digitChar_toNat_inv _ (Nat.mod_lt _ (by omega))]
      omega

-- For all-digit lists starting from (false, false, true, true), state is invariant
private lemma isNat_foldl_stable (l : List Char) (hl : ∀ c ∈ l, c.isDigit = true) :
    List.foldl
      (fun x c =>
        let isDigit := c.isDigit
        let isUnderscore := c = '_'
        (false, decide isUnderscore, isDigit,
         x.2.2.2 && (isDigit || decide isUnderscore) &&
         !(x.1 && decide isUnderscore) &&
         !(x.2.1 && decide isUnderscore)))
      (false, false, true, true) l = (false, false, true, true) := by
  induction l with
  | nil => simp
  | cons c t iht =>
    simp only [List.foldl_cons]
    have hcdig : c.isDigit = true := hl c List.mem_cons_self
    have hcund : ¬(c = '_') := fun h => by simp [h, Char.isDigit] at hcdig
    have hcdec : decide (c = '_') = false := decide_eq_false_iff_not.mpr hcund
    simp only [hcdig, hcdec,
               Bool.and_true, Bool.true_or, Bool.false_and, Bool.not_false]
    apply iht
    intro x hx; exact hl x (List.mem_cons.mpr (Or.inr hx))

-- H7: nonempty all-digit char list passes String.Slice.isNat
private lemma isNat_foldl_digit (cs : List Char) (hne : cs ≠ [])
    (hall : ∀ c ∈ cs, c.isDigit = true) :
    List.foldl
      (fun x c =>
        let isDigit := c.isDigit
        let isUnderscore := c = '_'
        (false, decide isUnderscore, isDigit,
         x.2.2.2 && (isDigit || decide isUnderscore) &&
         !(x.1 && decide isUnderscore) &&
         !(x.2.1 && decide isUnderscore)))
      (true, false, false, true) cs = (false, false, true, true) := by
  rcases List.exists_cons_of_ne_nil hne with ⟨c, t, rfl⟩
  simp only [List.foldl_cons]
  have hcdig : c.isDigit = true := hall c List.mem_cons_self
  have hcund : ¬(c = '_') := fun h => by simp [h, Char.isDigit] at hcdig
  have hcdec : decide (c = '_') = false := decide_eq_false_iff_not.mpr hcund
  -- First step: (true, false, false, true) → (false, false, true, true)
  simp only [hcdig, hcdec,
             Bool.and_true, Bool.true_or, Bool.false_and, Bool.not_false]
  -- Remaining tail: invariant holds
  apply isNat_foldl_stable
  intro x hx; exact hall x (List.mem_cons.mpr (Or.inr hx))

-- H8: nonempty all-digit char list passes String.Slice.isNat
private lemma isNat_ofDigitList (cs : List Char)
    (hne : cs ≠ [])
    (hall : ∀ c ∈ cs, c.isDigit = true) :
    (String.ofList cs).toSlice.isNat = true := by
  simp only [String.Slice.isNat]
  have hemp : (String.ofList cs).toSlice.isEmpty = false := by
    simp [String.Slice.isEmpty, hne]
  simp only [hemp, Bool.false_eq_true, ↓reduceIte]
  rw [slice_foldl_ofList]
  rw [isNat_foldl_digit cs hne hall]
  simp

-- Main theorem: decimal render/parse roundtrip
theorem nat_repr_toNat?_some (n : Nat) :
    n.repr.toNat? = some n := by
  simp only [Nat.repr, String.toNat?, String.Slice.toNat?]
  rw [isNat_ofDigitList _ (toDigits_ne_nil n) (toDigits_all_isDigit n)]
  simp only [ite_true]
  rw [slice_foldl_ofList]
  exact congr_arg some (foldl_toDigits n)
