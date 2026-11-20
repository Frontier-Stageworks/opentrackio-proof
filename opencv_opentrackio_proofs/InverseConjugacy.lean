/-
  InverseConjugacy.lean

  A standalone, model-independent fact about conjugating partial inverses
  under a bijective coordinate change. No import from opencv_opentrackio_proofs/
  or openlensio_semantics/ — pure Mathlib function/set theory, deliberately
  independent of any distortion-specific definition. Specialized to the
  actual OpenCV/OpenTrackIO forward maps in
  opencv_opentrackio_proofs/Pipeline/InverseConjugacyApplication.lean.

  Scope discipline (read before citing): this file proves a conjugacy-of-
  inverses IDENTITY — if g and f are related by `∀x, g (S x) = S (f x)` for a
  bijection S, and f' is a genuine two-sided inverse of f on explicit domain/
  range sets A, B (not assumed globally), then `S ∘ f' ∘ S.symm` is the
  correspondingly-conjugated two-sided inverse of g on `S '' A`, `S '' B`.
  It does NOT construct f' — existence of a genuine inverse of f on any
  particular set is a hypothesis here, supplied by the caller. It does NOT
  use `Function.invFun` (which would require separately tracking its
  unconstrained behavior outside f's range) — `Set.InvOn` already states
  the inverse relationship only where it is actually claimed to hold, with
  no junk-value ambiguity to track.
-/

import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Function

/-─────────────────────────────────────────────────────────────────────────────
  conjugate_invOn

  If `g (S x) = S (f x)` for all `x` (i.e. `g ∘ S = S ∘ f` pointwise, the
  pointwise form of `g = S ∘ f ∘ S.symm` since `S` is a bijection), and `f'`
  is a genuine two-sided inverse of `f` relating domain `A` to range `B`
  (`Set.InvOn f' f A B`: `f'(f a) = a` for `a ∈ A`, and `f(f' b) = b` for
  `b ∈ B` — NOT a claim that `f` is globally bijective), then
  `S ∘ f' ∘ S.symm` is the correspondingly-conjugated two-sided inverse of
  `g`, relating the `S`-transported sets `S '' A` and `S '' B`.

  This is the general identity instantiated by
  `Pipeline/InverseConjugacyApplication.lean` to relate an inverse of
  OpenCV's forward distortion map to an inverse of OpenTrackIO's — it does
  not, by itself, assert that either map actually has an inverse anywhere.
─────────────────────────────────────────────────────────────────────────────-/

theorem conjugate_invOn {α β : Type*} (S : α ≃ β) (f f' : α → α) (g : β → β)
    (A B : Set α)
    (hconj : ∀ x : α, g (S x) = S (f x))
    (hf' : Set.InvOn f' f A B) :
    Set.InvOn (S ∘ f' ∘ S.symm) g (S '' A) (S '' B) := by
  constructor
  · -- LeftInvOn (S∘f'∘S.symm) g (S '' A) : ∀ y ∈ S '' A, (S∘f'∘S.symm) (g y) = y
    rintro y ⟨a, haA, rfl⟩
    simp only [Function.comp_apply]
    rw [hconj a, Equiv.symm_apply_apply, hf'.1 haA]
  · -- RightInvOn (S∘f'∘S.symm) g (S '' B), i.e. LeftInvOn g (S∘f'∘S.symm) (S '' B):
    -- ∀ y ∈ S '' B, g ((S∘f'∘S.symm) y) = y
    rintro y ⟨b, hbB, rfl⟩
    simp only [Function.comp_apply]
    rw [Equiv.symm_apply_apply, hconj (f' b), hf'.2 hbB]
