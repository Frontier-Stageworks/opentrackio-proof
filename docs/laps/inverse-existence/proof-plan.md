---
name: inverse-existence-proof-plan
description: Proof plan for D_exists_unique_preimage, including the validated scratch architecture
metadata:
  type: project
---

# Proof Plan — Local Existence and Uniqueness

## Validated scratch architecture (compiled before touching the real file)

```lean
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Contracting

open Set

example (f : ℂ → ℂ) (R Kreal : ℝ) (hR : 0 ≤ R) (hK0 : 0 ≤ Kreal) (hK1 : Kreal < 1)
    (hmaps : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ R)
    (hlip : ∀ a b : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R → ‖f a - f b‖ ≤ Kreal * ‖a - b‖)
    (y0 : ℂ) (hy0 : ‖y0‖ ≤ R) :
    ∃! z : ℂ, ‖z‖ ≤ R ∧ f z = z := by
  set s : Set ℂ := {z : ℂ | ‖z‖ ≤ R} with hs_def
  have hclosed : IsClosed s := by
    have : s = Metric.closedBall (0:ℂ) R := by
      ext z; simp [hs_def, Metric.mem_closedBall, dist_eq_norm]
    rw [this]; exact Metric.isClosed_closedBall
  have hcomplete : IsComplete s := hclosed.isComplete
  have hMapsTo : MapsTo f s s := fun z hz => hmaps z hz
  set K : NNReal := Kreal.toNNReal with hK_def
  have hKcoe : (K : ℝ) = Kreal := Real.coe_toNNReal Kreal hK0
  have hKlt1 : K < 1 := by
    rw [← NNReal.coe_lt_coe, hKcoe]; simpa using hK1
  have hLip : LipschitzWith K (hMapsTo.restrict f s s) := by
    apply LipschitzWith.of_dist_le_mul
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [MapsTo.restrict, Subtype.dist_eq]
    rw [hKcoe]
    have := hlip a b ha hb
    simpa [dist_eq_norm] using this
  have hContract : ContractingWith K (hMapsTo.restrict f s s) := ⟨hKlt1, hLip⟩
  have hxs : y0 ∈ s := hy0
  have hedist : edist y0 (f y0) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨z, hzs, hfz, _, _⟩ := hContract.exists_fixedPoint' hcomplete hMapsTo hxs hedist
  refine ⟨z, ⟨hzs, hfz⟩, ?_⟩
  rintro w ⟨hws, hfw⟩
  have hzs' : (⟨z, hzs⟩ : s) = (⟨w, hws⟩ : s) := by
    apply hContract.fixedPoint_unique' (x := (⟨z, hzs⟩ : s)) (y := (⟨w, hws⟩ : s))
    · show (hMapsTo.restrict f s s) ⟨z, hzs⟩ = ⟨z, hzs⟩
      exact Subtype.ext hfz
    · show (hMapsTo.restrict f s s) ⟨w, hws⟩ = ⟨w, hws⟩
      exact Subtype.ext hfw
  exact (congrArg Subtype.val hzs').symm
```

Compiled clean on the second attempt (one direction-mismatch fix: the final
line originally read `congrArg Subtype.val hzs'` — type `z = w` — but the
goal (from `∃!`'s uniqueness clause, `w = z`) wanted the symmetric form;
added `.symm`). No other issues.

## Adapting to the real theorem

Substitute: `f := inverseStep θ t y`, `Kreal := |t| * L θ R`, `hmaps :=
inverse_step_maps_disk θ R t hR y · hy ·` (per-point application),
`hlip := inverse_step_lipschitz θ R t hR y`, `y0 := ` **the point whose
existence we're proving a preimage for is `y` itself as the target, not the
seed of the iteration** — re-examine this carefully (see "Seed point"
below), and translate the conclusion `∃! z, ‖z‖≤R ∧ f z = z` (fixed point
of `inverseStep θ t y`) into `∃! z, ‖z‖≤R ∧ D θ t z = y` via:

```lean
have hiff : ∀ z : ℂ, inverseStep θ t y z = z ↔ D θ t z = y := by
  intro z
  unfold inverseStep D
  constructor <;> intro h <;> simp only [Complex.real_smul] at h ⊢ <;> linear_combination h
```

(or equivalent — exact tactic confirmed at Stop 3; this is simple ring-level
algebra, same style as `D_eq_implies_eq`'s `heq` derivation, low risk.)

## Seed point for the iteration

The scratch test's `y0` (with `‖y0‖ ≤ R`) is the STARTING point for the
Picard iteration `f^[n] y0`, not the target `y` in `D θ t z = y`. In the
real theorem, `y` (the hypothesis `hy : ‖y‖ + |t|*M θ R ≤ R`, in particular
`‖y‖ ≤ R`) is a natural, always-available seed: it is already known to be
in the disk, and no other canonical point is more obviously available.
**Plan: use `y0 := y`** (the target itself, which is a perfectly legal seed
for `exists_fixedPoint'` — the iteration seed does not need to be the fixed
point, or anywhere near it, just a starting point in the complete set `s`
with `edist y0 (f y0) ≠ ⊤`, which is automatic since `ℂ` has finite
distances everywhere — `edist_ne_top` applies unconditionally). This
requires `‖y‖ ≤ R`, which follows from `hy` (`‖y‖ + |t|*M θ R ≤ R` and
`|t|*M θ R ≥ 0`) exactly as in `inverse_approx_error`/`D_eq_implies_eq`'s
existing derivations of `‖x‖ ≤ R` from the buffer hypothesis.

## Goal shape / opening move for `D_exists_unique_preimage`

1. `have hyR : ‖y‖ ≤ R` from `hy` (same pattern as prior theorems: `M θ R ≥
   0` via `positivity`, then `linarith`).
2. Set `s := {z : ℂ | ‖z‖ ≤ R}`, establish `IsClosed s` /`IsComplete s` via
   the closed-ball identification (scratch-validated).
3. `MapsTo (inverseStep θ t y) s s` directly from `inverse_step_maps_disk`
   (needs `hy` as given, not just `hyR` — matches the theorem's own
   hypothesis exactly, no adaptation needed).
4. `K := (|t| * L θ R).toNNReal`, `ContractingWith K (restriction)` built
   from `inverse_step_lipschitz` via `LipschitzWith.of_dist_le_mul` +
   `Subtype.dist_eq`, exactly as scratch-tested.
5. `exists_fixedPoint'` with seed `y`, giving `z`, `hzs : z ∈ s`, `hfz :
   inverseStep θ t y z = z`.
6. Translate `hfz` to `D θ t z = y` via the `hiff` lemma above.
7. Uniqueness via `ContractingWith.fixedPoint_unique'` on the subtype,
   translating any other `w` satisfying `‖w‖≤R ∧ D θ t w = y` back through
   `hiff` to `inverseStep θ t y w = w` first.

## Automation budget

This is architecture-integration work, not algebra — no `nlinarith`/`ring`
budget concerns anticipated beyond the one `hiff` lemma (trivial) and the
`‖y‖≤R` derivation (already-proven pattern, copy from `D_eq_implies_eq`).
The hard-step risk is entirely in Mathlib API shape-matching, already
de-risked by the passing scratch test above.

## Time-box tracking

Scratch validation: 2 attempts total (1 failure: direction mismatch, fixed
immediately). Well within the user's 2-3-iteration budget, with margin
remaining for the real-file integration in case something about the exact
`Coeffs`/`θ`-parametrized definitions (vs. the scratch's generic `f`)
introduces friction the generic test didn't surface (e.g. `unfold
inverseStep` interacting with `Φ`'s own definition inside `hlip`'s
application). If new friction appears during integration, the 2-3-iteration
budget applies fresh to that specific new sticking point, per the user's
instruction ("2-3 iterations of a single sticking point").
