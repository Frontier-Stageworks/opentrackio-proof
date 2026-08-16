---
name: bounded-inverse-approximation-capsule
description: Proof capsule for a bounded-error first-order approximate inverse of the polynomial (non-rational) Brown-Conrady displacement field, on a bounded disk
metadata:
  type: project
---

# Proof Capsule — Bounded Inverse Approximation (Layers 1–3)

## Intent (plain English)

`docs/specification-questions.md` SQ-CV-07 (and `docs/limitations.md`) raise
an open question about whether OpenTrackIO's native undistortion (D→U,
distorted input, undistorted output) is correctly reproduced by consuming
converted OpenCV coefficients — a question this repository's existing
pipeline theorems (`opencv_openlensio_full_pipeline_pixel_iff`/`_corrected`)
explicitly do NOT answer, since those are same-direction (U→D) conjugacy
results. Answering the D→U question properly requires knowing something
about the actual *inverse* of the Brown-Conrady distortion map — which has
no closed form in general (per `docs/limitations.md` SQ-OL-03,
`radialDescale_left_inverse_zero_tangential`).

This task is **layers 1–3 only** of a larger plan (discussed with the user
outside this session) to build toward a bounded-error statement about an
*approximate* inverse, without invoking existence/uniqueness machinery:

1. Define the pure polynomial (non-rational) Brown-Conrady displacement
   field `Φ_θ`, and a scaled distortion map `D_t(x) = x + t·Φ_θ(x)`.
2. Prove boundedness (`‖Φ_θ(x)‖ ≤ M`) and Lipschitz (`‖Φ_θ(a)-Φ_θ(b)‖ ≤
   L·‖a-b‖`) estimates on a bounded disk, with `M`, `L` explicit closed-form
   expressions in the coefficients and the disk radius `R`.
3. Define the first-order approximate inverse `U_t(y) = y - t·Φ_θ(y)` and
   prove `‖U_t(D_t(x)) - x‖ ≤ L·M·t²` — a direct algebraic estimate, not a
   fixed-point/contraction argument.

**Explicitly out of scope** (deferred to separate, larger follow-on tasks,
per the user's instruction):

- Layer 4: existence/uniqueness of the *true* inverse of `D_t` via a
  fixed-point/contraction argument (would use Mathlib's
  `ContractingWith`/Banach fixed-point machinery — none of that is used here).
- Layer 5: folding the `F`/mm/pixel unit-conversion machinery from
  `opencv_opentrackio_proofs/` back into this generic estimate.
- Anything under `Pipeline/` or `DistortionConversion*.lean` — this task
  touches neither; it produces exactly one new theorem file in a new,
  independent top-level directory.
- The D-U/U-D schema question itself (SQ-CV-07) is **not resolved** by this
  task — this is scaffolding toward a possible future resolution, not the
  resolution itself. The doc updates in this task say so explicitly.

## Why Lean here (informal verification-fit note)

This is an abstract mathematical estimate, not source-code validation, so
the formal `VERIFICATION FIT CHECK` block is optional per LAPS and omitted.
Informally: this is exactly the kind of estimate SQ-CV-07 says is needed
("a bounded-error approximation theorem") to make any future progress on the
D-U/U-D question rigorous rather than hand-wavy; a hand-proof of a Lipschitz
composition-error bound is easy to get subtly wrong (sign errors, forgetting
that the disk needs a buffer margin — both of which this session's own
planning caught, see `ambiguity-register.md`), which is precisely the kind
of error Lean's kernel check rules out.

## Lean grounding

- Lean 4 `v4.29.0`, Mathlib `v4.29.0` (unchanged toolchain, same as rest of repo)
- New top-level directory: `inverse_approximation/` (sibling to
  `opencv_opentrackio_proofs/`, `openlensio_semantics/`, `opentrackio_parser/`)
- New file: `inverse_approximation/InverseApproximation.lean`
- New `[[lean_lib]]` entry in `lakefile.toml`: `name = "InverseApproximation"`,
  `srcDir = "inverse_approximation"`
- New `inverse_approximation/README.md`
- Imports: `Mathlib.Tactic` and whatever specific `Mathlib.Analysis.*` /
  `Mathlib.Data.Complex.*` modules the `‖·‖`/`Complex` API needs (resolved
  during Stop 3 against actual `exact?` output, not guessed) — no
  Pipeline/DistortionConversion imports; this module is self-contained.

## Vector-space representation choice (see ambiguity-register.md for full reasoning)

**Chosen: `ℂ`** (not `EuclideanSpace ℝ (Fin 2)`, not a bespoke `SensorPoint`-
style struct). Scratch-verified against this exact Mathlib version before
committing:

```lean
example (a b : ℂ) : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
example (a b : ℂ) : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
example (a b : ℝ) : a - b ≤ ‖(a:ℝ) - b‖ := ... -- reverse triangle via norm_sub_norm_le
example (t : ℝ) (z : ℂ) : ‖t • z‖ = |t| * ‖z‖ := by rw [Complex.real_smul, norm_mul]; simp
example (z : ℂ) : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
example (z : ℂ) : ‖z‖^2 = Complex.normSq z := Complex.sq_norm z
example (z : ℂ) : Complex.normSq z = z.re*z.re + z.im*z.im := Complex.normSq_apply z
```

All resolve. This gives triangle inequality, scalar-multiplication norm, and
component bounds "for free" from Mathlib's `NormedField ℂ` instance, instead
of hand-proving them for a bespoke 2-field struct.

## Load-bearing definitions to create (new file, all new — nothing existing touched)

| Name | Role |
|------|------|
| `Coeffs` | structure bundling `k1 k2 k3 p1 p2 : ℝ` (the coefficient vector θ) |
| `radial` | `ℂ → ℝ`, the polynomial radial factor `k1·r²+k2·r⁴+k3·r⁶` where `r² = Complex.normSq` |
| `Φ` | `Coeffs → ℂ → ℂ`, the polynomial Brown-Conrady displacement field |
| `D` | `Coeffs → ℝ → ℂ → ℂ`, `D θ t x = x + t • Φ θ x` |
| `U` | `Coeffs → ℝ → ℂ → ℂ`, `U θ t y = y - t • Φ θ y` (sign flip vs. `D`, deliberate) |
| `M` | `Coeffs → ℝ → ℝ`, explicit boundedness constant |
| `L` | `Coeffs → ℝ → ℝ`, explicit Lipschitz constant |

No existing repository definition is reused or modified — this module does
not import `DistortionModel`, `OpenCVModel`, or any `Pipeline/*` file.

## Theorem texts (specification-level, exact closed forms pre-derived by hand
before any Lean code — see proof-plan.md for the derivation)

```lean
theorem phi_bounded (θ : Coeffs) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖Φ θ z‖ ≤ M θ R

theorem phi_lipschitz (θ : Coeffs) (R : ℝ) (hR : 0 ≤ R) (a b : ℂ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖Φ θ a - Φ θ b‖ ≤ L θ R * ‖a - b‖

theorem inverse_approx_error (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R) (x : ℂ)
    (hx : ‖x‖ + |t| * M θ R ≤ R) :   -- "buffer" hypothesis, see ambiguity-register.md AMB-BIA-002
    ‖U θ t (D θ t x) - x‖ ≤ L θ R * M θ R * t ^ 2
```

with

```lean
M θ R := 2*|θ.k1|*R^3 + 2*|θ.k2|*R^5 + 2*|θ.k3|*R^7 + 5*|θ.p1|*R^2 + 5*|θ.p2|*R^2
L θ R := 6*|θ.k1|*R^2 + 10*|θ.k2|*R^4 + 14*|θ.k3|*R^6 + 10*|θ.p1|*R + 10*|θ.p2|*R
```

(Derivations in `proof-plan.md`/`algebra-plan.md`. These are deliberately
NOT the tightest possible constants — the task asks for "an explicit M/L,"
not the sharpest one, and a generous-but-simple constant keeps the proof
tractable.)

## Allowed changes

- The one new file `inverse_approximation/InverseApproximation.lean` and its
  definitions/theorems as scoped above.
- Small named helper lemmas inside that file for the telescoping/product-
  difference algebra (e.g. bounds on `radial`'s own boundedness/Lipschitz
  behavior, difference-of-squares/cubes facts) — anticipated and pre-approved
  as part of this slice, not scope creep.
- `lakefile.toml`: one new `[[lean_lib]]` entry.
- `inverse_approximation/README.md`: new file.
- `docs/limitations.md`, `docs/specification-questions.md` (SQ-CV-07): short
  notes recording that this bounded estimate now exists, per the user's
  explicit instruction — framed as still not resolving the D-U/U-D question.

## Forbidden changes

- No edits to any file under `Pipeline/`, `DistortionConversion.lean`,
  `DistortionConversionCorrected.lean`, or any other existing theorem file.
- No existence/uniqueness claim about the true inverse of `D_t` (layer 4).
- No unit-conversion (`F`, mm, pixel) machinery folded in (layer 5).
- `sorry`, `admit`, unauthorized `axiom`, `unsafe`, `partial` forbidden.
- No silent softening of `docs/limitations.md`'s existing language — only
  additive notes, per the user's explicit instruction.
