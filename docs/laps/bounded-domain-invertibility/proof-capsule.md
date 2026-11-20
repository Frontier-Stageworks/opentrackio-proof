# Proof Capsule — bounded-domain-invertibility

## Task size
Large. Extends `inverse_approximation/InverseApproximation.lean`'s Banach-fixed-point
architecture to the actual 6-coefficient RATIONAL (not polynomial) Brown-Conrady model
used by `distortXCV`/`distortYCV`/`distortPointCV`/`CVmap`
(`opencv_opentrackio_proofs/Pipeline/OpenCVModel.lean`,
`Pipeline/InverseConjugacyApplication.lean`), and connects the result to
`opencv_openlensio_inverse_conjugate` by discharging its `hCVInv` hypothesis on an
explicit, nonempty, positive-radius disk.

## Hard constraint check (from the task)
- Do not modify `InverseApproximation.lean`'s existing `Coeffs`/`Φ`/`D`/`U`/`M`/`L`
  definitions or any of its proved theorems — the rational-denominator model is
  STRUCTURALLY DIFFERENT (`distortXCV = R(r²)·x + T(x,y)` with `R` already a full ratio
  including its own "1" baseline and no separate "+x" identity term or "t" strength
  parameter, vs. `D θ t x = x + t•Φ θ x`) and needs its own new definitions — not a
  retrofit of the existing ones.
- Reuse what IS generic: `radial_bounded`/`radial_lipschitz` (parameterized by a `Coeffs`
  value; depend only on `θ.k1,θ.k2,θ.k3`, ignoring `θ.p1,θ.p2` — directly reusable for
  BOTH the new numerator polynomial (k1,k2,k3) and denominator polynomial (k4,k5,k6) by
  constructing dummy `Coeffs` values with `p1=p2=0`), `normSq_lipschitz`/
  `normSq_sq_lipschitz`/`normSq_cube_lipschitz` (fully generic, no `Coeffs` dependence at
  all), `smul_norm`. Also reuse `conjugate_invOn` (`InverseConjugacy.lean`, this session's
  prior slice) to transport the ℂ-based existence result back to `SensorPoint`.
- No new axioms, no `sorry`, no silently weakened conclusions.

## Architecture decision (and why)

Representation: **ℂ**, mirroring `InverseApproximation.lean` exactly, to reuse its generic
`normSq_*`/`smul_norm` lemmas by direct import rather than re-deriving them for a second
representation. The final connection to `CVmap`/`opencv_openlensio_inverse_conjugate`
(stated over `SensorPoint`) is made via a `SensorPoint ≃ ℂ` equivalence and
`conjugate_invOn`, exactly as `ScreenScale`/`screenScaleEquiv` connected `SensorPoint` to
itself in the prior slice — same tool, new purpose (representation transport, not
coordinate scaling).

Key new definitions (plan, finalized against actual Lean output as built):
- `RCoeffs`: k1,k2,k3 (radial numerator, OpenCV convention), k4,k5,k6 (radial
  denominator), p1,p2 (tangential) — six-plus-two fields, matching `distortXCV`'s own
  parameter list exactly (NOT `RadialCoefficients`'s alternating OTI convention).
- `Nnum θ z := 1 + θ.k1·normSq z + θ.k2·(normSq z)² + θ.k3·(normSq z)³`
  `Dden θ z := 1 + θ.k4·normSq z + θ.k5·(normSq z)² + θ.k6·(normSq z)³`
  Both expressible as `1 + radial ⟨k_i,k_j,k_k,0,0⟩ z` for the appropriate triple, so
  `radial_bounded`/`radial_lipschitz` apply directly after a `+1` shift (the `+1`
  cancels in any Lipschitz difference, and shifts the bound by exactly 1).
- Denominator safety: `|k4|R²+|k5|R⁴+|k6|R⁶ < 1 ⟹ Dden θ z ≥ 1-(|k4|R²+|k5|R⁴+|k6|R⁶) > 0`
  on `‖z‖≤R`, via `radial_bounded`'s dummy-`Coeffs` instantiation.
- `Rfac θ z := Nnum θ z / Dden θ z` — the rational radial factor. Bounded/Lipschitz on
  the disk via a quotient-rule combination of the Nnum/Dden bounds (new, short algebra —
  not present anywhere in `InverseApproximation.lean`, since that file's `radial` has no
  denominator at all).
- `Tang θ z := ⟨2·p1·z.re·z.im + p2·(normSq z+2z.re²), p1·(normSq z+2z.im²)+2·p2·z.re·z.im⟩`
  (as a ℂ value) — same shape as `Φ`'s own tangential part, reused by the SAME technique
  as `phi_bounded`/`phi_lipschitz`'s tangential-term bullets (not a literal lemma reuse,
  since `Φ` bundles radial and tangential together rather than exposing the tangential
  part standalone, but the per-term algebra is identical).
- `RDist θ z := Rfac θ z • z + Tang θ z` — the actual forward map, matching
  `distortXCV`/`distortYCV`'s combined shape exactly (verified by an explicit bridging
  lemma to `distortPointCV`, analogous to `ForwardConjugacy.lean`'s `hCVx`/`hCVy`).
- Bound `MR`, Lipschitz `LR` for `RDist` on the disk, combining `Rfac`'s and `Tang`'s
  bounds/Lipschitz constants via the same triangle-inequality technique
  `phi_bounded`/`phi_lipschitz` use.
- Injectivity + existence via the SAME two-step architecture as
  `D_eq_implies_eq`/`inverse_step_maps_disk`/`inverse_step_lipschitz`/
  `D_exists_unique_preimage`, re-derived for `RDist` (no `t`/`D`/`U` split needed here,
  since `RDist` already IS the full forward map at full strength — no separate
  "approximate inverse" layer is attempted, only existence/uniqueness of the TRUE
  inverse, matching the task's request).

## Two calibration examples required
1. Pure radial (nonzero k1 or k2, p1=p2=0) — simplest nontrivial case, isolates the new
   rational-denominator machinery from the tangential machinery.
2. Both radial AND tangential nonzero — exercises the full combined bound/Lipschitz
   machinery end to end.
Both must have an explicit, checkable, POSITIVE disk radius `R>0` and coefficient bounds
satisfying the derived sufficient conditions, verified by `norm_num`/`nlinarith`, not
merely asserted.

## Honesty commitment
If the Lipschitz/contraction algebra for the combined rational+tangential map proves
intractable within reasonable effort, this will be reported as a precise blocked
obligation (per the task's explicit instruction), not silently weakened into a smaller
claim dressed up as the original one.
