/-
  InjectivityModel.lean — SLICE-UI-00, SLICE-UI-01, SLICE-UI-02, SLICE-UI-03, SLICE-UI-04

  Injectivity properties of the Brown-Conrady undistortion map.

  This file proves injectivity of undistortPoint under restricted conditions.
  It does NOT prove global injectivity or define a forward distortion function.
  See docs/laps/undistort-invertibility/work-queue.md for the staged roadmap.

  SLICE-UI-00: On-circle injectivity with zero tangential coefficients.
  Theorem: if ε₁ and ε₂ lie on the same circle (sensorRadius ε₁ = sensorRadius ε₂),
  p₁ = p₂ = 0, and R(r) ≠ 0, then U(ε₁) = U(ε₂) → ε₁ = ε₂.

  SLICE-UI-01: Global pure-radial injectivity with zero tangential coefficients.

  SLICE-UI-02: Radial term positivity under coefficient conditions.
  Theorems: radialTerm_pos (R > 0 from per-point numerator/denominator positivity)
  and radialTerm_ne_zero (corollary: R ≠ 0). Allows callers to discharge the hR₁
  hypothesis in undistortPoint_injective_pure_radial concretely.

  SLICE-UI-03: On-circle injectivity with full tangential coefficients (general p).

  SLICE-UI-04: Concrete left inverse for the zero-tangential case.
  Definition: radialDescale k r hr ε = ⟨ε.x / R(r), ε.y / R(r)⟩.
  Theorem: radialDescale_left_inverse_zero_tangential proves D(r, U(ε)) = ε when
  p = 0 and R(r) ≠ 0. The explicit r parameter reflects AMB-UI-001: no closed-form
  D exists from the output alone; knowing the input radius is required.
  Theorem: undistortPoint_injective_on_circle_tangential. Extends UI-00 to nonzero p.
  Proof approach: subtracting the two component equalities gives a linear system
  A·δx + B·δy = 0, C·δx + D·δy = 0 in the coordinate deltas. If the algebraic
  determinant AD − BC ≠ 0 (caller-supplied hDet), then δx = δy = 0. No analytic
  Jacobian or IFT required — purely algebraic via linear_combination + mul_eq_zero.
  Theorem: if p₁ = p₂ = 0, R(r₁) ≠ 0, and the radial scaling r ↦ R(r)·r is injective
  on [0,∞) (caller-supplied hScaleInj), then U(ε₁) = U(ε₂) → ε₁ = ε₂.
  Proof reduces to UI-00 after deriving sensorRadius ε₁ = sensorRadius ε₂ from
  the squared component equalities.

  This is a necessary condition for invertibility. It does not imply that a
  closed-form inverse exists. The OpenLensIO spec defines D = U⁻¹ in Eqs (5)
  and (11) and asserts it exists; the numerical iteration note (Eq 11) is about
  computing D, not defining it. No closed-form formula for D exists for the full
  Brown-Conrady model; `radialDescale` (UI-04) provides a concrete left inverse
  for the p=0 subcase with explicit input-radius parameter.
-/

import DistortionModel

/-─────────────────────────────────────────────────────────────────────────────
  undistortPoint_injective_zero_tangential

  With zero tangential coefficients (p₁ = p₂ = 0), on each circle of fixed
  radius (sensorRadius ε₁ = sensorRadius ε₂), and with a nonzero radial factor
  (R ≠ 0), the undistortion map is injective:

    U(ε₁) = U(ε₂) → ε₁ = ε₂

  Key proof fact: radialTerm k r h ignores its proof argument h in the body
  (bound as _). So radialTerm k (sensorRadius ε₁) h₁ = radialTerm k (sensorRadius ε₂) h₂
  follows from sensorRadius ε₁ = sensorRadius ε₂ alone, without proof-irrelevance
  machinery.

  Scope: on-circle only (hSameR required); zero tangential only (hp1, hp2 required);
  nonzero radial factor (hR required). See AMB-UI-002, AMB-UI-003.
─────────────────────────────────────────────────────────────────────────────-/

theorem undistortPoint_injective_zero_tangential
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0)
    (ε₁ ε₂ : SensorPoint)
    (h₁ : denominatorNonzero k (sensorRadius ε₁))
    (h₂ : denominatorNonzero k (sensorRadius ε₂))
    (hR : radialTerm k (sensorRadius ε₁) h₁ ≠ 0)
    (hSameR : sensorRadius ε₁ = sensorRadius ε₂)
    (hU : undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂) :
    ε₁ = ε₂ := by
  have hRR : radialTerm k (sensorRadius ε₁) h₁ = radialTerm k (sensorRadius ε₂) h₂ := by
    simp only [radialTerm, hSameR]
  have hR' : radialTerm k (sensorRadius ε₂) h₂ ≠ 0 := hRR ▸ hR
  have hX : undistortX k p ε₁ h₁ = undistortX k p ε₂ h₂ := congr_arg SensorPoint.x hU
  have hY : undistortY k p ε₁ h₁ = undistortY k p ε₂ h₂ := congr_arg SensorPoint.y hU
  simp only [undistortX, hp1, hp2, mul_zero, zero_mul, add_zero] at hX
  simp only [undistortY, hp1, hp2, mul_zero, zero_mul, add_zero] at hY
  rw [hRR] at hX hY
  exact SensorPoint.ext (mul_left_cancel₀ hR' hX) (mul_left_cancel₀ hR' hY)

/-─────────────────────────────────────────────────────────────────────────────
  SLICE-UI-01: Global pure-radial injectivity

  radialScale k r — the radial factor R(r) without a domain-condition proof
  argument. Used in the hScaleInj hypothesis of undistortPoint_injective_pure_radial,
  where the caller asserts that r ↦ (R(r)·r)² is injective on [0,∞).

  When denominatorNonzero k r holds, radialScale k r = radialTerm k r h
  (bridge lemma: radialTerm_eq_radialScale).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def radialScale (k : RadialCoefficients) (r : ℝ) : ℝ :=
  (1 + k.k1 * r ^ 2 + k.k3 * r ^ 4 + k.k5 * r ^ 6) /
  (1 + k.k2 * r ^ 2 + k.k4 * r ^ 4 + k.k6 * r ^ 6)

lemma radialTerm_eq_radialScale (k : RadialCoefficients) (r : ℝ)
    (h : denominatorNonzero k r) : radialTerm k r h = radialScale k r := by
  simp [radialTerm, radialScale]

/-─────────────────────────────────────────────────────────────────────────────
  undistortPoint_injective_pure_radial

  With zero tangential coefficients (p₁ = p₂ = 0), a nonzero radial factor at
  ε₁, and caller-supplied injectivity of the squared radial scaling function
  (hScaleInj: r ↦ (radialScale k r)² · r² is injective on [0,∞)), the
  undistortion map is globally injective:

    U(ε₁) = U(ε₂) → ε₁ = ε₂

  Proof sketch:
  1. Extract and simplify component equalities (p = 0 → pure radial scaling).
  2. Square each component equality to get R₁²·x₁² = R₂²·x₂², R₁²·y₁² = R₂²·y₂².
  3. Add: R₁²·r₁² = R₂²·r₂² via sensorRadius² = x² + y².
  4. Apply hScaleInj to recover sensorRadius ε₁ = sensorRadius ε₂.
  5. Reduce to undistortPoint_injective_zero_tangential (SLICE-UI-00).

  The hSameR restriction from UI-00 is not an input; it is derived as a
  consequence of the squared scaled-radii equality.
─────────────────────────────────────────────────────────────────────────────-/

theorem undistortPoint_injective_pure_radial
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0)
    (ε₁ ε₂ : SensorPoint)
    (h₁ : denominatorNonzero k (sensorRadius ε₁))
    (h₂ : denominatorNonzero k (sensorRadius ε₂))
    (hR₁ : radialTerm k (sensorRadius ε₁) h₁ ≠ 0)
    (hScaleInj : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
        (radialScale k r₁) ^ 2 * r₁ ^ 2 = (radialScale k r₂) ^ 2 * r₂ ^ 2 → r₁ = r₂)
    (hU : undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂) :
    ε₁ = ε₂ := by
  -- Step 1: Extract and simplify component equalities (p = 0)
  have hX : undistortX k p ε₁ h₁ = undistortX k p ε₂ h₂ := congr_arg SensorPoint.x hU
  have hY : undistortY k p ε₁ h₁ = undistortY k p ε₂ h₂ := congr_arg SensorPoint.y hU
  simp only [undistortX, hp1, hp2, mul_zero, zero_mul, add_zero] at hX
  simp only [undistortY, hp1, hp2, mul_zero, zero_mul, add_zero] at hY
  -- hX : R₁ * ε₁.x = R₂ * ε₂.x,  hY : R₁ * ε₁.y = R₂ * ε₂.y
  -- Step 2: Square each component equality
  have hX2 : (radialTerm k (sensorRadius ε₁) h₁) ^ 2 * ε₁.x ^ 2 =
             (radialTerm k (sensorRadius ε₂) h₂) ^ 2 * ε₂.x ^ 2 := by
    have h := congr_arg (· ^ 2) hX; simp only [mul_pow] at h; exact h
  have hY2 : (radialTerm k (sensorRadius ε₁) h₁) ^ 2 * ε₁.y ^ 2 =
             (radialTerm k (sensorRadius ε₂) h₂) ^ 2 * ε₂.y ^ 2 := by
    have h := congr_arg (· ^ 2) hY; simp only [mul_pow] at h; exact h
  -- Step 3: sensorRadius squared = sum of squared components
  have hsr1 : (sensorRadius ε₁) ^ 2 = ε₁.x ^ 2 + ε₁.y ^ 2 := by
    unfold sensorRadius; rw [Real.sq_sqrt (by positivity)]
  have hsr2 : (sensorRadius ε₂) ^ 2 = ε₂.x ^ 2 + ε₂.y ^ 2 := by
    unfold sensorRadius; rw [Real.sq_sqrt (by positivity)]
  -- Step 4: Add squared component equalities, restate with sensorRadius and radialScale
  have hSumXY : (radialTerm k (sensorRadius ε₁) h₁) ^ 2 * (ε₁.x ^ 2 + ε₁.y ^ 2) =
                (radialTerm k (sensorRadius ε₂) h₂) ^ 2 * (ε₂.x ^ 2 + ε₂.y ^ 2) := by
    nlinarith [hX2, hY2]
  have hSum : (radialScale k (sensorRadius ε₁)) ^ 2 * (sensorRadius ε₁) ^ 2 =
              (radialScale k (sensorRadius ε₂)) ^ 2 * (sensorRadius ε₂) ^ 2 := by
    rw [← radialTerm_eq_radialScale k (sensorRadius ε₁) h₁,
        ← radialTerm_eq_radialScale k (sensorRadius ε₂) h₂, hsr1, hsr2]
    exact hSumXY
  -- Step 5: Derive sensorRadius ε₁ = sensorRadius ε₂ from hScaleInj
  have hr : sensorRadius ε₁ = sensorRadius ε₂ :=
    hScaleInj _ _ (sensorRadius_nonneg ε₁) (sensorRadius_nonneg ε₂) hSum
  -- Step 6: Reduce to UI-00
  exact undistortPoint_injective_zero_tangential k p hp1 hp2 ε₁ ε₂ h₁ h₂ hR₁ hr hU

/-─────────────────────────────────────────────────────────────────────────────
  SLICE-UI-02: Radial term positivity under coefficient conditions

  radialTerm_pos: if the numerator and denominator of R(r) are both strictly
  positive at r, then R(r) > 0. Proof: unfold to a / b; div_pos closes.

  radialTerm_ne_zero: corollary via .ne'. Allows callers to discharge the
  hR₁ hypothesis in undistortPoint_injective_pure_radial concretely instead
  of asserting R ≠ 0 as an opaque precondition.

  AMB-UI-003 resolution: per-point polynomial positivity (hNum, hDen) is the
  minimal sufficient condition. No global coefficient constraints are assumed.
─────────────────────────────────────────────────────────────────────────────-/

theorem radialTerm_pos
    (k : RadialCoefficients) (r : ℝ)
    (h : denominatorNonzero k r)
    (hNum : 0 < 1 + k.k1 * r ^ 2 + k.k3 * r ^ 4 + k.k5 * r ^ 6)
    (hDen : 0 < 1 + k.k2 * r ^ 2 + k.k4 * r ^ 4 + k.k6 * r ^ 6) :
    0 < radialTerm k r h := by
  simp only [radialTerm]
  exact div_pos hNum hDen

theorem radialTerm_ne_zero
    (k : RadialCoefficients) (r : ℝ)
    (h : denominatorNonzero k r)
    (hNum : 0 < 1 + k.k1 * r ^ 2 + k.k3 * r ^ 4 + k.k5 * r ^ 6)
    (hDen : 0 < 1 + k.k2 * r ^ 2 + k.k4 * r ^ 4 + k.k6 * r ^ 6) :
    radialTerm k r h ≠ 0 :=
  (radialTerm_pos k r h hNum hDen).ne'

/-─────────────────────────────────────────────────────────────────────────────
  SLICE-UI-03: On-circle injectivity with full tangential coefficients

  Extends SLICE-UI-00 to nonzero tangential coefficients (general p₁, p₂).
  The on-circle restriction (hSameR) is retained, which equates the radial
  terms R₁ = R₂ = R and collapses the two sensorRadius values.

  With p nonzero, U(ε₁) = U(ε₂) no longer factors cleanly as R·scaling.
  Instead, subtracting the two component equalities gives a linear system in
  the coordinate deltas δx = ε₁.x − ε₂.x and δy = ε₁.y − ε₂.y:

    A·δx + B·δy = 0   (from x-component)
    C·δx + D·δy = 0   (from y-component)

  where:
    A = R + 2·p₁·ε₁.y + 2·p₂·(ε₁.x + ε₂.x)
    B = 2·p₁·ε₂.x
    C = 2·p₂·ε₁.y
    D = R + 2·p₁·(ε₁.y + ε₂.y) + 2·p₂·ε₂.x

  If the algebraic determinant AD − BC ≠ 0 (caller-supplied hDet), the only
  solution is δx = δy = 0, i.e., ε₁ = ε₂.

  Proof:
  - (AD−BC)·δx = D·eqX − B·eqY  via linear_combination (ring verifies)
  - (AD−BC)·δy = A·eqY − C·eqX  via linear_combination (ring verifies)
  - Cancel det from each via mul_eq_zero + hDet; close with SensorPoint.ext

  When p = 0: A = D = R, B = C = 0, det = R² ≠ 0 from hR ≠ 0 — recovering
  the structure of undistortPoint_injective_zero_tangential.
─────────────────────────────────────────────────────────────────────────────-/

theorem undistortPoint_injective_on_circle_tangential
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε₁ ε₂ : SensorPoint)
    (h₁ : denominatorNonzero k (sensorRadius ε₁))
    (h₂ : denominatorNonzero k (sensorRadius ε₂))
    (hSameR : sensorRadius ε₁ = sensorRadius ε₂)
    (hDet : (radialTerm k (sensorRadius ε₁) h₁ + 2 * p.p1 * ε₁.y +
             2 * p.p2 * (ε₁.x + ε₂.x)) *
            (radialTerm k (sensorRadius ε₁) h₁ + 2 * p.p1 * (ε₁.y + ε₂.y) +
             2 * p.p2 * ε₂.x) -
            4 * p.p1 * p.p2 * ε₁.y * ε₂.x ≠ 0)
    (hU : undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂) :
    ε₁ = ε₂ := by
  -- Equate radial terms using hSameR (radialTerm ignores its proof argument)
  have hRR : radialTerm k (sensorRadius ε₁) h₁ = radialTerm k (sensorRadius ε₂) h₂ := by
    simp only [radialTerm, hSameR]
  -- Extract component equalities
  have hX : undistortX k p ε₁ h₁ = undistortX k p ε₂ h₂ := congr_arg SensorPoint.x hU
  have hY : undistortY k p ε₁ h₁ = undistortY k p ε₂ h₂ := congr_arg SensorPoint.y hU
  -- Unfold component definitions (tangential terms kept)
  simp only [undistortX] at hX
  simp only [undistortY] at hY
  -- Unify R and sensorRadius on both sides
  rw [← hRR, ← hSameR] at hX hY
  -- Derive (AD − BC) · δx = 0 via D · eqX − B · eqY
  have hδx : ((radialTerm k (sensorRadius ε₁) h₁ + 2 * p.p1 * ε₁.y +
               2 * p.p2 * (ε₁.x + ε₂.x)) *
              (radialTerm k (sensorRadius ε₁) h₁ + 2 * p.p1 * (ε₁.y + ε₂.y) +
               2 * p.p2 * ε₂.x) -
              4 * p.p1 * p.p2 * ε₁.y * ε₂.x) * (ε₁.x - ε₂.x) = 0 := by
    linear_combination
      (radialTerm k (sensorRadius ε₁) h₁ + 2 * p.p1 * (ε₁.y + ε₂.y) +
       2 * p.p2 * ε₂.x) * hX -
      (2 * p.p1 * ε₂.x) * hY
  -- Derive (AD − BC) · δy = 0 via A · eqY − C · eqX
  have hδy : ((radialTerm k (sensorRadius ε₁) h₁ + 2 * p.p1 * ε₁.y +
               2 * p.p2 * (ε₁.x + ε₂.x)) *
              (radialTerm k (sensorRadius ε₁) h₁ + 2 * p.p1 * (ε₁.y + ε₂.y) +
               2 * p.p2 * ε₂.x) -
              4 * p.p1 * p.p2 * ε₁.y * ε₂.x) * (ε₁.y - ε₂.y) = 0 := by
    linear_combination
      (radialTerm k (sensorRadius ε₁) h₁ + 2 * p.p1 * ε₁.y +
       2 * p.p2 * (ε₁.x + ε₂.x)) * hY -
      (2 * p.p2 * ε₁.y) * hX
  -- Cancel det from δx and δy using hDet
  have hx : ε₁.x = ε₂.x := by
    rcases mul_eq_zero.mp hδx with h | h
    · exact absurd h hDet
    · linarith
  have hy : ε₁.y = ε₂.y := by
    rcases mul_eq_zero.mp hδy with h | h
    · exact absurd h hDet
    · linarith
  exact SensorPoint.ext hx hy

/-─────────────────────────────────────────────────────────────────────────────
  SLICE-UI-04: Concrete left inverse for the zero-tangential case

  radialDescale k r hr ε divides each component of ε by R(r) = radialTerm k r hr.
  This is the explicit D for the zero-tangential subclass, parameterized by the
  input radius r.

  AMB-UI-005 resolution: concrete D (not existential), for the p = 0 case.
  AMB-UI-001 reflection: r must be supplied explicitly — there is no closed-form
  way to recover r from the output u = U(ε) for general Brown-Conrady. Knowing r
  is the minimal additional datum required to construct D(r, u) = u / R(r).

  radialDescale_left_inverse_zero_tangential closes the first D ∘ U = id result
  in the campaign: D(r, U(ε)) = ε when p = 0 and R(r) ≠ 0.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def radialDescale
    (k : RadialCoefficients) (r : ℝ)
    (hr : denominatorNonzero k r) (ε : SensorPoint) : SensorPoint :=
  let R := radialTerm k r hr
  ⟨ε.x / R, ε.y / R⟩

theorem radialDescale_left_inverse_zero_tangential
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0)
    (ε : SensorPoint)
    (h : denominatorNonzero k (sensorRadius ε))
    (hR : radialTerm k (sensorRadius ε) h ≠ 0) :
    radialDescale k (sensorRadius ε) h (undistortPoint k p ε h) = ε := by
  simp only [radialDescale, undistortPoint, undistortX, undistortY, hp1, hp2,
             mul_zero, zero_mul, add_zero]
  exact SensorPoint.ext (mul_div_cancel_left₀ ε.x hR) (mul_div_cancel_left₀ ε.y hR)
