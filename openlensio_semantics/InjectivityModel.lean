/-
  InjectivityModel.lean — SLICE-UI-00, SLICE-UI-01, SLICE-UI-02

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
  Theorem: if p₁ = p₂ = 0, R(r₁) ≠ 0, and the radial scaling r ↦ R(r)·r is injective
  on [0,∞) (caller-supplied hScaleInj), then U(ε₁) = U(ε₂) → ε₁ = ε₂.
  Proof reduces to UI-00 after deriving sensorRadius ε₁ = sensorRadius ε₂ from
  the squared component equalities.

  This is a necessary condition for invertibility. It does not imply that a
  closed-form inverse exists (SLICE-UI-04, deferred). The OpenLensIO spec
  (following Eq 11) characterises U⁻¹ as computed via numerical iterative
  methods; no closed-form D is assumed here.
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
