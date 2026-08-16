/-
  InverseApproximation.lean

  A bounded-error first-order approximate inverse, and a local existence/
  uniqueness theorem for the true inverse, for a polynomial (non-rational)
  Brown-Conrady-shaped displacement field, on a bounded disk. Status:
  Layers 1-3 complete (boundedness, Lipschitz, first-order
  composition-error estimate); Layer 4 complete (injectivity of the
  forward map, an invariant disk and contraction estimate for the
  fixed-point iteration step, and — via Mathlib's Banach fixed-point
  theorem — local existence and uniqueness of the true inverse,
  `D_exists_unique_preimage`). See README.md,
  docs/laps/bounded-inverse-approximation/, docs/laps/inverse-injectivity/,
  and docs/laps/inverse-existence/ for full context, derivation, and scope.
  Motivated by, but does not resolve, docs/specification-questions.md
  SQ-CV-07 — `D_exists_unique_preimage` is a standalone fact about the
  polynomial model; its relevance to that interoperability question is a
  separate, open matter.

  Deliberately independent of opencv_opentrackio_proofs/ and
  openlensio_semantics/: no imports from either, and this file is not
  imported by anything under Pipeline/.

  Vector representation: ℂ (not a bespoke struct, not EuclideanSpace),
  chosen to inherit Mathlib's NormedField ℂ triangle-inequality/scalar-norm
  API directly. See ambiguity-register.md AMB-BIA-001.
-/

import Mathlib.Tactic

/-─────────────────────────────────────────────────────────────────────────────
  Coeffs — the coefficient vector θ = (k1, k2, k3, p1, p2).
─────────────────────────────────────────────────────────────────────────────-/

structure Coeffs where
  k1 : ℝ
  k2 : ℝ
  k3 : ℝ
  p1 : ℝ
  p2 : ℝ

/-─────────────────────────────────────────────────────────────────────────────
  radial — the polynomial radial factor k1·r² + k2·r⁴ + k3·r⁶, where
  r² = Complex.normSq z = ‖z‖².
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def radial (θ : Coeffs) (z : ℂ) : ℝ :=
  θ.k1 * Complex.normSq z + θ.k2 * (Complex.normSq z) ^ 2 + θ.k3 * (Complex.normSq z) ^ 3

/-─────────────────────────────────────────────────────────────────────────────
  Φ — the pure polynomial (non-rational) Brown-Conrady displacement field.
  Φx = radial·x + 2p1·x·y + p2·(r²+2x²)
  Φy = radial·y + p1·(r²+2y²) + 2p2·x·y
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def Φ (θ : Coeffs) (z : ℂ) : ℂ :=
  ⟨radial θ z * z.re + 2 * θ.p1 * z.re * z.im + θ.p2 * (Complex.normSq z + 2 * z.re ^ 2),
   radial θ z * z.im + θ.p1 * (Complex.normSq z + 2 * z.im ^ 2) + 2 * θ.p2 * z.re * z.im⟩

/-─────────────────────────────────────────────────────────────────────────────
  D — the scaled distortion map D_t(x) = x + t • Φ_θ(x).
  U — the first-order approximate inverse U_t(y) = y - t • Φ_θ(y).
  NOTE the sign flip vs. D: deliberate, the point of the exercise.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def D (θ : Coeffs) (t : ℝ) (x : ℂ) : ℂ := x + t • Φ θ x

noncomputable def U (θ : Coeffs) (t : ℝ) (y : ℂ) : ℂ := y - t • Φ θ y

/-─────────────────────────────────────────────────────────────────────────────
  M, L — explicit (not tight) boundedness / Lipschitz constants for Φ on the
  disk ‖z‖ ≤ R. Derivations in docs/laps/bounded-inverse-approximation/
  algebra-plan.md.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def M (θ : Coeffs) (R : ℝ) : ℝ :=
  2 * |θ.k1| * R ^ 3 + 2 * |θ.k2| * R ^ 5 + 2 * |θ.k3| * R ^ 7
    + 5 * |θ.p1| * R ^ 2 + 5 * |θ.p2| * R ^ 2

noncomputable def L (θ : Coeffs) (R : ℝ) : ℝ :=
  6 * |θ.k1| * R ^ 2 + 10 * |θ.k2| * R ^ 4 + 14 * |θ.k3| * R ^ 6
    + 10 * |θ.p1| * R + 10 * |θ.p2| * R

/-─────────────────────────────────────────────────────────────────────────────
  Mrad, Lrad — local helper constants for `radial` alone (algebra-plan.md).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def Mrad (θ : Coeffs) (R : ℝ) : ℝ :=
  |θ.k1| * R ^ 2 + |θ.k2| * R ^ 4 + |θ.k3| * R ^ 6

noncomputable def Lrad (θ : Coeffs) (R : ℝ) : ℝ :=
  2 * |θ.k1| * R + 4 * |θ.k2| * R ^ 3 + 6 * |θ.k3| * R ^ 5

/-─────────────────────────────────────────────────────────────────────────────
  radial_bounded — |radial θ z| ≤ Mrad θ R for ‖z‖ ≤ R.
─────────────────────────────────────────────────────────────────────────────-/

theorem radial_bounded (θ : Coeffs) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |radial θ z| ≤ Mrad θ R := by
  have hns_nonneg : (0:ℝ) ≤ Complex.normSq z := Complex.normSq_nonneg z
  have hns_le : Complex.normSq z ≤ R ^ 2 := by
    have h1 : Complex.normSq z = ‖z‖ ^ 2 := (Complex.sq_norm z).symm
    rw [h1]
    exact pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hns2_le : (Complex.normSq z) ^ 2 ≤ R ^ 4 := by
    have := pow_le_pow_left₀ hns_nonneg hns_le 2
    calc (Complex.normSq z) ^ 2 ≤ (R ^ 2) ^ 2 := this
      _ = R ^ 4 := by ring
  have hns3_le : (Complex.normSq z) ^ 3 ≤ R ^ 6 := by
    have := pow_le_pow_left₀ hns_nonneg hns_le 3
    calc (Complex.normSq z) ^ 3 ≤ (R ^ 2) ^ 3 := this
      _ = R ^ 6 := by ring
  unfold radial Mrad
  calc |θ.k1 * Complex.normSq z + θ.k2 * (Complex.normSq z) ^ 2 + θ.k3 * (Complex.normSq z) ^ 3|
      ≤ |θ.k1 * Complex.normSq z| + |θ.k2 * (Complex.normSq z) ^ 2|
          + |θ.k3 * (Complex.normSq z) ^ 3| := abs_add_three _ _ _
    _ = |θ.k1| * Complex.normSq z + |θ.k2| * (Complex.normSq z) ^ 2
          + |θ.k3| * (Complex.normSq z) ^ 3 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hns_nonneg,
            abs_of_nonneg (pow_nonneg hns_nonneg 2), abs_of_nonneg (pow_nonneg hns_nonneg 3)]
    _ ≤ |θ.k1| * R ^ 2 + |θ.k2| * R ^ 4 + |θ.k3| * R ^ 6 := by gcongr

/-─────────────────────────────────────────────────────────────────────────────
  normSq_lipschitz — |r²(a) - r²(b)| ≤ 2R·‖a-b‖ for ‖a‖,‖b‖ ≤ R.
  Key building block for radial_lipschitz (algebra-plan.md).
─────────────────────────────────────────────────────────────────────────────-/

theorem normSq_lipschitz (R : ℝ) (a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |Complex.normSq a - Complex.normSq b| ≤ 2 * R * ‖a - b‖ := by
  have heq : Complex.normSq a - Complex.normSq b = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) := by
    rw [← Complex.sq_norm, ← Complex.sq_norm]; ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖a‖ + ‖b‖)]
  have h1 : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
  have h2 : ‖a‖ + ‖b‖ ≤ 2 * R := by linarith
  calc |‖a‖ - ‖b‖| * (‖a‖ + ‖b‖) ≤ ‖a - b‖ * (2 * R) := by
        apply mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
    _ = 2 * R * ‖a - b‖ := by ring

/-─────────────────────────────────────────────────────────────────────────────
  normSq_sq_lipschitz — |r⁴(a) - r⁴(b)| ≤ 4R³·‖a-b‖ for ‖a‖,‖b‖ ≤ R.
─────────────────────────────────────────────────────────────────────────────-/

theorem normSq_sq_lipschitz (R : ℝ) (hR : 0 ≤ R) (a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |(Complex.normSq a) ^ 2 - (Complex.normSq b) ^ 2| ≤ 4 * R ^ 3 * ‖a - b‖ := by
  have hda : (0:ℝ) ≤ Complex.normSq a := Complex.normSq_nonneg a
  have hdb : (0:ℝ) ≤ Complex.normSq b := Complex.normSq_nonneg b
  have hale : Complex.normSq a ≤ R ^ 2 := by
    rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg a) ha 2
  have hble : Complex.normSq b ≤ R ^ 2 := by
    rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg b) hb 2
  have heq : (Complex.normSq a) ^ 2 - (Complex.normSq b) ^ 2
      = (Complex.normSq a - Complex.normSq b) * (Complex.normSq a + Complex.normSq b) := by ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Complex.normSq a + Complex.normSq b)]
  have h1 := normSq_lipschitz R a b ha hb
  have h2 : Complex.normSq a + Complex.normSq b ≤ 2 * R ^ 2 := by linarith
  calc |Complex.normSq a - Complex.normSq b| * (Complex.normSq a + Complex.normSq b)
      ≤ (2 * R * ‖a - b‖) * (2 * R ^ 2) := by
        apply mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 4 * R ^ 3 * ‖a - b‖ := by ring

/-─────────────────────────────────────────────────────────────────────────────
  normSq_cube_lipschitz — |r⁶(a) - r⁶(b)| ≤ 6R⁵·‖a-b‖ for ‖a‖,‖b‖ ≤ R.
─────────────────────────────────────────────────────────────────────────────-/

theorem normSq_cube_lipschitz (R : ℝ) (hR : 0 ≤ R) (a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |(Complex.normSq a) ^ 3 - (Complex.normSq b) ^ 3| ≤ 6 * R ^ 5 * ‖a - b‖ := by
  have hda : (0:ℝ) ≤ Complex.normSq a := Complex.normSq_nonneg a
  have hdb : (0:ℝ) ≤ Complex.normSq b := Complex.normSq_nonneg b
  have hale : Complex.normSq a ≤ R ^ 2 := by
    rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg a) ha 2
  have hble : Complex.normSq b ≤ R ^ 2 := by
    rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg b) hb 2
  have heq : (Complex.normSq a) ^ 3 - (Complex.normSq b) ^ 3
      = (Complex.normSq a - Complex.normSq b)
        * ((Complex.normSq a) ^ 2 + Complex.normSq a * Complex.normSq b
            + (Complex.normSq b) ^ 2) := by ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity :
      (0:ℝ) ≤ (Complex.normSq a) ^ 2 + Complex.normSq a * Complex.normSq b + (Complex.normSq b) ^ 2)]
  have h1 := normSq_lipschitz R a b ha hb
  have h2 : (Complex.normSq a) ^ 2 + Complex.normSq a * Complex.normSq b + (Complex.normSq b) ^ 2
      ≤ 3 * R ^ 4 := by nlinarith
  calc |Complex.normSq a - Complex.normSq b|
        * ((Complex.normSq a) ^ 2 + Complex.normSq a * Complex.normSq b + (Complex.normSq b) ^ 2)
      ≤ (2 * R * ‖a - b‖) * (3 * R ^ 4) := by
        apply mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 6 * R ^ 5 * ‖a - b‖ := by ring

/-─────────────────────────────────────────────────────────────────────────────
  radial_lipschitz — |radial θ a - radial θ b| ≤ Lrad θ R · ‖a-b‖ for
  ‖a‖,‖b‖ ≤ R.
─────────────────────────────────────────────────────────────────────────────-/

theorem radial_lipschitz (θ : Coeffs) (R : ℝ) (hR : 0 ≤ R) (a b : ℂ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |radial θ a - radial θ b| ≤ Lrad θ R * ‖a - b‖ := by
  have h2 := normSq_lipschitz R a b ha hb
  have h4 := normSq_sq_lipschitz R hR a b ha hb
  have h6 := normSq_cube_lipschitz R hR a b ha hb
  have heq : radial θ a - radial θ b
      = θ.k1 * (Complex.normSq a - Complex.normSq b)
        + θ.k2 * ((Complex.normSq a) ^ 2 - (Complex.normSq b) ^ 2)
        + θ.k3 * ((Complex.normSq a) ^ 3 - (Complex.normSq b) ^ 3) := by
    unfold radial; ring
  rw [heq]
  unfold Lrad
  calc |θ.k1 * (Complex.normSq a - Complex.normSq b)
        + θ.k2 * ((Complex.normSq a) ^ 2 - (Complex.normSq b) ^ 2)
        + θ.k3 * ((Complex.normSq a) ^ 3 - (Complex.normSq b) ^ 3)|
      ≤ |θ.k1 * (Complex.normSq a - Complex.normSq b)|
          + |θ.k2 * ((Complex.normSq a) ^ 2 - (Complex.normSq b) ^ 2)|
          + |θ.k3 * ((Complex.normSq a) ^ 3 - (Complex.normSq b) ^ 3)| := abs_add_three _ _ _
    _ = |θ.k1| * |Complex.normSq a - Complex.normSq b|
          + |θ.k2| * |(Complex.normSq a) ^ 2 - (Complex.normSq b) ^ 2|
          + |θ.k3| * |(Complex.normSq a) ^ 3 - (Complex.normSq b) ^ 3| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |θ.k1| * (2 * R * ‖a - b‖) + |θ.k2| * (4 * R ^ 3 * ‖a - b‖)
          + |θ.k3| * (6 * R ^ 5 * ‖a - b‖) := by gcongr
    _ = (2 * |θ.k1| * R + 4 * |θ.k2| * R ^ 3 + 6 * |θ.k3| * R ^ 5) * ‖a - b‖ := by ring

/-─────────────────────────────────────────────────────────────────────────────
  phi_bounded — ‖Φ θ z‖ ≤ M θ R for ‖z‖ ≤ R.
─────────────────────────────────────────────────────────────────────────────-/

theorem phi_bounded (θ : Coeffs) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖Φ θ z‖ ≤ M θ R := by
  have hrad := radial_bounded θ R hR z hz
  have hre : |z.re| ≤ R := le_trans (Complex.abs_re_le_norm z) hz
  have him : |z.im| ≤ R := le_trans (Complex.abs_im_le_norm z) hz
  have hns_nonneg : (0:ℝ) ≤ Complex.normSq z := Complex.normSq_nonneg z
  have hns_le : Complex.normSq z ≤ R ^ 2 := by
    rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hre_nonneg : (0:ℝ) ≤ z.re ^ 2 := sq_nonneg _
  have hre_sq_le : z.re ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs z.re, hre, abs_nonneg z.re]
  have him_sq_le : z.im ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs z.im, him, abs_nonneg z.im]
  have hMrad_nonneg : (0:ℝ) ≤ Mrad θ R := by unfold Mrad; positivity
  have hΦx : |(Φ θ z).re| ≤ Mrad θ R * R + 2 * |θ.p1| * R ^ 2 + 3 * |θ.p2| * R ^ 2 := by
    show |radial θ z * z.re + 2 * θ.p1 * z.re * z.im
        + θ.p2 * (Complex.normSq z + 2 * z.re ^ 2)| ≤ _
    calc |radial θ z * z.re + 2 * θ.p1 * z.re * z.im + θ.p2 * (Complex.normSq z + 2 * z.re ^ 2)|
        ≤ |radial θ z * z.re| + |2 * θ.p1 * z.re * z.im|
            + |θ.p2 * (Complex.normSq z + 2 * z.re ^ 2)| := abs_add_three _ _ _
      _ = |radial θ z| * |z.re| + 2 * |θ.p1| * |z.re| * |z.im|
            + |θ.p2| * (Complex.normSq z + 2 * z.re ^ 2) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
              abs_of_nonneg (by positivity : (0:ℝ) ≤ Complex.normSq z + 2 * z.re ^ 2)]
      _ ≤ Mrad θ R * R + 2 * |θ.p1| * R * R + |θ.p2| * (R ^ 2 + 2 * R ^ 2) := by
          gcongr
      _ = Mrad θ R * R + 2 * |θ.p1| * R ^ 2 + 3 * |θ.p2| * R ^ 2 := by ring
  have hΦy : |(Φ θ z).im| ≤ Mrad θ R * R + 3 * |θ.p1| * R ^ 2 + 2 * |θ.p2| * R ^ 2 := by
    show |radial θ z * z.im + θ.p1 * (Complex.normSq z + 2 * z.im ^ 2)
        + 2 * θ.p2 * z.re * z.im| ≤ _
    calc |radial θ z * z.im + θ.p1 * (Complex.normSq z + 2 * z.im ^ 2) + 2 * θ.p2 * z.re * z.im|
        ≤ |radial θ z * z.im| + |θ.p1 * (Complex.normSq z + 2 * z.im ^ 2)|
            + |2 * θ.p2 * z.re * z.im| := abs_add_three _ _ _
      _ = |radial θ z| * |z.im| + |θ.p1| * (Complex.normSq z + 2 * z.im ^ 2)
            + 2 * |θ.p2| * |z.re| * |z.im| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
              abs_of_nonneg (by positivity : (0:ℝ) ≤ Complex.normSq z + 2 * z.im ^ 2)]
      _ ≤ Mrad θ R * R + |θ.p1| * (R ^ 2 + 2 * R ^ 2) + 2 * |θ.p2| * R * R := by
          gcongr
      _ = Mrad θ R * R + 3 * |θ.p1| * R ^ 2 + 2 * |θ.p2| * R ^ 2 := by ring
  calc ‖Φ θ z‖ ≤ |(Φ θ z).re| + |(Φ θ z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (Mrad θ R * R + 2 * |θ.p1| * R ^ 2 + 3 * |θ.p2| * R ^ 2)
          + (Mrad θ R * R + 3 * |θ.p1| * R ^ 2 + 2 * |θ.p2| * R ^ 2) := by linarith
    _ = M θ R := by unfold M Mrad; ring

/-─────────────────────────────────────────────────────────────────────────────
  phi_lipschitz — ‖Φ θ a - Φ θ b‖ ≤ L θ R · ‖a-b‖ for ‖a‖,‖b‖ ≤ R.
─────────────────────────────────────────────────────────────────────────────-/

theorem phi_lipschitz (θ : Coeffs) (R : ℝ) (hR : 0 ≤ R) (a b : ℂ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖Φ θ a - Φ θ b‖ ≤ L θ R * ‖a - b‖ := by
  have hrad_a : |radial θ a| ≤ Mrad θ R := radial_bounded θ R hR a ha
  have hrad_diff : |radial θ a - radial θ b| ≤ Lrad θ R * ‖a - b‖ :=
    radial_lipschitz θ R hR a b ha hb
  have hns_diff : |Complex.normSq a - Complex.normSq b| ≤ 2 * R * ‖a - b‖ :=
    normSq_lipschitz R a b ha hb
  have hare : |a.re| ≤ R := le_trans (Complex.abs_re_le_norm a) ha
  have haim : |a.im| ≤ R := le_trans (Complex.abs_im_le_norm a) ha
  have hbre : |b.re| ≤ R := le_trans (Complex.abs_re_le_norm b) hb
  have hbim : |b.im| ≤ R := le_trans (Complex.abs_im_le_norm b) hb
  have hre_diff : |a.re - b.re| ≤ ‖a - b‖ := by
    have := Complex.abs_re_le_norm (a - b)
    simpa using this
  have him_diff : |a.im - b.im| ≤ ‖a - b‖ := by
    have := Complex.abs_im_le_norm (a - b)
    simpa using this
  have hMrad_nonneg : (0:ℝ) ≤ Mrad θ R := by unfold Mrad; positivity
  have hLrad_nonneg : (0:ℝ) ≤ Lrad θ R := by unfold Lrad; positivity
  have habnorm : (0:ℝ) ≤ ‖a - b‖ := norm_nonneg _
  -- Term 1 (shared shape for Φx and Φy): radial·coord product-difference bound
  have hterm1 : |radial θ a * a.re - radial θ b * b.re|
      ≤ (Mrad θ R + Lrad θ R * R) * ‖a - b‖ := by
    have heq : radial θ a * a.re - radial θ b * b.re
        = radial θ a * (a.re - b.re) + (radial θ a - radial θ b) * b.re := by ring
    rw [heq]
    calc |radial θ a * (a.re - b.re) + (radial θ a - radial θ b) * b.re|
        ≤ |radial θ a * (a.re - b.re)| + |(radial θ a - radial θ b) * b.re| := abs_add_le _ _
      _ = |radial θ a| * |a.re - b.re| + |radial θ a - radial θ b| * |b.re| := by
          rw [abs_mul, abs_mul]
      _ ≤ Mrad θ R * ‖a - b‖ + (Lrad θ R * ‖a - b‖) * R := by gcongr
      _ = (Mrad θ R + Lrad θ R * R) * ‖a - b‖ := by ring
  have hterm1' : |radial θ a * a.im - radial θ b * b.im|
      ≤ (Mrad θ R + Lrad θ R * R) * ‖a - b‖ := by
    have heq : radial θ a * a.im - radial θ b * b.im
        = radial θ a * (a.im - b.im) + (radial θ a - radial θ b) * b.im := by ring
    rw [heq]
    calc |radial θ a * (a.im - b.im) + (radial θ a - radial θ b) * b.im|
        ≤ |radial θ a * (a.im - b.im)| + |(radial θ a - radial θ b) * b.im| := abs_add_le _ _
      _ = |radial θ a| * |a.im - b.im| + |radial θ a - radial θ b| * |b.im| := by
          rw [abs_mul, abs_mul]
      _ ≤ Mrad θ R * ‖a - b‖ + (Lrad θ R * ‖a - b‖) * R := by gcongr
      _ = (Mrad θ R + Lrad θ R * R) * ‖a - b‖ := by ring
  -- Term 2 (shared shape): cross term a.re*a.im - b.re*b.im
  have hterm2 : |a.re * a.im - b.re * b.im| ≤ 2 * R * ‖a - b‖ := by
    have heq : a.re * a.im - b.re * b.im
        = a.re * (a.im - b.im) + (a.re - b.re) * b.im := by ring
    rw [heq]
    calc |a.re * (a.im - b.im) + (a.re - b.re) * b.im|
        ≤ |a.re * (a.im - b.im)| + |(a.re - b.re) * b.im| := abs_add_le _ _
      _ = |a.re| * |a.im - b.im| + |a.re - b.re| * |b.im| := by rw [abs_mul, abs_mul]
      _ ≤ R * ‖a - b‖ + ‖a - b‖ * R := by gcongr
      _ = 2 * R * ‖a - b‖ := by ring
  -- Term 3a: a.re² - b.re²
  have hterm3a : |a.re ^ 2 - b.re ^ 2| ≤ 2 * R * ‖a - b‖ := by
    have heq : a.re ^ 2 - b.re ^ 2 = (a.re - b.re) * (a.re + b.re) := by ring
    rw [heq, abs_mul]
    have hsum : |a.re + b.re| ≤ 2 * R := by
      calc |a.re + b.re| ≤ |a.re| + |b.re| := abs_add_le _ _
        _ ≤ R + R := by gcongr
        _ = 2 * R := by ring
    calc |a.re - b.re| * |a.re + b.re| ≤ ‖a - b‖ * (2 * R) := by
          apply mul_le_mul hre_diff hsum (abs_nonneg _) habnorm
      _ = 2 * R * ‖a - b‖ := by ring
  -- Term 3b: a.im² - b.im²
  have hterm3b : |a.im ^ 2 - b.im ^ 2| ≤ 2 * R * ‖a - b‖ := by
    have heq : a.im ^ 2 - b.im ^ 2 = (a.im - b.im) * (a.im + b.im) := by ring
    rw [heq, abs_mul]
    have hsum : |a.im + b.im| ≤ 2 * R := by
      calc |a.im + b.im| ≤ |a.im| + |b.im| := abs_add_le _ _
        _ ≤ R + R := by gcongr
        _ = 2 * R := by ring
    calc |a.im - b.im| * |a.im + b.im| ≤ ‖a - b‖ * (2 * R) := by
          apply mul_le_mul him_diff hsum (abs_nonneg _) habnorm
      _ = 2 * R * ‖a - b‖ := by ring
  -- Combine into Φx, Φy difference bounds
  have hΦx : |(Φ θ a).re - (Φ θ b).re| ≤ ((Mrad θ R + Lrad θ R * R) + 4 * |θ.p1| * R
      + 6 * |θ.p2| * R) * ‖a - b‖ := by
    have heq : (Φ θ a).re - (Φ θ b).re
        = (radial θ a * a.re - radial θ b * b.re)
          + 2 * θ.p1 * (a.re * a.im - b.re * b.im)
          + θ.p2 * ((Complex.normSq a - Complex.normSq b) + 2 * (a.re ^ 2 - b.re ^ 2)) := by
      show (radial θ a * a.re + 2 * θ.p1 * a.re * a.im + θ.p2 * (Complex.normSq a + 2 * a.re ^ 2))
          - (radial θ b * b.re + 2 * θ.p1 * b.re * b.im + θ.p2 * (Complex.normSq b + 2 * b.re ^ 2))
          = _
      ring
    rw [heq]
    calc |(radial θ a * a.re - radial θ b * b.re) + 2 * θ.p1 * (a.re * a.im - b.re * b.im)
          + θ.p2 * ((Complex.normSq a - Complex.normSq b) + 2 * (a.re ^ 2 - b.re ^ 2))|
        ≤ |radial θ a * a.re - radial θ b * b.re|
            + |2 * θ.p1 * (a.re * a.im - b.re * b.im)|
            + |θ.p2 * ((Complex.normSq a - Complex.normSq b) + 2 * (a.re ^ 2 - b.re ^ 2))| :=
          abs_add_three _ _ _
      _ = |radial θ a * a.re - radial θ b * b.re|
            + 2 * |θ.p1| * |a.re * a.im - b.re * b.im|
            + |θ.p2| * |(Complex.normSq a - Complex.normSq b) + 2 * (a.re ^ 2 - b.re ^ 2)| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ (Mrad θ R + Lrad θ R * R) * ‖a - b‖ + 2 * |θ.p1| * (2 * R * ‖a - b‖)
            + |θ.p2| * (2 * R * ‖a - b‖ + 2 * (2 * R * ‖a - b‖)) := by
          gcongr
          calc |(Complex.normSq a - Complex.normSq b) + 2 * (a.re ^ 2 - b.re ^ 2)|
              ≤ |Complex.normSq a - Complex.normSq b| + |2 * (a.re ^ 2 - b.re ^ 2)| := abs_add_le _ _
            _ = |Complex.normSq a - Complex.normSq b| + 2 * |a.re ^ 2 - b.re ^ 2| := by
                rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
            _ ≤ 2 * R * ‖a - b‖ + 2 * (2 * R * ‖a - b‖) := by gcongr
      _ = ((Mrad θ R + Lrad θ R * R) + 4 * |θ.p1| * R + 6 * |θ.p2| * R) * ‖a - b‖ := by ring
  have hΦy : |(Φ θ a).im - (Φ θ b).im| ≤ ((Mrad θ R + Lrad θ R * R) + 6 * |θ.p1| * R
      + 4 * |θ.p2| * R) * ‖a - b‖ := by
    have heq : (Φ θ a).im - (Φ θ b).im
        = (radial θ a * a.im - radial θ b * b.im)
          + θ.p1 * ((Complex.normSq a - Complex.normSq b) + 2 * (a.im ^ 2 - b.im ^ 2))
          + 2 * θ.p2 * (a.re * a.im - b.re * b.im) := by
      show (radial θ a * a.im + θ.p1 * (Complex.normSq a + 2 * a.im ^ 2) + 2 * θ.p2 * a.re * a.im)
          - (radial θ b * b.im + θ.p1 * (Complex.normSq b + 2 * b.im ^ 2) + 2 * θ.p2 * b.re * b.im)
          = _
      ring
    rw [heq]
    calc |(radial θ a * a.im - radial θ b * b.im)
          + θ.p1 * ((Complex.normSq a - Complex.normSq b) + 2 * (a.im ^ 2 - b.im ^ 2))
          + 2 * θ.p2 * (a.re * a.im - b.re * b.im)|
        ≤ |radial θ a * a.im - radial θ b * b.im|
            + |θ.p1 * ((Complex.normSq a - Complex.normSq b) + 2 * (a.im ^ 2 - b.im ^ 2))|
            + |2 * θ.p2 * (a.re * a.im - b.re * b.im)| := abs_add_three _ _ _
      _ = |radial θ a * a.im - radial θ b * b.im|
            + |θ.p1| * |(Complex.normSq a - Complex.normSq b) + 2 * (a.im ^ 2 - b.im ^ 2)|
            + 2 * |θ.p2| * |a.re * a.im - b.re * b.im| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ (Mrad θ R + Lrad θ R * R) * ‖a - b‖
            + |θ.p1| * (2 * R * ‖a - b‖ + 2 * (2 * R * ‖a - b‖))
            + 2 * |θ.p2| * (2 * R * ‖a - b‖) := by
          gcongr
          calc |(Complex.normSq a - Complex.normSq b) + 2 * (a.im ^ 2 - b.im ^ 2)|
              ≤ |Complex.normSq a - Complex.normSq b| + |2 * (a.im ^ 2 - b.im ^ 2)| := abs_add_le _ _
            _ = |Complex.normSq a - Complex.normSq b| + 2 * |a.im ^ 2 - b.im ^ 2| := by
                rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
            _ ≤ 2 * R * ‖a - b‖ + 2 * (2 * R * ‖a - b‖) := by gcongr
      _ = ((Mrad θ R + Lrad θ R * R) + 6 * |θ.p1| * R + 4 * |θ.p2| * R) * ‖a - b‖ := by ring
  calc ‖Φ θ a - Φ θ b‖ ≤ |(Φ θ a - Φ θ b).re| + |(Φ θ a - Φ θ b).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |(Φ θ a).re - (Φ θ b).re| + |(Φ θ a).im - (Φ θ b).im| := by
        rw [Complex.sub_re, Complex.sub_im]
    _ ≤ ((Mrad θ R + Lrad θ R * R) + 4 * |θ.p1| * R + 6 * |θ.p2| * R) * ‖a - b‖
          + ((Mrad θ R + Lrad θ R * R) + 6 * |θ.p1| * R + 4 * |θ.p2| * R) * ‖a - b‖ := by
        linarith
    _ = L θ R * ‖a - b‖ := by unfold L Mrad Lrad; ring

/-─────────────────────────────────────────────────────────────────────────────
  inverse_approx_error — the main theorem. ‖U_t(D_t(x)) - x‖ ≤ L·M·t².

  hx is the "buffer" hypothesis: x lives in a disk of radius R minus the
  worst-case displacement, guaranteeing D_t(x) also lands in the R-disk
  (a DERIVED fact below, not assumed separately). See
  docs/laps/bounded-inverse-approximation/ambiguity-register.md AMB-BIA-002.
─────────────────────────────────────────────────────────────────────────────-/

theorem inverse_approx_error (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R) (x : ℂ)
    (hx : ‖x‖ + |t| * M θ R ≤ R) :
    ‖U θ t (D θ t x) - x‖ ≤ L θ R * M θ R * t ^ 2 := by
  have hM_nonneg : (0:ℝ) ≤ M θ R := by unfold M; positivity
  have hL_nonneg : (0:ℝ) ≤ L θ R := by unfold L; positivity
  have habst_nonneg : (0:ℝ) ≤ |t| * M θ R := mul_nonneg (abs_nonneg t) hM_nonneg
  have hxR : ‖x‖ ≤ R := by linarith
  have hphi_x : ‖Φ θ x‖ ≤ M θ R := phi_bounded θ R hR x hxR
  have hsmul_norm : ∀ w : ℂ, ‖t • w‖ = |t| * ‖w‖ := by
    intro w; rw [Complex.real_smul, norm_mul]; simp
  have hDxR : ‖D θ t x‖ ≤ R := by
    unfold D
    calc ‖x + t • Φ θ x‖ ≤ ‖x‖ + ‖t • Φ θ x‖ := norm_add_le _ _
      _ = ‖x‖ + |t| * ‖Φ θ x‖ := by rw [hsmul_norm]
      _ ≤ ‖x‖ + |t| * M θ R := by gcongr
      _ ≤ R := hx
  have hid : U θ t (D θ t x) - x = t • (Φ θ x - Φ θ (D θ t x)) := by
    unfold U D
    simp only [Complex.real_smul]
    ring
  have hclose : ‖Φ θ x - Φ θ (D θ t x)‖ ≤ L θ R * ‖x - D θ t x‖ :=
    phi_lipschitz θ R hR x (D θ t x) hxR hDxR
  have hdiff : ‖x - D θ t x‖ = |t| * ‖Φ θ x‖ := by
    have heq : x - D θ t x = -(t • Φ θ x) := by unfold D; abel
    rw [heq, norm_neg, hsmul_norm]
  calc ‖U θ t (D θ t x) - x‖ = ‖t • (Φ θ x - Φ θ (D θ t x))‖ := by rw [hid]
    _ = |t| * ‖Φ θ x - Φ θ (D θ t x)‖ := hsmul_norm _
    _ ≤ |t| * (L θ R * ‖x - D θ t x‖) := by gcongr
    _ = |t| * (L θ R * (|t| * ‖Φ θ x‖)) := by rw [hdiff]
    _ ≤ |t| * (L θ R * (|t| * M θ R)) := by gcongr
    _ = L θ R * M θ R * t ^ 2 := by rw [← sq_abs t]; ring

/-─────────────────────────────────────────────────────────────────────────────
  smul_norm — ‖t • w‖ = |t| * ‖w‖. New top-level helper (previously a local
  `have` inside inverse_approx_error; that theorem is left unchanged, this
  is an additive promotion for reuse by the new theorems below). See
  docs/laps/inverse-injectivity/ambiguity-register.md AMB-II-002.
─────────────────────────────────────────────────────────────────────────────-/

theorem smul_norm (t : ℝ) (w : ℂ) : ‖t • w‖ = |t| * ‖w‖ := by
  rw [Complex.real_smul, norm_mul]; simp

/-─────────────────────────────────────────────────────────────────────────────
  D_eq_implies_eq — D θ t is injective on the disk ‖·‖ ≤ R, given the
  contraction condition |t| * L θ R < 1.

  This theorem establishes injectivity of D θ t only — it does not by
  itself construct or guarantee a preimage. Existence and uniqueness of
  the true inverse are established separately below by
  D_exists_unique_preimage, via a Banach fixed-point argument applied to
  inverseStep θ t y (using inverse_step_maps_disk/inverse_step_lipschitz
  as prerequisites). D_eq_implies_eq remains useful in its own right: it
  needs no completeness/fixed-point machinery at all, just the Lipschitz
  estimate.

  q := |t| * L θ R is a sufficient contraction threshold, not shown
  necessary: the same quantity governs inverse_step_lipschitz's contraction
  constant below, and — together with the self-map condition hy used by
  D_exists_unique_preimage — is exactly the hypothesis pair under which
  local existence and uniqueness are proved there. Larger distortions
  (q ≥ 1) may still be invertible; this is not shown either way.

  Scope: polynomial (non-rational) Brown-Conrady model only; no F/mm/pixel
  conversion; does not resolve docs/specification-questions.md SQ-CV-07.
─────────────────────────────────────────────────────────────────────────────-/

theorem D_eq_implies_eq
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R)
    (hcontract : |t| * L θ R < 1)
    (a b : ℂ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R)
    (hD : D θ t a = D θ t b) :
    a = b := by
  have heq : a - b = -(t • (Φ θ a - Φ θ b)) := by
    unfold D at hD
    simp only [Complex.real_smul] at hD ⊢
    linear_combination hD
  have hnormeq : ‖a - b‖ = |t| * ‖Φ θ a - Φ θ b‖ := by
    rw [heq, norm_neg, smul_norm]
  have hlip := phi_lipschitz θ R hR a b ha hb
  have hle : ‖a - b‖ ≤ |t| * L θ R * ‖a - b‖ := by
    calc ‖a - b‖ = |t| * ‖Φ θ a - Φ θ b‖ := hnormeq
      _ ≤ |t| * (L θ R * ‖a - b‖) := by gcongr
      _ = |t| * L θ R * ‖a - b‖ := by ring
  have hzero : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-─────────────────────────────────────────────────────────────────────────────
  D_injective_on_disk — thin Set.InjOn corollary of D_eq_implies_eq.
─────────────────────────────────────────────────────────────────────────────-/

theorem D_injective_on_disk (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R)
    (hcontract : |t| * L θ R < 1) :
    Set.InjOn (D θ t) {z : ℂ | ‖z‖ ≤ R} := by
  intro a ha b hb hDab
  exact D_eq_implies_eq θ R t hR hcontract a b ha hb hDab

/-─────────────────────────────────────────────────────────────────────────────
  inverseStep — the fixed-point iteration map T_y(z) = y - t • Φ_θ(z), used
  by a Picard-iteration-style Banach argument for the true inverse of
  D θ t. Named per docs/laps/inverse-injectivity/ambiguity-register.md
  AMB-II-001 (equivalent to the raw expression y - t • Φ θ z).

  inverse_step_maps_disk / inverse_step_lipschitz below establish exactly
  the two properties (self-mapping, contraction) a Banach fixed-point
  argument needs as HYPOTHESES to conclude T_y has a unique fixed point.
  Neither of these two theorems establishes that conclusion by itself —
  existence of the fixed point (the true inverse) is established
  separately below, by D_exists_unique_preimage, via Mathlib's
  ContractingWith.exists_fixedPoint' applied to the closed disk
  {z : ℂ | ‖z‖ ≤ R} (using IsClosed.isComplete directly on the set, not a
  bundled subtype — see docs/laps/inverse-existence/ambiguity-register.md
  AMB-IE-001).

  q := |t| * L θ R (inverse_step_lipschitz's contraction constant) is the
  same threshold as D_eq_implies_eq's hcontract — a sufficient contraction
  threshold (not shown necessary) that, together with the self-map
  condition hy, is exactly the hypothesis pair D_exists_unique_preimage
  uses to establish local existence and uniqueness below.

  Scope: polynomial (non-rational) Brown-Conrady model only; no F/mm/pixel
  conversion; does not resolve docs/specification-questions.md SQ-CV-07.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def inverseStep (θ : Coeffs) (t : ℝ) (y z : ℂ) : ℂ := y - t • Φ θ z

theorem inverse_step_maps_disk
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R) (y z : ℂ)
    (hy : ‖y‖ + |t| * M θ R ≤ R) (hz : ‖z‖ ≤ R) :
    ‖inverseStep θ t y z‖ ≤ R := by
  unfold inverseStep
  have hphi := phi_bounded θ R hR z hz
  calc ‖y - t • Φ θ z‖ ≤ ‖y‖ + ‖t • Φ θ z‖ := norm_sub_le _ _
    _ = ‖y‖ + |t| * ‖Φ θ z‖ := by rw [smul_norm]
    _ ≤ ‖y‖ + |t| * M θ R := by gcongr
    _ ≤ R := hy

theorem inverse_step_lipschitz
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R) (y a b : ℂ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖inverseStep θ t y a - inverseStep θ t y b‖ ≤ |t| * L θ R * ‖a - b‖ := by
  unfold inverseStep
  have heq : (y - t • Φ θ a) - (y - t • Φ θ b) = -(t • (Φ θ a - Φ θ b)) := by
    simp only [Complex.real_smul]; ring
  have hlip := phi_lipschitz θ R hR a b ha hb
  calc ‖(y - t • Φ θ a) - (y - t • Φ θ b)‖ = ‖t • (Φ θ a - Φ θ b)‖ := by
        rw [heq, norm_neg]
    _ = |t| * ‖Φ θ a - Φ θ b‖ := smul_norm _ _
    _ ≤ |t| * (L θ R * ‖a - b‖) := by gcongr
    _ = |t| * L θ R * ‖a - b‖ := by ring

/-─────────────────────────────────────────────────────────────────────────────
  D_exists_unique_preimage — local existence and uniqueness of the true
  inverse of D θ t on the buffered disk, via Mathlib's Banach fixed-point
  theorem applied to inverseStep θ t y.

  This is the theorem docs/laps/inverse-injectivity/ explicitly deferred
  ("existence of the true inverse... is a separate, deferred task, not
  attempted here"). It is a standalone mathematical fact about the
  polynomial (non-rational) Brown-Conrady model — it does NOT resolve
  docs/specification-questions.md SQ-CV-07 (the D-U/U-D interoperability
  question); that relevance is a separate, open matter, not established by
  this theorem.

  q := |t| * L θ R < 1 remains a SUFFICIENT contraction threshold (not
  shown necessary) for this local inversion result, together with the
  self-map condition hy.
─────────────────────────────────────────────────────────────────────────────-/

theorem D_exists_unique_preimage
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R)
    (hcontract : |t| * L θ R < 1)
    (y : ℂ) (hy : ‖y‖ + |t| * M θ R ≤ R) :
    ∃! z : ℂ, ‖z‖ ≤ R ∧ D θ t z = y := by
  have hM_nonneg : (0:ℝ) ≤ M θ R := by unfold M; positivity
  have hyR : ‖y‖ ≤ R := by nlinarith [mul_nonneg (abs_nonneg t) hM_nonneg]
  have hiff : ∀ z : ℂ, inverseStep θ t y z = z ↔ D θ t z = y := by
    intro z
    unfold inverseStep D
    constructor <;> (intro h; simp only [Complex.real_smul] at h ⊢; linear_combination -h)
  set s : Set ℂ := {z : ℂ | ‖z‖ ≤ R} with hs_def
  have hclosed : IsClosed s := by
    have hball : s = Metric.closedBall (0 : ℂ) R := by
      ext z; simp [hs_def, Metric.mem_closedBall, dist_eq_norm]
    rw [hball]; exact Metric.isClosed_closedBall
  have hcomplete : IsComplete s := hclosed.isComplete
  have hMapsTo : Set.MapsTo (inverseStep θ t y) s s := fun z hz =>
    inverse_step_maps_disk θ R t hR y z hy hz
  set K : NNReal := (|t| * L θ R).toNNReal with hK_def
  have hK0 : (0:ℝ) ≤ |t| * L θ R := by
    have hL_nonneg : (0:ℝ) ≤ L θ R := by unfold L; positivity
    exact mul_nonneg (abs_nonneg t) hL_nonneg
  have hKcoe : (K : ℝ) = |t| * L θ R := Real.coe_toNNReal _ hK0
  have hKlt1 : K < 1 := by
    rw [← NNReal.coe_lt_coe, hKcoe]; simpa using hcontract
  have hLip : LipschitzWith K (hMapsTo.restrict (inverseStep θ t y) s s) := by
    apply LipschitzWith.of_dist_le_mul
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Set.MapsTo.restrict, Subtype.dist_eq]
    rw [hKcoe]
    have := inverse_step_lipschitz θ R t hR y a b ha hb
    simpa [dist_eq_norm] using this
  have hContract : ContractingWith K (hMapsTo.restrict (inverseStep θ t y) s s) := ⟨hKlt1, hLip⟩
  have hys : y ∈ s := hyR
  have hedist : edist y (inverseStep θ t y y) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨z, hzs, hfz, _, _⟩ := hContract.exists_fixedPoint' hcomplete hMapsTo hys hedist
  refine ⟨z, ⟨hzs, (hiff z).mp hfz⟩, ?_⟩
  rintro w ⟨hws, hDw⟩
  have hfw : inverseStep θ t y w = w := (hiff w).mpr hDw
  have hzw : (⟨z, hzs⟩ : s) = (⟨w, hws⟩ : s) := by
    apply hContract.fixedPoint_unique' (x := (⟨z, hzs⟩ : s)) (y := (⟨w, hws⟩ : s))
    · show (hMapsTo.restrict (inverseStep θ t y) s s) ⟨z, hzs⟩ = ⟨z, hzs⟩
      exact Subtype.ext hfz
    · show (hMapsTo.restrict (inverseStep θ t y) s s) ⟨w, hws⟩ = ⟨w, hws⟩
      exact Subtype.ext hfw
  exact (congrArg Subtype.val hzw).symm
