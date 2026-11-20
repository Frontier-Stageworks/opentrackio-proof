/-
  Pipeline/InverseConjugacyApplication.lean

  Specializes the abstract `conjugate_invOn` (InverseConjugacy.lean) to the
  actual OpenCV/OpenTrackIO forward maps (`distortPointCV`/`distortPointOTI`),
  using the two-dimensional forward conjugacy already proved in
  Pipeline/ForwardConjugacy.lean.

  READ BEFORE CITING. This file establishes a genuine inverse-direction
  relation between the exact mathematical forward maps `distortPointCV`
  (OpenCV) and `distortPointOTI` (OpenTrackIO's corrected forward model) — and
  nothing more. In particular it does NOT claim, state, or imply:

  - that OpenLensIO's independently-parameterized NATIVE undistortion
    function `U` (`undistortPoint`, openlensio_semantics/DistortionModel.lean,
    operating on RadialCoefficients/TangentialCoefficients — a different
    coefficient structure entirely) equals this exact inverse;
  - that a finite inverse Brown-Conrady coefficient set exists (it provably
    does not, in general — see audit/DISTORTION_DIRECTION_INTEROPERABILITY.md
    §7, the polynomial-degree and Abel–Ruffini obstructions);
  - that any consumer numerically computes this inverse correctly;
  - that floating-point evaluation of anything here is certified;
  - that OpenTrackIO interoperability (SQ-CV-07) is resolved, partially or
    otherwise.

  `distortPointCV`'s invertibility on any particular set is NOT proved
  anywhere in this repository (the existing injectivity results in
  `openlensio_semantics/InjectivityModel.lean` are for `undistortPoint`, a
  DIFFERENT function over a DIFFERENT coefficient structure — they do not
  apply to `distortPointCV`). The theorem below therefore takes that
  invertibility as an explicit, named, undischarged hypothesis
  (`hCVInv : Set.InvOn cv' (CVmap ...) A B`) rather than deriving or assuming
  it is available for free. See docs/specification-questions.md SQ-CV-07.
-/

import InverseConjugacy
import Pipeline.ForwardConjugacy

/-─────────────────────────────────────────────────────────────────────────────
  denom_sensorRadius_ne_zero

  Bridges a free, universally-quantified raw-real denominator-nonzero
  hypothesis (the form every pipeline theorem in this repository already
  takes) to the sensorRadius-squared form `distortPointCV`/`distortPointOTI`
  require as their domain hypothesis. Reused for both the CV side
  (a,b,c := k4,k5,k6) and the OTI side (a,b,c := l2,l4,l6, applied at an
  already-scaled point).
─────────────────────────────────────────────────────────────────────────────-/

theorem denom_sensorRadius_ne_zero
    (a b c : ℝ)
    (hden : ∀ x' y' : ℝ, 1 + a * (x' ^ 2 + y' ^ 2) + b * (x' ^ 2 + y' ^ 2) ^ 2
              + c * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0)
    (ε : SensorPoint) :
    1 + a * (sensorRadius ε) ^ 2 + b * (sensorRadius ε) ^ 4 + c * (sensorRadius ε) ^ 6 ≠ 0 := by
  have hr2 : (sensorRadius ε) ^ 2 = ε.x ^ 2 + ε.y ^ 2 := Real.sq_sqrt (by positivity)
  rw [show (sensorRadius ε) ^ 4 = ((sensorRadius ε) ^ 2) ^ 2 from by ring,
      show (sensorRadius ε) ^ 6 = ((sensorRadius ε) ^ 2) ^ 3 from by ring, hr2]
  exact hden ε.x ε.y

/-─────────────────────────────────────────────────────────────────────────────
  CVmap, OTImap

  distortPointCV/distortPointOTI packaged as plain `SensorPoint → SensorPoint`
  functions (closing over a global denominator-nonzero hypothesis to supply
  the per-point domain proof `distortPointCV`/`distortPointOTI` require) —
  needed because `conjugate_invOn` is stated over plain functions, not
  dependently-typed ones. `distortPointOTI`'s value does not depend on which
  proof of its domain hypothesis is supplied (Prop proof-irrelevance), so this
  repackaging changes nothing about what is computed.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def CVmap
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (hden : ∀ x' y' : ℝ, 1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
              + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0) :
    SensorPoint → SensorPoint :=
  fun ε => distortPointCV k1 k2 k3 k4 k5 k6 p1 p2 ε (denom_sensorRadius_ne_zero k4 k5 k6 hden ε)

noncomputable def OTImap
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (hdenOTI : ∀ x' y' : ℝ, 1 + l2 * (x' ^ 2 + y' ^ 2) + l4 * (x' ^ 2 + y' ^ 2) ^ 2
                 + l6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0) :
    SensorPoint → SensorPoint :=
  fun ε => distortPointOTI l1 l2 l3 l4 l5 l6 q1 q2 ε (denom_sensorRadius_ne_zero l2 l4 l6 hdenOTI ε)

/-─────────────────────────────────────────────────────────────────────────────
  screenScaleEquiv

  ScreenScale F is a genuine bijection on SensorPoint when F ≠ 0 (its own
  inverse is ScreenScale F⁻¹) — this is what lets `conjugate_invOn` apply at
  all (it requires a Equiv, not merely an injective map).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def screenScaleEquiv (F : ℝ) (hF : F ≠ 0) : SensorPoint ≃ SensorPoint where
  toFun := ScreenScale F
  invFun := ScreenScale F⁻¹
  left_inv := fun ε => by
    show ScreenScale F⁻¹ (ScreenScale F ε) = ε
    simp only [ScreenScale]
    exact SensorPoint.ext (by field_simp) (by field_simp)
  right_inv := fun ε => by
    show ScreenScale F (ScreenScale F⁻¹ ε) = ε
    simp only [ScreenScale]
    exact SensorPoint.ext (by field_simp) (by field_simp)

/-─────────────────────────────────────────────────────────────────────────────
  opencv_openlensio_inverse_conjugate

  The specialized inverse-conjugacy theorem. Given:
  - the same coefficient-conversion hypotheses
    `opencv_openlensio_forward_point_corrected` already requires (radial
    l=k/F^(2n), corrected tangential q=p/F, focal-length/offset relations for
    both axes with a SHARED F);
  - `hCVInv : Set.InvOn cv' (CVmap ...) A B` — an EXPLICIT, UNDISCHARGED
    hypothesis that `cv'` is a genuine two-sided inverse of OpenCV's forward
    map on sets A (domain) and B (range). No theorem anywhere in this
    repository currently proves this for `distortPointCV`/`CVmap` on any
    nonempty A, B — it is taken here exactly as what it is: a missing proof
    obligation, not a fact in evidence;

  concludes: `Set.InvOn (S∘cv'∘S.symm) (OTImap ...) (S''A) (S''B)`, where
  `S := screenScaleEquiv F hF` — i.e. the conjugated map `S∘cv'∘S.symm` is a
  genuine two-sided inverse of OpenTrackIO's forward map on the
  correspondingly `S`-scaled sets.

  This is the inverse-direction fact `opencv_openlensio_full_pipeline_pixel_corrected`
  does not by itself provide. It is NOT a claim about OpenLensIO's native `U`
  — see the file header.
─────────────────────────────────────────────────────────────────────────────-/

theorem opencv_openlensio_inverse_conjugate
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fx fy cx cy ws w h_shader h F ΔPx ΔPy : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0) (hh : h ≠ 0) (hhs : h_shader ≠ 0)
    (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F) (hq2 : q2 = p2 / F)
    (hF_eq_x : F = (w / ws) * fx) (hF_eq_y : F = (h / h_shader) * fy)
    (hΔPx : ΔPx = (w / ws) * (cx - ws / 2)) (hΔPy : ΔPy = (h / h_shader) * (cy - h_shader / 2))
    (hden : ∀ x' y' : ℝ,
        1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
          + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0)
    (hdenOTI : ∀ x' y' : ℝ,
        1 + l2 * (x' ^ 2 + y' ^ 2) + l4 * (x' ^ 2 + y' ^ 2) ^ 2
          + l6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0)
    (A B : Set SensorPoint) (cv' : SensorPoint → SensorPoint)
    (hCVInv : Set.InvOn cv' (CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden) A B) :
    Set.InvOn ((screenScaleEquiv F hF) ∘ cv' ∘ (screenScaleEquiv F hF).symm)
      (OTImap l1 l2 l3 l4 l5 l6 q1 q2 hdenOTI) (screenScaleEquiv F hF '' A)
      (screenScaleEquiv F hF '' B) := by
  apply conjugate_invOn (screenScaleEquiv F hF)
    (CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden) cv'
    (OTImap l1 l2 l3 l4 l5 l6 q1 q2 hdenOTI) A B _ hCVInv
  intro ε
  show OTImap l1 l2 l3 l4 l5 l6 q1 q2 hdenOTI (ScreenScale F ε)
      = ScreenScale F (CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden ε)
  exact opencv_openlensio_forward_point_corrected
    k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2
    fx fy cx cy ws w h_shader h F ΔPx ΔPy
    hw hws hh hhs hF hF_pos hl1 hl3 hl5 hl2 hl4 hl6 hq1 hq2
    hF_eq_x hF_eq_y hΔPx hΔPy hden ε
    (denom_sensorRadius_ne_zero k4 k5 k6 hden ε)
    (denom_sensorRadius_ne_zero l2 l4 l6 hdenOTI (ScreenScale F ε))
