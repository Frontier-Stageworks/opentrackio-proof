/-
  Pipeline/InverseConjugacyExample.lean

  A concrete, nontrivial, exact-rational instantiation of
  `opencv_openlensio_inverse_conjugate` (InverseConjugacyApplication.lean),
  demonstrating its hypotheses — specifically `hCVInv`, the explicit
  undischarged invertibility hypothesis — can be satisfied on a genuine
  nonempty domain for a NON-IDENTITY distortion map (nonzero k1, nonzero p1;
  not the all-zero-coefficient case). This is NOT a claim that
  `distortPointCV` is invertible on any open set, ball, or physically
  meaningful region — only that the hypothesis is non-vacuous: at least one
  genuine (point, inverse-on-a-singleton) instance exists where everything
  the specialized theorem requires can be exhibited and kernel-checked.

  Calibration used: k1 = 1 (all other radial coefficients 0), p1 = 1, p2 = 0
  (a pure single-term radial-plus-tangential lens — distorting, not the
  identity map), F = 2, fx = fy = 1, w = 2, ws = 1, h = 2, h_shader = 1 (so
  F = (w/ws)*fx = (2/1)*1 = 2, satisfying the shared-F requirement for both
  axes), cx = cy = 0 (so ΔPx = ΔPy = (w/ws)*(cx-ws/2) = 2*(0-1/2) = -1),
  evaluated at the normalised point ε₀ = (1, 0).
-/

import Pipeline.InverseConjugacyApplication

/-─────────────────────────────────────────────────────────────────────────────
  Hand-computed values (exact rationals, reproduced here as `norm_num`-checked
  facts, not floating point):

    CVmap ε₀ = (2, 1)       — distortXCV: R(1)=2, 2·1 + 2·1·1·0 + 0 = 2
                               distortYCV: 2·0 + 1·(1+0) + 2·0·1·0 = 1
    ScreenScale 2 (1,0) = (2, 0)
    OTImap (2,0) = (4, 2)   — l1 = 1/4, q1 = 1/2, q2 = 0
                               distortXOTI: R_oti(4) = (1+0.25·4)/1 = 2; 2·2+2·0.5·2·0+0 = 4
                               distortYOTI: 2·0 + 0.5·(4+0) + 2·0·2·0 = 2
    ScreenScale 2 (CVmap ε₀) = ScreenScale 2 (2,1) = (4, 2)  = OTImap (ScreenScale 2 ε₀) ✓
─────────────────────────────────────────────────────────────────────────────-/

example :
    Set.InvOn
      ((screenScaleEquiv 2 (by norm_num)) ∘ (fun _ => (⟨1, 0⟩ : SensorPoint))
        ∘ (screenScaleEquiv 2 (by norm_num)).symm)
      (OTImap (1/4) 0 0 0 0 0 (1/2) 0
        (by intro x' y'; norm_num))
      (screenScaleEquiv 2 (by norm_num) '' ({(⟨1, 0⟩ : SensorPoint)} : Set SensorPoint))
      (screenScaleEquiv 2 (by norm_num)
        '' ({(⟨2, 1⟩ : SensorPoint)} : Set SensorPoint)) := by
  apply opencv_openlensio_inverse_conjugate
    1 0 0 0 0 0 1 0                              -- k1..k6, p1, p2
    (1/4) 0 0 0 0 0 (1/2) 0                       -- l1..l6, q1, q2
    1 1 0 0 1 2 1 2 2 (-1) (-1)                   -- fx fy cx cy ws w h_shader h F ΔPx ΔPy
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by intro x' y'; norm_num) (by intro x' y'; norm_num)
    ({(⟨1, 0⟩ : SensorPoint)} : Set SensorPoint) ({(⟨2, 1⟩ : SensorPoint)} : Set SensorPoint)
    (fun _ => (⟨1, 0⟩ : SensorPoint))
  constructor
  · rintro ε (rfl : ε = ⟨1, 0⟩)
    show (⟨1, 0⟩ : SensorPoint) = (⟨1, 0⟩ : SensorPoint)
    rfl
  · rintro ε (rfl : ε = (⟨2, 1⟩ : SensorPoint))
    show CVmap 1 0 0 0 0 0 1 0 (by intro x' y'; norm_num) (⟨1, 0⟩ : SensorPoint)
        = (⟨2, 1⟩ : SensorPoint)
    apply SensorPoint.ext
    · simp only [CVmap, distortPointCV, distortXCV, sensorRadius]; norm_num
    · simp only [CVmap, distortPointCV, distortYCV, sensorRadius]; norm_num
