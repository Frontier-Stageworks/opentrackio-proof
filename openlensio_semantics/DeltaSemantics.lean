/-
  DeltaSemantics.lean — SLICE-OL-09

  Defines SensorPoint vector operations and proves the ΔP/ΔC coordinate
  translation theorems from OpenLensIO §3 Eqs (12) and (13).

  AMB-OL-002 resolution (load-bearing): Eq (13) is the authority.
    ε_d = ε'_d + ΔP  (addition, not the inline text's subtraction near Eq (10))
  Mathematical check: with Eq (13) sign,
    U(ε_d − ΔC − ΔP) = U((ε'_d + ΔP) − ΔC − ΔP) = U(ε'_d − ΔC)  ✓ (matches Eq 10)

  If AMB-OL-002 is resolved differently, all three theorems below need sign changes.
-/

import LensSemantics

/-─────────────────────────────────────────────────────────────────────────────
  addSensorPoints / subSensorPoints

  Component-wise vector addition and subtraction for SensorPoint.
  Used to model the ΔP and ΔC coordinate offsets from §1.5, §3.
─────────────────────────────────────────────────────────────────────────────-/

def addSensorPoints (p q : SensorPoint) : SensorPoint :=
  ⟨p.x + q.x, p.y + q.y⟩

def subSensorPoints (p q : SensorPoint) : SensorPoint :=
  ⟨p.x - q.x, p.y - q.y⟩

/-─────────────────────────────────────────────────────────────────────────────
  deltaP_characterisation

  Formal statement of §3 Eq (12): ε_u = ε'_u + ΔP.
  Stated as a roundtrip: shifting by ΔP and then unshifting returns the
  original FOV-form undistorted coordinate. Sign per AMB-OL-002.
─────────────────────────────────────────────────────────────────────────────-/

theorem deltaP_characterisation (ε'_u ΔP : SensorPoint) :
    subSensorPoints (addSensorPoints ε'_u ΔP) ΔP = ε'_u := by
  ext <;> simp [addSensorPoints, subSensorPoints]

/-─────────────────────────────────────────────────────────────────────────────
  deltaC_characterisation

  Formal statement of §3 Eq (13): ε_d = ε'_d + ΔP.
  Same algebraic form as deltaP_characterisation but for the distorted
  coordinate pair. Kept separate to document the distinct paper equation.
─────────────────────────────────────────────────────────────────────────────-/

theorem deltaC_characterisation (ε'_d ΔP : SensorPoint) :
    subSensorPoints (addSensorPoints ε'_d ΔP) ΔP = ε'_d := by
  ext <;> simp [addSensorPoints, subSensorPoints]

/-─────────────────────────────────────────────────────────────────────────────
  distortion_center_translation_commutes

  Key consistency fact connecting Eq (4) and Eq (10) via Eq (13):
    (ε'_d + ΔP) − ΔC − ΔP = ε'_d − ΔC

  The ΔP terms cancel, so both parametrisations feed U the same
  distortion-centred argument. This is why Eq (4) and Eq (10) agree.
─────────────────────────────────────────────────────────────────────────────-/

theorem distortion_center_translation_commutes (ε'_d ΔP ΔC : SensorPoint) :
    subSensorPoints (subSensorPoints (addSensorPoints ε'_d ΔP) ΔC) ΔP =
    subSensorPoints ε'_d ΔC := by
  ext <;> simp [addSensorPoints, subSensorPoints] <;> ring
