/-
  DeltaSemantics.lean — SLICE-OL-09

  Defines SensorPoint vector operations and proves the ΔP/ΔC coordinate
  translation theorems from OpenLensIO §3 Eqs (12) and (13).

  Eq (13): ε_d = ε'_d + ΔP.
  Inline text near Eq (10) (verified against PDF): also says "where ε_d = ε'_d + ΔP" —
  identical form to Eq (13). The specification is self-consistent and unambiguous.
  Mathematical check: substituting Eq (13) into Eq (4):
    U(ε_d − ΔC − ΔP) = U((ε'_d + ΔP) − ΔC − ΔP) = U(ε'_d − ΔC)  ✓ (matches Eq 10)

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
  original FOV-form undistorted coordinate. Sign per Eq (13).

  ⚠ Formal note (audit finding VAC-01): deltaP_characterisation and
  deltaC_characterisation are formally α-equivalent — they prove the same
  algebraic fact `sub(add(a, b), b) = a` with different bound variable names
  and identical proof scripts. The duplication is intentional: Eq (12) and
  Eq (13) apply the same algebraic relationship to different coordinate-space
  roles (undistorted vs. distorted coordinates respectively). A single theorem
  would suffice formally; both are retained for equation-traceability to the
  paper. The semantic distinction is interpretive, not algebraic.
─────────────────────────────────────────────────────────────────────────────-/

theorem deltaP_characterisation (ε'_u ΔP : SensorPoint) :
    subSensorPoints (addSensorPoints ε'_u ΔP) ΔP = ε'_u := by
  ext <;> simp [addSensorPoints, subSensorPoints]

/-─────────────────────────────────────────────────────────────────────────────
  deltaC_characterisation

  Formal statement of §3 Eq (13): ε_d = ε'_d + ΔP.
  Same algebraic form as deltaP_characterisation but for the distorted
  coordinate pair. Kept separate to document the distinct paper equation.

  ⚠ Formal note (audit finding VAC-01): this theorem is formally α-equivalent
  to deltaP_characterisation (same statement, same proof, different variable
  names). The coordinate-role distinction — undistorted (ε'_u / Eq 12) vs.
  distorted (ε'_d / Eq 13) — is interpretive, not algebraic. Both theorems are
  retained for paper-equation traceability. See deltaP_characterisation note.
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
