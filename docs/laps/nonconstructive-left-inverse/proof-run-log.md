---
name: nonconstructive-left-inverse-proof-run-log
description: Proof run log for NCL-00 (definitions + injectivity wrapper) and NCL-01 (main invFun theorem)
metadata:
  type: reference
---

# Proof Run Log — Nonconstructive Left Inverse

**Task slug:** `nonconstructive-left-inverse`

---

## NCL-00: Definitions and injectivity wrapper

### Attempt 1 — 2026-05-25

**Code written:**

```lean
def DomainPoint (k : RadialCoefficients) : Type :=
  {ε : SensorPoint // denominatorNonzero k (sensorRadius ε)}

noncomputable def undistortSub (k : RadialCoefficients) (p : TangentialCoefficients) :
    DomainPoint k → SensorPoint :=
  fun ⟨ε, h⟩ => undistortPoint k p ε h

instance domainPoint_nonempty (k : RadialCoefficients) : Nonempty (DomainPoint k) :=
  ⟨⟨⟨0, 0⟩, by simp [denominatorNonzero, sensorRadius, Real.sqrt_zero]⟩⟩

theorem undistortSub_injective_pure_radial ... (proof via have hU' + Subtype.ext)
```

**Lean command:**
```sh
cd /Users/markstalzer/github/opentrackio-proof && lake env lean openlensio_semantics/InjectivityModel.lean
```

**Result:** exit 0, no warnings, first attempt.

```sh
lake env lean openlensio_semantics/InjectivityModel.lean
# exit: 0 (no output)
```

---

## NCL-01: Main theorem (same Lean check)

### Attempt 1 — 2026-05-25

**Code written:**

```lean
theorem undistortSub_nonconstructive_left_inverse_pure_radial ... (εd : DomainPoint k) :
    Function.invFun (undistortSub k p) (undistortSub k p εd) = εd :=
  Function.leftInverse_invFun
    (undistortSub_injective_pure_radial k p hp1 hp2 hR_all hScaleInj) εd
```

Key Mathlib lemma: `Function.leftInverse_invFun` (not `Function.Injective.invFun_apply`
as originally speculated in proof-plan.md — `leftInverse_invFun` is the correct name
in Lean 4 Mathlib).

**Lean command:**
```sh
lake env lean openlensio_semantics/InjectivityModel.lean
```

**Result:** exit 0, no warnings, first attempt.

**lake build result:** exit 0, 3316 jobs, 0 warnings.
