---
name: undistort-invertibility-statement-audit
description: Statement audit for the undistort invertibility campaign — checks theorem shapes for vacuity, alignment, and semantic risk
metadata:
  type: reference
---

# Statement Audit — Undistort Invertibility Campaign

**Task slug:** `undistort-invertibility`
**Phase:** Stop 1
**Date:** 2026-05-24

---

## SLICE-UI-00: `undistortPoint_injective_zero_tangential`

### Theorem text (proposed)

```lean
theorem undistortPoint_injective_zero_tangential
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0)
    (ε₁ ε₂ : SensorPoint)
    (h₁ : denominatorNonzero k (sensorRadius ε₁))
    (h₂ : denominatorNonzero k (sensorRadius ε₂))
    (hR : radialTerm k (sensorRadius ε₁) h₁ ≠ 0)
    (hSameR : sensorRadius ε₁ = sensorRadius ε₂)
    (hU : undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂) :
    ε₁ = ε₂
```

### Audit checks

**Is it vacuous?**
No. The hypotheses are satisfiable. Example witness: `k` all-zero (→ R = 1 ≠ 0, denom = 1 ≠ 0),
`p` all-zero, any ε₁ ε₂ with the same radius but different angles. The conclusion
`ε₁ = ε₂` is then non-trivially forced by `hU`.

**Is `hR` necessary?**
Yes. If R = 0 then U maps every point on the circle to the origin, so distinct ε₁ ≠ ε₂
would both undistort to `⟨0, 0⟩`, making `hU` true while `ε₁ = ε₂` is false.
`hR` is a genuine necessary condition, not a convenience hypothesis.

**Is `hSameR` necessary?**
Yes for this slice. Without `hSameR`, the two points might have different radii and thus
different radial factors R₁ ≠ R₂. The equation R₁*ε₁ = R₂*ε₂ does not force ε₁ = ε₂
unless we can equate R₁ and R₂. `hSameR` is the minimal hypothesis that allows this.
Removing `hSameR` is the goal of SLICE-UI-01 (which requires a separate monotonicity argument).

**Is `h₁` necessary?**
Yes. `radialTerm` requires a proof of `denominatorNonzero` to be called. Without it, `undistortX`
and `undistortY` are not well-typed.

**Is `h₂` necessary?**
Yes. Same reason for ε₂.

**Is the conclusion too weak?**
No. The conclusion `ε₁ = ε₂` is the full injectivity statement for this restricted case.
It is the strongest conclusion available from these hypotheses.

**Is the theorem over-strong (requires hypotheses it doesn't need)?**
`hp1`, `hp2` are used to zero out the tangential terms. Without them, the theorem is
false in general (tangential terms create cross-coupling between x and y that can break
injectivity on a circle). They are necessary.

**Semantic alignment with user intent?**
The user's intent is to prove "invertibility" of U. This theorem is one direction of
injectivity (a necessary condition). It should be clearly labeled as a first step, not
the final claim. The name `injective_zero_tangential` is accurate and honest about scope.

**Proxy property risk?**
Low. The theorem directly proves the property of interest (injectivity) under stated
restrictions. It is not a proxy for a different property.

**Audit verdict:** PASS — theorem is non-vacuous, hypotheses are necessary, conclusion
matches stated claim, scope restriction is honest and documented.

---

## Future Slice Statements (Not Yet Audited — Require Authorization)

### SLICE-UI-01: Pure radial injectivity without `hSameR`

Proposed: Remove `hSameR`, replace with a monotonicity condition on R(r)*r.

**Requires audit when authorized.** Key risk: the monotonicity condition may be difficult
to state without introducing new definitions. The theorem may need a coefficient-domain
predicate (e.g., "R(r)*r is strictly increasing on [0, ∞)") that requires real-analysis
machinery. Do not state this theorem until the monotonicity approach is audited.

### SLICE-UI-02: Radial term positivity

Proposed: Under specific coefficient sign conditions, R(r) > 0 for all r in the domain.

**Requires audit when authorized.** This would allow dropping `hR` from UI-00 in
scenarios where the coefficient conditions are known.

### SLICE-UI-03: Full model (tangential) injectivity

Proposed: Injectivity with p₁, p₂ arbitrary (non-zero tangential).

**Requires audit when authorized.** Will require Jacobian determinant analysis.
Very high difficulty. Do not approach until UI-01 and UI-02 are complete and reviewed.

### SLICE-UI-04: Existence of local inverse

Proposed: Via the Implicit Function Theorem (IFT) from Mathlib, U has a local inverse
near any point where the Jacobian is nonzero.

**Requires audit when authorized.** Mathlib IFT availability and applicability to this
model must be checked before planning. Do not approach until UI-03 is complete.
