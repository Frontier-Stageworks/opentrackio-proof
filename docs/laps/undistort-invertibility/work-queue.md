---
name: undistort-invertibility-work-queue
description: Work queue for the undistort invertibility campaign — injectivity and invertibility of undistortPoint, staged from on-circle restriction to full model
metadata:
  type: reference
---

# Work Queue — Undistort Invertibility Campaign

**Task slug:** `undistort-invertibility`
**Source plan:** openlensio-semantics SLICE-OL-DEFER-03 + user intent (2026-05-24)
**Lean files involved:** `openlensio_semantics/InjectivityModel.lean` (new), `lakefile.toml`
**Task size:** large
**Status:** SLICE-UI-00 and SLICE-UI-01 complete — SLICE-UI-02 pending user authorization

---

## Reason for Classification as Large

- Multiple theorem families (on-circle, pure-radial, full-model, D-definition)
- Multiple proof domains (algebraic cancellation, real-analysis monotonicity, Jacobian, IFT)
- Both new file creation and theorem proving
- Fundamental constraint (AMB-UI-001): no closed-form D for general Brown-Conrady means
  each slice must be authorized separately before proceeding
- High-risk later slices cannot be planned until the early slices' results are known

---

## Global Objective

Prove that the Brown-Conrady undistortion map `undistortPoint` is injective under
progressively weaker restrictions, ultimately establishing as much of the invertibility
property as the model and Mathlib machinery permit.

The campaign begins with the most restricted, most achievable result (on-circle injectivity
for zero tangential) and proceeds only as far as the proof machinery allows.

---

## Non-Goals (Explicitly Deferred)

- Full global invertibility for the general Brown-Conrady model (no closed-form D exists)
- Proving D ∘ U = id for a closed-form D without first defining D for a restricted class
- Floating-point or executable invertibility proofs
- Continuity or topology of U beyond what Mathlib can close in a bounded proof effort

---

## Theorem Families

| Family | Purpose | Proof domain | Main risk | Status |
|---|---|---|---|---|
| On-circle injectivity (zero tangential) | Injectivity of U on circles, p = 0 | Algebraic cancellation | Low | **complete** |
| Global pure-radial injectivity | Injectivity of U globally, p = 0 | Real-analysis monotonicity | High | **complete** |
| Radial term positivity | R(r) > 0 under coefficient conditions | Polynomial sign analysis | Medium | **complete** |
| Full-model injectivity (with tangential) | Global injectivity with nonzero p | Jacobian determinant | Very high | pending |
| Local invertibility (IFT-based) | Local inverse near regular points | IFT from Mathlib | Very high | pending |

---

## Slices

| ID | Purpose | Likely files | Main ambiguity risk | Status |
|---|---|---|---|---|
| SLICE-UI-00 | On-circle injectivity, p = 0, R ≠ 0 | `InjectivityModel.lean`, `lakefile.toml` | None blocking | **complete** |
| SLICE-UI-01 | Global pure-radial injectivity, p = 0 | `InjectivityModel.lean` | AMB-UI-004 (monotonicity) | **complete** |
| SLICE-UI-02 | Radial term positivity under coefficient conditions | `InjectivityModel.lean` | AMB-UI-003 | **complete** |
| SLICE-UI-03 | Full-model injectivity with tangential | `InjectivityModel.lean` | Jacobian approach TBD | pending |
| SLICE-UI-04 | Existence of local inverse (IFT) or D for restricted class | TBD | AMB-UI-005 | pending |

---

## Slice Details

### SLICE-UI-00 — On-circle injectivity, zero tangential (SELECTED)

**Purpose:** Prove `undistortPoint_injective_zero_tangential`.

**Likely files:**
- New: `openlensio_semantics/InjectivityModel.lean`
- Modified: `lakefile.toml` (add `InjectivityModel` target)

**Definitions expected:** None (no new definitions; uses existing `undistortPoint`, `radialTerm`, `denominatorNonzero`)

**Theorems expected:**
- `undistortPoint_injective_zero_tangential` (primary)

**Forbidden scope:**
- No new definitions of D
- No changes to existing DistortionModel.lean definitions
- No deferred slices (UI-01 through UI-04)

**Main ambiguity risk:** None blocking. `hSameR` sidesteps all the hard real-analysis.

**Completion condition:**
- `lake env lean openlensio_semantics/InjectivityModel.lean` exits 0
- No `sorry`, no warnings
- Proof review confirms semantic alignment
- work-queue updated

**Stop condition:**
- Proof fails twice on the same subgoal → PROOF STOP
- Theorem requires changing `undistortX` or `undistortY` definition → stop and report

---

### SLICE-UI-01 — Global pure-radial injectivity (COMPLETE)

**Purpose:** Prove injectivity of U without the `hSameR` restriction, when p = 0.

**Approach:** Square the component equalities to derive R₁²·r₁² = R₂²·r₂², then apply
a caller-supplied `hScaleInj` hypothesis (r ↦ (R(r)·r)² is injective on [0,∞)) to
recover `sensorRadius ε₁ = sensorRadius ε₂`, then reduce to UI-00.

**Lean check:** exit 0, no warnings, first attempt.

**AMB-UI-004 resolution:** The monotonicity approach (HasDerivAt + f' > 0) is not needed.
The `hScaleInj` hypothesis cleanly defers the radial-factor injectivity to the caller;
SLICE-UI-02 will supply a concrete discharge of this hypothesis under coefficient conditions.

---

### SLICE-UI-02 — Radial term positivity (DEFERRED)

**Purpose:** Derive `R(r) > 0` from coefficient conditions, enabling drop of `hR` from the
injectivity hypotheses.

**Gate:** May not begin until:
1. UI-01 is complete or abandoned
2. AMB-UI-003 resolved (what coefficient conditions to use)
3. User explicitly authorizes

---

### SLICE-UI-03 — Full model injectivity (DEFERRED)

**Purpose:** Injectivity with nonzero tangential coefficients. Likely requires computing
the 2×2 Jacobian matrix of U and showing its determinant is positive.

**Gate:** May not begin until:
1. UI-01 and UI-02 are complete
2. Jacobian approach is feasibility-analyzed
3. User explicitly authorizes

---

### SLICE-UI-04 — Existence of local inverse or D for restricted class (DEFERRED)

**Purpose:** Either use Mathlib IFT for a local invertibility statement, or define D
explicitly for the constant-radial-factor subclass and prove D ∘ U = id.

**Gate:** May not begin until:
1. UI-00 through UI-02 are complete
2. AMB-UI-005 resolved (existential vs concrete D)
3. User explicitly authorizes

---

## Selected First Slice

**SLICE-UI-00** is first because:
- It has no hard analysis dependencies (no derivatives, no IFT, no Jacobian)
- It is the minimal achievable injectivity result that is meaningful
- It closes the open mathematical gap for the on-circle case
- It succeeds or fails cleanly, informing whether the approach generalizes to UI-01

**What is explicitly deferred from UI-00:**
- All of UI-01 through UI-04
- Any definition of D
- Any claim beyond on-circle injectivity with p = 0

---

## Next-Slice Contract

The agent may not begin SLICE-UI-02 until:
1. SLICE-UI-01 Lean file compiles without `sorry` or warnings — ✓ done
2. Proof review passes — ✓ done
3. `work-queue.md` is updated to mark UI-01 complete — ✓ done
4. User explicitly authorizes UI-02
