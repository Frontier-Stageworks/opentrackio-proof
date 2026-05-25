---
name: nonconstructive-left-inverse-proof-review
description: Proof review for NCL-00 (DomainPoint, undistortSub, injectivity wrapper) and NCL-01 (nonconstructive left-inverse theorem)
metadata:
  type: reference
---

# Proof Review — Nonconstructive Left Inverse

**Task slug:** `nonconstructive-left-inverse`
**Review date:** 2026-05-25
**Repo HEAD at review:** `494947f8f84032390c560148d87fe8ce2c115a87`
**Modified file:** `openlensio_semantics/InjectivityModel.lean` (uncommitted at review time)

---

## REVIEW EVIDENCE

**Repo path:** `/Users/markstalzer/github/opentrackio-proof`

**Lean command run:**
```sh
cd /Users/markstalzer/github/opentrackio-proof && lake env lean openlensio_semantics/InjectivityModel.lean
```
**Result:** exit 0, no output, no warnings.

**lake build command run:**
```sh
cd /Users/markstalzer/github/opentrackio-proof && lake build
```
**Result:** exit 0, "Build completed successfully (3316 jobs).", no warnings.

**Forbidden construct scan:**
```sh
grep -n "sorry\|admit\|^unsafe\|^partial" openlensio_semantics/InjectivityModel.lean
```
**Result:** 0 matches in proof code.

**Declaration inventory (new declarations in NCL-00 + NCL-01):**
```sh
grep -n "^def \|^noncomputable def \|^instance \|^theorem \|^lemma " openlensio_semantics/InjectivityModel.lean | tail -10
```

| Line | Kind | Name |
|---|---|---|
| ~323 | def | `DomainPoint` |
| ~326 | noncomputable def | `undistortSub` |
| ~330 | instance | `domainPoint_nonempty` |
| ~333 | theorem | `undistortSub_injective_pure_radial` |
| ~363 | theorem | `undistortSub_nonconstructive_left_inverse_pure_radial` |

**Total new proof-bearing declarations: 2** (the two theorems).
New definitions/instances: 3 (DomainPoint, undistortSub, domainPoint_nonempty).

---

## DECLARATION-BY-DECLARATION REVIEW

### `DomainPoint k`

```lean
def DomainPoint (k : RadialCoefficients) : Type :=
  {ε : SensorPoint // denominatorNonzero k (sensorRadius ε)}
```

**Intended meaning:** The type of sensor points where the radial denominator is nonzero.

**Review:**
- Plain Lean subtype — the standard Lean/Mathlib idiom for domain restriction.
- Encodes exactly `denominatorNonzero k (sensorRadius ε)` — neither more nor less than the per-point domain predicate already used throughout the project.
- No invariants deferred or hidden.
- No illegal states representable — the subtype proof argument is in `Prop`.

**Verdict:** pass.

---

### `undistortSub k p`

```lean
noncomputable def undistortSub (k : RadialCoefficients) (p : TangentialCoefficients) :
    DomainPoint k → SensorPoint :=
  fun ⟨ε, h⟩ => undistortPoint k p ε h
```

**Intended meaning:** `undistortPoint k p` wrapped as a plain function on `DomainPoint k`.

**Review:**
- `noncomputable` correct: `undistortPoint` is noncomputable (real arithmetic).
- Lambda destructures the subtype pair, forwarding `ε` and `h` to `undistortPoint k p ε h` — definitionally equal to the application.
- Does not introduce any new semantic content beyond lifting the proof-dependent argument into the subtype.

**Verdict:** pass.

---

### `domainPoint_nonempty k`

```lean
instance domainPoint_nonempty (k : RadialCoefficients) : Nonempty (DomainPoint k) :=
  ⟨⟨⟨0, 0⟩, by simp [denominatorNonzero, sensorRadius, Real.sqrt_zero]⟩⟩
```

**Intended meaning:** Provides the `[Nonempty (DomainPoint k)]` instance required by `Function.leftInverse_invFun` / `Function.invFun`.

**Review:**
- Mathematical content: `⟨0, 0⟩ : SensorPoint` is always a domain point.
  - `sensorRadius ⟨0,0⟩ = Real.sqrt (0² + 0²) = Real.sqrt 0 = 0`
  - `denominatorNonzero k 0 = (1 + k.k2·0² + k.k4·0⁴ + k.k6·0⁶ ≠ 0) = (1 ≠ 0)` ✓ for all k.
- Proof: `simp [denominatorNonzero, sensorRadius, Real.sqrt_zero]` reduces all arithmetic and closes with `1 ≠ 0`.
- Compiled without error — Lean's kernel accepted the term.

**Verdict:** pass.

---

### `undistortSub_injective_pure_radial`

```lean
theorem undistortSub_injective_pure_radial
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0)
    (hR_all : ∀ (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε)),
        radialTerm k (sensorRadius ε) h ≠ 0)
    (hScaleInj : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
        (radialScale k r₁) ^ 2 * r₁ ^ 2 = (radialScale k r₂) ^ 2 * r₂ ^ 2 → r₁ = r₂) :
    Function.Injective (undistortSub k p) := by
  intro ⟨ε₁, h₁⟩ ⟨ε₂, h₂⟩ hU
  have hU' : undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂ := hU
  exact Subtype.ext
    (undistortPoint_injective_pure_radial k p hp1 hp2 ε₁ ε₂ h₁ h₂
      (hR_all ε₁ h₁) hScaleInj hU')
```

**Intended claim:** `undistortSub k p` is injective for p = 0 given global R ≠ 0 and hScaleInj.

**Proof shape:**
1. `intro ⟨ε₁, h₁⟩ ⟨ε₂, h₂⟩ hU` — destructs two `DomainPoint k` arguments and gets the function-equality hypothesis.
2. `have hU' := hU` — coerces `hU` to the `undistortPoint`-level equality (definitional equality of `undistortSub` applied to the subtype pair).
3. `exact Subtype.ext (undistortPoint_injective_pure_radial ...)` — applies the UI-01 result to get `ε₁ = ε₂`, then `Subtype.ext` converts this to the `DomainPoint k` equality.

**Hard step:** `have hU' : undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂ := hU` — relies on definitional equality of `undistortSub k p ⟨ε₁, h₁⟩` with `undistortPoint k p ε₁ h₁`. Lean accepts this, confirming the lambda pattern-match reduces definitionally.

**Semantic checks:**
- Statement laundering: No. The proof directly delegates to `undistortPoint_injective_pure_radial` (UI-01); the conclusion `Function.Injective (undistortSub k p)` is exactly the lifted version of UI-01's `ε₁ = ε₂` conclusion.
- Vacuity: No. Both `hR_all` and `hScaleInj` are satisfiable (all-zero k case).
- Over-strong hypotheses: `hR_all` is the minimal global lift of UI-01's per-point `hR₁`. `hScaleInj` is the same as UI-01.
- Automation hiding hard step: No automation is used beyond `Subtype.ext`. The hard step (delegation to UI-01) is explicit.

**Verdict:** pass.

---

### `undistortSub_nonconstructive_left_inverse_pure_radial`

```lean
theorem undistortSub_nonconstructive_left_inverse_pure_radial
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0)
    (hR_all : ∀ (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε)),
        radialTerm k (sensorRadius ε) h ≠ 0)
    (hScaleInj : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
        (radialScale k r₁) ^ 2 * r₁ ^ 2 = (radialScale k r₂) ^ 2 * r₂ ^ 2 → r₁ = r₂)
    (εd : DomainPoint k) :
    Function.invFun (undistortSub k p) (undistortSub k p εd) = εd :=
  Function.leftInverse_invFun
    (undistortSub_injective_pure_radial k p hp1 hp2 hR_all hScaleInj) εd
```

**Intended claim:** `Function.invFun (undistortSub k p)` is a left inverse of `undistortSub k p` at every domain point. This is D ∘ U = id for the pure-radial case.

**Proof shape:**
- Term-mode one-liner.
- Key Mathlib lemma: `Function.leftInverse_invFun (hf : Injective f) : LeftInverse (invFun f) f`
  (Mathlib.Logic.Function.Basic). Instantiated at `εd` to give the pointwise equation.
- `[Nonempty (DomainPoint k)]` resolved automatically from `domainPoint_nonempty` instance.

**Semantic checks:**
- Statement laundering: No. The conclusion is the pointwise D ∘ U = id — exactly `invFun f (f a) = a` instantiated at `a = εd`. The Lean kernel verified this via `Function.leftInverse_invFun`.
- Proxy property: No. The statement IS D ∘ U = id. Not a weakened or proxy version.
- Left-only claim: Yes, by design. The theorem name includes `left_inverse`. Right inverse (U ∘ D = id) is not claimed and is deferred.
- Vacuity: No. `hR_all` and `hScaleInj` are satisfiable. `domainPoint_nonempty` provides a concrete witness.
- Over-strong hypotheses: `hScaleInj` is carried from UI-01, documented as open. `hR_all` is minimal.
- Automation hiding hard step: Not applicable — single Mathlib lemma application. The hard step (injectivity) is in `undistortSub_injective_pure_radial`, which was reviewed above.
- Comment/formal alignment: Header comment correctly states "D ∘ U = id on DomainPoint k (pure-radial, p = 0)" — matches the formal statement.

**Relation to spec:** OpenLensIO Eqs (5) and (11) define D = U⁻¹ as a mathematical object. This theorem proves D(U(ε)) = ε where D = `Function.invFun (undistortSub k p)`. The spec's claim is formally instantiated for the pure-radial subcase. The nonconstructive character (Classical.choice) is not a gap — it matches the spec's existence claim without requiring a closed-form formula (AMB-UI-001).

**Verdict:** pass.

---

## CLASSIFICATION CONSISTENCY CHECK

- Lean file check: run — exit 0, no warnings.
- lake build: run — exit 0, 3316 jobs, no warnings.
- Forbidden constructs: scan run — 0 hits.
- Theorem inventory: complete (5 new items listed above; 2 proof-bearing).
- Statement-intent alignment: verified for all 5 items.
- Definition-model alignment: verified (DomainPoint and undistortSub correctly model the intended concepts).
- Semantic risks: none detected.

---

## Required Action

- **Semantic proof action:** none
- **Verification/build action:** none — `lake env lean` and `lake build` both run and passed.
- **Process evidence action:** commit uncommitted Lean changes to InjectivityModel.lean.

---

## Verdict

**Accepted.**

`lake build` passes at HEAD `494947f8f84032390c560148d87fe8ce2c115a87` (modified InjectivityModel.lean, uncommitted). All 5 new declarations (2 defs, 1 instance, 2 theorems) are kernel-checked, semantically sound, and aligned with the intended claim. No forbidden constructs. The main theorem `undistortSub_nonconstructive_left_inverse_pure_radial` formally proves D ∘ U = id for the pure-radial case using `Function.leftInverse_invFun`. Both open hypotheses (hR_all, hScaleInj) are correctly carried and documented as honest preconditions (AMB-NCL-003) rather than proof gaps.
