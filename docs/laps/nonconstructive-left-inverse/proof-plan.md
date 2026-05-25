---
name: nonconstructive-left-inverse-proof-plan
description: Proof plan for NCL-00 (definitions + injectivity wrapper) and NCL-01 (main invFun theorem)
metadata:
  type: reference
---

# Proof Plan — Nonconstructive Left Inverse

**Task slug:** `nonconstructive-left-inverse`
**Date:** 2026-05-25

---

## Proof Engineering Level

- **NCL-00:** mapping concepts into Lean definitions + proving a fixed theorem
- **NCL-01:** proving a fixed theorem (one-liner term-mode)

---

## Slice NCL-00: Definitions and injectivity wrapper

### Goal

Define `DomainPoint k`, `undistortSub k p`, prove `domainPoint_nonempty`, and prove
`undistortSub_injective_pure_radial`.

### File

`openlensio_semantics/InjectivityModel.lean` — append after SLICE-UI-04 section.

### Definition plan

**`DomainPoint k`:**
```lean
def DomainPoint (k : RadialCoefficients) : Type :=
  {ε : SensorPoint // denominatorNonzero k (sensorRadius ε)}
```
Plain subtype. No special instances needed beyond Nonempty.

**`undistortSub k p`:**
```lean
noncomputable def undistortSub (k : RadialCoefficients) (p : TangentialCoefficients) :
    DomainPoint k → SensorPoint :=
  fun ⟨ε, h⟩ => undistortPoint k p ε h
```
The lambda destructs the subtype pair, forwarding ε and h to undistortPoint.
`noncomputable` because undistortPoint is noncomputable (real arithmetic).

**`domainPoint_nonempty`:**
```lean
instance domainPoint_nonempty (k : RadialCoefficients) : Nonempty (DomainPoint k) :=
  ⟨⟨⟨0, 0⟩, by simp [denominatorNonzero, sensorRadius]; norm_num⟩⟩
```
Mathematical content: at ε = ⟨0,0⟩, sensorRadius = 0, denominator = 1 ≠ 0.
Tactic uncertainty: `simp [sensorRadius]` may or may not reduce `Real.sqrt 0` to `0`
automatically. Fallback: unfold sensorRadius, apply Real.sqrt_zero, then simp/norm_num.
If `simp` alone doesn't close it, the chain is:
```lean
  unfold denominatorNonzero sensorRadius
  simp only [zero_pow, mul_zero, add_zero, Real.sqrt_zero]
  exact one_ne_zero
```

### Injectivity wrapper plan

**Opening move:** `intro ⟨ε₁, h₁⟩ ⟨ε₂, h₂⟩ hU`

This destructs the two `DomainPoint k` arguments and gets
`hU : undistortSub k p ⟨ε₁, h₁⟩ = undistortSub k p ⟨ε₂, h₂⟩`.

**Unfolding `undistortSub`:**
After intro, `hU` has type `undistortSub k p ⟨ε₁, h₁⟩ = undistortSub k p ⟨ε₂, h₂⟩`.
Unfolding `undistortSub` gives `undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂`.
Tactic options:
- `simp only [undistortSub] at hU` (may work since def unfolds by simp)
- `unfold undistortSub at hU` (direct unfold)
- `change undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂ at hU` (explicit)

**Hard step:** Applying `undistortPoint_injective_pure_radial` to get `ε₁ = ε₂`.
```lean
have heq : ε₁ = ε₂ :=
  undistortPoint_injective_pure_radial k p hp1 hp2 ε₁ ε₂ h₁ h₂
    (hR_all ε₁ h₁) hScaleInj hU
```
Then `Subtype.ext heq` closes the goal `⟨ε₁, h₁⟩ = ⟨ε₂, h₂⟩`.

**Full proof sketch:**
```lean
  intro ⟨ε₁, h₁⟩ ⟨ε₂, h₂⟩ hU
  simp only [undistortSub] at hU
  exact Subtype.ext
    (undistortPoint_injective_pure_radial k p hp1 hp2 ε₁ ε₂ h₁ h₂
      (hR_all ε₁ h₁) hScaleInj hU)
```

### Automation budget (NCL-00)

| Tactic | Use |
|---|---|
| `simp only [...]` | unfold `undistortSub`, `denominatorNonzero`, `sensorRadius` in Nonempty |
| `norm_num` | close `1 ≠ 0` in Nonempty |
| `Subtype.ext` | extract ε₁ = ε₂ → subtype equality |
| existing project lemma | `undistortPoint_injective_pure_radial` |

No broad automation; no `grind`; no global simp attributes.

---

## Slice NCL-01: Main theorem

### Goal

Prove `undistortSub_nonconstructive_left_inverse_pure_radial`.

### File

`openlensio_semantics/InjectivityModel.lean` — append after NCL-00 definitions.

### Proof plan

**Key Mathlib lemma:** `Function.Injective.invFun_apply`

Signature (Mathlib):
```lean
theorem Function.Injective.invFun_apply {α : Sort u} {β : Sort v} [Nonempty α]
    {f : α → β} (hf : Function.Injective f) {a : α} :
    Function.invFun f (f a) = a
```

Requires `[Nonempty (DomainPoint k)]` — provided by `domainPoint_nonempty` instance.

**Proof (term-mode):**
```lean
  (undistortSub_injective_pure_radial k p hp1 hp2 hR_all hScaleInj).invFun_apply
```

This is a single-line term-mode proof: apply injectivity → immediately get invFun_apply.

**Tactic-mode fallback (if term-mode has elaboration issues):**
```lean
  apply Function.Injective.invFun_apply
  exact undistortSub_injective_pure_radial k p hp1 hp2 hR_all hScaleInj
```

Or:
```lean
  have hinj := undistortSub_injective_pure_radial k p hp1 hp2 hR_all hScaleInj
  exact hinj.invFun_apply
```

**Potential issue:** Lean may need `εd` to be implicit or `invFun_apply` may need an
explicit `(a := εd)`. If the elaborator does not resolve the implicit argument, use:
```lean
  exact (undistortSub_injective_pure_radial k p hp1 hp2 hR_all hScaleInj).invFun_apply (a := εd)
```

### Automation budget (NCL-01)

Essentially no automation needed beyond applying one Mathlib theorem.

---

## Expected Hard Steps

| Step | Slice | Why hard |
|---|---|---|
| `domainPoint_nonempty` proof | NCL-00 | `Real.sqrt_zero` may need explicit unfolding; `simp` depth on subtype goals can be finicky |
| unfolding `undistortSub` in `hU` | NCL-00 | Definitional equality for lambda destructure may require `simp only` or `unfold` |
| `Function.Injective.invFun_apply` elaboration | NCL-01 | Implicit `{a}` in the lemma may require explicit annotation |

---

## Non-Goals

- Right inverse / surjectivity (deferred; separate campaign)
- Discharging `hScaleInj` (deferred; next-steps item 5)
- General-p (tangential) version (deferred; blocked by on-circle restriction of UI-03)
- Adding `[Inhabited]` or `[DecidableEq]` instances for `DomainPoint` (not needed for invFun_apply)

---

## Lean Check Requirements

- **NCL-00:** `lake env lean openlensio_semantics/InjectivityModel.lean` after adding definitions and injectivity wrapper. Must exit 0, no warnings.
- **NCL-01:** Same command after adding main theorem. Must exit 0, no warnings.
- **After both slices:** `lake build` must exit 0, no warnings.
