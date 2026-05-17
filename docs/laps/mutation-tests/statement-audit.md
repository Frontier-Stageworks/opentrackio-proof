---
name: mutation-tests-statement-audit
description: Statement audit for wrong_projection_offset_unscaled_forces_degenerate_relation
metadata:
  type: project
---

# Statement Audit — wrong_projection_offset_unscaled_forces_degenerate_relation

## Theorem text

```lean
theorem wrong_projection_offset_unscaled_forces_degenerate_relation
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = cx) :
    cx = (w / w_shader) * (cx - w_shader / 2)
```

## Classification

**Forces degeneracy** — not a direct contradiction. The wrong formula ΔPx = cx
is not universally inconsistent; it forces cx to lie on a specific curve
parameterized by w and w_shader.

## Audit checks

| Check | Result |
|-------|--------|
| Vacuous? | No — hconsist and hbug are satisfiable simultaneously (requires specific cx) |
| Over-strong hypotheses? | No — hw and hw_s are needed for field_simp; hconsist drives the derivation |
| Unused hypotheses? | None expected |
| Proxy property? | No — conclusion is exactly the value ΔPx must have per consistency, equated to cx |
| Theorem laundering? | No — uses existing proven theorem, does not restate it |
| Test-shaped? | No — universally quantified over x via hconsist |
| Implementation artifact? | No — pure mathematical claim about coordinate system parameters |
| Unreadable specification? | No |

## Derivation sketch

1. Apply `principal_point_conversion_necessary` to `hconsist` → get
   `hΔPx : ΔPx = (w / w_shader) * (cx - w_shader / 2)`
2. Rewrite with `hbug : ΔPx = cx` →
   `cx = (w / w_shader) * (cx - w_shader / 2)` ✓

The proof is one `obtain` + one `linarith` (or `rw`+`exact`).

## Risk: is the statement too weak?

No. This is the correct two-layer pattern. The second layer
(`wrong_projection_offset_unscaled_inconsistent`) adds the anti-degeneracy
hypothesis and closes to `False`. That theorem is deferred.

## Authorization

Statement approved as-is. No clarification needed.

---

# Statement Audit — buggy_projection_offset_missing_center_inconsistent

## Theorem text

```lean
theorem buggy_projection_offset_missing_center_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = (w / w_shader) * cx) :
    False
```

## Classification

**Direct contradiction** — This wrong formula (missing the centering term `-w_shader/2`)
is unconditionally inconsistent under `w ≠ 0`, `w_shader ≠ 0`.
Proved in `PrincipalPointConversion` as `buggy_principal_point_conversion_inconsistent`.
This theorem delegates to that existing proof.

## Audit

| Check | Result |
|-------|--------|
| Vacuity? | No — `buggy_principal_point_conversion_inconsistent` already establishes satisfiability is impossible |
| Overclaims? | No — direct contradiction is correct here per the paper |
| Delegation valid? | Yes — same parameters, same hypotheses |

---

# Statement Audit — wrong_projection_offset_unscaled_inconsistent

## Theorem text

```lean
theorem wrong_projection_offset_unscaled_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hnot : cx ≠ (w / w_shader) * (cx - w_shader / 2))
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = cx) :
    False
```

## Classification

**Contradiction under anti-degeneracy** — layer 2 of section B.
The anti-degeneracy hypothesis is exactly the negation of the forced equality
derived in layer 1. No extra assumptions needed.

## Audit

| Check | Result |
|-------|--------|
| Vacuous? | No — hnot is satisfiable (e.g. cx=0, w=2, w_shader=1 → forced eq is 0 = -1, so hnot holds) |
| Over-strong? | No — hnot is the minimal negation of the forced equality |
| Proxy? | No |

---

# Statement Audit — wrong_projection_offset_minus_half_forces_degenerate_relation

## Theorem text

```lean
theorem wrong_projection_offset_minus_half_forces_degenerate_relation
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = cx - w_shader / 2) :
    cx - w_shader / 2 = (w / w_shader) * (cx - w_shader / 2)
```

## Classification

**Forces degeneracy** — layer 1 of section C. The wrong formula is not universally
inconsistent; it forces the principal-point offset `cx - w_shader/2` to be a fixed
point of the scale `w/w_shader`.

## Derivation sketch

`principal_point_conversion_necessary` gives `ΔPx = (w/w_shader)*(cx - w_shader/2)`.
Rewrite with `hbug` → conclusion. Closed by `linarith`.

---

# Statement Audit — wrong_projection_offset_minus_half_inconsistent

## Theorem text

```lean
theorem wrong_projection_offset_minus_half_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hnot : cx - w_shader / 2 ≠ (w / w_shader) * (cx - w_shader / 2))
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = cx - w_shader / 2) :
    False
```

## Classification

**Contradiction under anti-degeneracy** — layer 2 of section C.
`hnot` is the negation of the forced equality. Proof: call layer 1 and apply `hnot`.

## Authorization

All four section A/B/C statements approved. No clarification needed.

---

# Statement Audit — wrong_focal_length_identity_forces_degeneracy (D layer 1)

## Theorem text

```lean
theorem wrong_focal_length_identity_forces_degeneracy
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)  (hw_s : w_shader ≠ 0)  (hfx  : fx ≠ 0)
    (hconsist : ∀ x : ℝ, fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : F = fx) :
    w = w_shader
```

## Classification

**Forces degeneracy** — consistency forces `F = (w/w_shader)*fx`; combined with `F = fx`
and `fx ≠ 0`, the scale `w/w_shader` must equal 1, i.e. `w = w_shader`.

## Audit

| Check | Result |
|-------|--------|
| Vacuous? | No — satisfiable when w = w_shader |
| Over-strong hypotheses? | `hfx` needed: without it, F = fx = 0 is consistent at any scale |
| Unused hypotheses? | None |
| Proxy? | No — conclusion is exactly the degenerate condition |

## Derivation

`obtain ⟨hF, _⟩` from `principal_point_conversion_necessary` → `hF : F = (w/w_shader)*fx`.
`rw [hbug] at hF` → `hF : fx = (w/w_shader)*fx`.
`mul_right_cancel₀ hfx` → `w/w_shader = 1`.
`div_eq_iff hw_s` → `w = w_shader`. ✓

---

# Statement Audit — wrong_focal_length_identity_inconsistent (D layer 2)

```lean
theorem wrong_focal_length_identity_inconsistent
    ... (hne : w ≠ w_shader) ... : False
```

**Classification:** Contradiction under anti-degeneracy. Calls layer 1. ✓

---

# Statement Audit — wrong_focal_length_inverted_inconsistent (E)

## Theorem text

```lean
theorem wrong_focal_length_inverted_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw_pos : 0 < w)  (hw_s_pos : 0 < w_shader)
    (hfx : fx ≠ 0)  (hne : w ≠ w_shader)
    (hconsist : ∀ x : ℝ, fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : F = (w_shader / w) * fx) :
    False
```

## Classification

**Direct contradiction under positivity** — over ℝ, `F = (w_shader/w)*fx` is satisfiable
when `w = -w_shader` (then `w/w_shader = -1 = w_shader/w`). Positivity rules that out,
making the contradiction unconditional under the listed assumptions.

## Audit

| Check | Result |
|-------|--------|
| Vacuous? | No — positivity + hne makes hypotheses satisfiable; they can't all hold simultaneously |
| Over-strong? | Positivity is the minimum needed to exclude `w = -w_shader` case |
| Unused? | None |
| Proxy? | No |

## Derivation

`hw = ne_of_gt hw_pos`, `hw_s = ne_of_gt hw_s_pos`.
`obtain ⟨hF, _⟩` → `hF : F = (w/w_shader)*fx`.
`rw [hbug] at hF` → `hF : (w_shader/w)*fx = (w/w_shader)*fx`.
`mul_right_cancel₀ hfx` → `w_shader/w = w/w_shader`.
`div_eq_div_iff hw hw_s` → `w_shader*w_shader = w*w`.
Factor `(w - w_shader)*(w + w_shader) = 0`. Case split on `mul_eq_zero`:
  - `w - w_shader = 0` → `hne` contradiction.
  - `w + w_shader = 0` → contradicts `hw_pos + hw_s_pos > 0`. ✓

## Authorization

All Task 3 statements approved.

---

# Statement Audit — Task 4: Radial Wrong-Power Mutations

## Pattern (all 12 theorems)

For each coefficient `li` with correct power `F^a` and wrong power `F^b`:
- Layer 1: `whole_radial_polynomial_iff` gives correct `li = ki/F^a`; combined with `li = ki/F^b` and `ki ≠ 0`, forces `F^a = F^b`.
- Layer 2: contradiction under `F^a ≠ F^b`.

## Numerator coefficients (k1 k2 k3, l1 l3 l5)

| Theorem | Wrong formula | Forced degeneracy |
|---------|--------------|-------------------|
| `wrong_l1_power_F4_*` | `l1 = k1/F^4` (correct: F^2) | `F^2 = F^4` |
| `wrong_l3_power_F2_*` | `l3 = k2/F^2` (correct: F^4) | `F^2 = F^4` |
| `wrong_l5_power_F4_*` | `l5 = k3/F^4` (correct: F^6) | `F^6 = F^4` |

## Denominator coefficients (k4 k5 k6, l2 l4 l6)

| Theorem | Wrong formula | Forced degeneracy |
|---------|--------------|-------------------|
| `wrong_l2_power_F4_*` | `l2 = k4/F^4` (correct: F^2) | `F^2 = F^4` |
| `wrong_l4_power_F2_*` | `l4 = k5/F^2` (correct: F^4) | `F^2 = F^4` |
| `wrong_l6_power_F4_*` | `l6 = k6/F^4` (correct: F^6) | `F^6 = F^4` |

## Proof shape (uniform across all 12)

```
obtain correct formula from whole_radial_polynomial_iff.mp
linarith: correct_formula = wrong_formula → ki/F^a = ki/F^b
div_eq_div_iff: ki * F^b = ki * F^a
mul_left_cancel₀ hki: F^b = F^a (or .symm for F^a = F^b)
```

## Audit (all theorems)

- Vacuous? No — satisfiable when F = ±1 (F^2 = F^4 case) or F = ±1 (F^6 = F^4 case at F=1)
- Over-strong? `hki ≠ 0` is minimal (without it, any F works)
- Proxy? No — the forced power equality is the exact algebraic consequence

## Authorization

All 12 Task 4 statements approved.

---

# Statement Audit — Task 5: Tangential Wrong-Power Mutations

## Pattern (all 8 theorems)

`whole_tangential_field_iff` gives `q1 = p1/F^2` and `q2 = p2/F^2`.
Each wrong formula forces a power degeneracy by the same `div_eq_div_iff` / `mul_left_cancel₀` step as the radial case.

Using `whole_tangential_field_iff` (δx only) rather than the 2D variant — δx alone suffices and using δx only is the weaker hypothesis, making each theorem strictly stronger.

| Theorem | Wrong formula | Forced degeneracy |
|---------|--------------|-------------------|
| `wrong_q1_power_F1_*` | `q1 = p1/F` (correct: F^2) | `F^2 = F` |
| `wrong_q1_power_F4_*` | `q1 = p1/F^4` (correct: F^2) | `F^2 = F^4` |
| `wrong_q2_power_F1_*` | `q2 = p2/F` (correct: F^2) | `F^2 = F` |
| `wrong_q2_power_F4_*` | `q2 = p2/F^4` (correct: F^2) | `F^2 = F^4` |

## Audit (all 8)

- Vacuous? No — `F^2 = F` when F = 0 or F = 1; excluded by `F ≠ 0` (F = 1 remains a genuine satisfying case).
- Over-strong hypotheses? `hpi ≠ 0` is minimal; `F ≠ 0` required for the division formulas.
- Proxy? No.

## Authorization

All 8 Task 5 statements approved.

---

# Statement Audit — Task 6: Coefficient-Swap Mutations

## Pattern (all 4 theorems)

A swapped coefficient uses the wrong parameter as the numerator.
The iff theorem gives the correct formula; equating correct and wrong forces the two parameters to be equal.

| Theorem | Wrong formula | Forced degeneracy |
|---------|--------------|-------------------|
| `wrong_l1_swapped_k2_*` | `l1 = k2/F^2` (correct: k1) | `k1 = k2` |
| `wrong_q1_swapped_p2_*` | `q1 = p2/F^2` (correct: p1) | `p1 = p2` |

## Note on unused hypotheses

The "swap" scenario has both q1 and q2 wrong simultaneously. Including both
`hwrong_q1 : q1 = p2/F^2` and `hwrong_q2 : q2 = p1/F^2` would create an
unused hypothesis (q2 alone suffices for the same conclusion by symmetry, and
either half suffices alone). Per LAPS audit, only the minimal hypothesis is included.
The q2 swap is rejected by the same argument with `obtain ⟨_, hq2⟩`.

## Proof shape

```
obtain correct coefficient from iff.mp
linarith: ki/F^2 = kj/F^2
div_eq_div_iff hF2 hF2: ki * F^2 = kj * F^2
mul_right_cancel₀ hF2: ki = kj
```

## Audit (all 4)

- Vacuous? No — `k1 = k2` (or `p1 = p2`) is the exact condition under which the swap is indistinguishable.
- Over-strong? No — no unnecessary hypotheses beyond `F ≠ 0`.
- Proxy? No.

## Authorization

All 4 Task 6 statements approved.
