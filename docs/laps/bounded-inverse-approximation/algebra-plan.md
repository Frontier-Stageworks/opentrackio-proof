# Algebra Plan — Bounded Inverse Approximation

Full hand-derivation of every constant and inequality chain, worked out
before any Lean code, per the algebra anti-spiral discipline (isolate
algebra, don't discover the bound by trial-and-error inside Lean).

## Notation

`r²(z) := Complex.normSq z = z.re² + z.im²` (equals `‖z‖²`). For `‖z‖ ≤ R`,
`r²(z) ≤ R²` (monotonicity of squaring on nonnegatives, `‖z‖ ≥ 0`).

## `radial_bounded`

`radial θ z = θ.k1·r²(z) + θ.k2·r²(z)² + θ.k3·r²(z)³`

For `‖z‖ ≤ R`, `0 ≤ R`: `r²(z) ≤ R²`, so `r²(z)² ≤ R⁴`, `r²(z)³ ≤ R⁶`
(monotonicity of `x ↦ xⁿ` on `[0,∞)`, via `pow_le_pow_left₀` chained, since
`r²(z) ≥ 0` always via `Complex.normSq_nonneg`).

```
|radial θ z| ≤ |θ.k1|·r²(z) + |θ.k2|·r²(z)² + |θ.k3|·r²(z)³   [triangle + abs_mul, r²≥0 so |r²ⁿ|=r²ⁿ]
             ≤ |θ.k1|·R² + |θ.k2|·R⁴ + |θ.k3|·R⁶
```

`Mrad θ R := |θ.k1|*R^2 + |θ.k2|*R^4 + |θ.k3|*R^6`. Local `have`/lemma, not
exported as a top-level definition (only `M`, `L` are — `Mrad` is an
implementation-detail helper reused between `phi_bounded`/`phi_lipschitz`).

## `radial_lipschitz`

Key sub-fact — difference of squares under a shared radius bound:

```
r²(a) - r²(b) = ‖a‖² - ‖b‖² = (‖a‖-‖b‖)(‖a‖+‖b‖)
|r²(a)-r²(b)| ≤ |‖a‖-‖b‖| · (‖a‖+‖b‖) ≤ ‖a-b‖ · 2R
```

using the reverse triangle inequality `|‖a‖-‖b‖| ≤ ‖a-b‖` (from
`norm_sub_norm_le` applied both ways, or `abs_norm_sub_norm_le` if that
exact name resolves — confirm at Stop 3) and `‖a‖+‖b‖ ≤ 2R` (from `‖a‖,‖b‖
≤ R`). Call this bound `Δr2 θ_free R := 2*R` (doesn't depend on θ — it's a
generic real-number fact about `r²` alone, but keeping the naming
`Δr2_bound` local for clarity).

```
r²(a)²-r²(b)² = (r²(a)-r²(b))(r²(a)+r²(b))
|r⁴(a)-r⁴(b)| ≤ |r²(a)-r²(b)| · (r²(a)+r²(b)) ≤ (2R·‖a-b‖) · 2R² = 4R³·‖a-b‖

r²(a)³-r²(b)³ = (r²(a)-r²(b))(r²(a)²+r²(a)r²(b)+r²(b)²)
|r⁶(a)-r⁶(b)| ≤ |r²(a)-r²(b)| · 3R⁴ ≤ (2R·‖a-b‖)·3R⁴ = 6R⁵·‖a-b‖
```

(Each step: standard difference-of-powers factoring, `ring`-checkable once
stated as an equality; then triangle/abs_mul + the previous step's bound,
`nlinarith`-closeable given the pieces as explicit hypotheses.)

```
|radial θ a - radial θ b|
  ≤ |θ.k1|·|r²(a)-r²(b)| + |θ.k2|·|r⁴(a)-r⁴(b)| + |θ.k3|·|r⁶(a)-r⁶(b)|
  ≤ |θ.k1|·2R·‖a-b‖ + |θ.k2|·4R³·‖a-b‖ + |θ.k3|·6R⁵·‖a-b‖
  = (2|θ.k1|R + 4|θ.k2|R³ + 6|θ.k3|R⁵) · ‖a-b‖
```

`Lrad θ R := 2*|θ.k1|*R + 4*|θ.k2|*R^3 + 6*|θ.k3|*R^5`.

## `phi_bounded`

```
Φx(z) = radial θ z · z.re + 2·p1·z.re·z.im + p2·(r²(z) + 2·z.re²)
|Φx(z)| ≤ |radial θ z|·|z.re| + 2|p1|·|z.re|·|z.im| + |p2|·(r²(z)+2z.re²)
        ≤ Mrad·R + 2|p1|·R·R + |p2|·(R²+2R²)
        = Mrad·R + 2|p1|R² + 3|p2|R²

Φy(z) = radial θ z · z.im + p1·(r²(z)+2z.im²) + 2·p2·z.re·z.im
|Φy(z)| ≤ Mrad·R + 3|p1|R² + 2|p2|R²     [symmetric]

‖Φ θ z‖ ≤ |Φx|+|Φy| ≤ 2·Mrad·R + 5|p1|R² + 5|p2|R²
        = 2R·(|k1|R²+|k2|R⁴+|k3|R⁶) + 5(|p1|+|p2|)R²
        = 2|k1|R³+2|k2|R⁵+2|k3|R⁷+5|p1|R²+5|p2|R²
```

`M θ R := 2*|k1|*R^3+2*|k2|*R^5+2*|k3|*R^7+5*|p1|*R^2+5*|p2|*R^2`. ✓ matches
`proof-plan.md`.

## `phi_lipschitz`

Product-difference identity, used repeatedly: for any `u₁,u₂,v₁,v₂ : ℝ`,
`u₁u₂ - v₁v₂ = u₁(u₂-v₂) + (u₁-v₁)v₂`, so
`|u₁u₂-v₁v₂| ≤ |u₁||u₂-v₂| + |u₁-v₁||v₂|` (triangle + abs_mul). This is a
one-line `have` provable by `ring` (for the equality) then `abs_add`/`abs_mul`
+ triangle (for the inequality) — cheap to reprove at each use site, so it
does NOT need to be a separate named lemma (unlike `radial_bounded`/
`radial_lipschitz`, which are genuinely reused across top-level theorems).

```
Φx(a)-Φx(b) = [radial θ a · a.re - radial θ b · b.re]
            + 2p1·[a.re·a.im - b.re·b.im]
            + p2·[(r²(a)-r²(b)) + 2(a.re²-b.re²)]

Term 1: |radial θ a·a.re - radial θ b·b.re|
  ≤ |radial θ a|·|a.re-b.re| + |radial θ a - radial θ b|·|b.re|
  ≤ Mrad·‖a-b‖ + Lrad·‖a-b‖·R        [|a.re-b.re| ≤ ‖a-b‖ via Complex.abs_re_le_norm (a-b)]
  = (Mrad + Lrad·R)·‖a-b‖

Term 2: |2p1·(a.re·a.im-b.re·b.im)|
  ≤ 2|p1|·(|a.re|·|a.im-b.im| + |a.re-b.re|·|b.im|)
  ≤ 2|p1|·(R·‖a-b‖ + ‖a-b‖·R) = 4|p1|R·‖a-b‖

Term 3: |p2|·|(r²(a)-r²(b)) + 2(a.re²-b.re²)|
  a.re²-b.re² = (a.re-b.re)(a.re+b.re), |a.re²-b.re²| ≤ ‖a-b‖·2R
  ≤ |p2|·(2R·‖a-b‖ + 2·2R·‖a-b‖) = 6|p2|R·‖a-b‖

|Φx(a)-Φx(b)| ≤ [(Mrad+Lrad·R) + 4|p1|R + 6|p2|R]·‖a-b‖

Φy(a)-Φy(b): symmetric, p1↔p2 roles swapped in the tangential part:
|Φy(a)-Φy(b)| ≤ [(Mrad+Lrad·R) + 6|p1|R + 4|p2|R]·‖a-b‖

‖Φθa-Φθb‖ ≤ |Φx(a)-Φx(b)|+|Φy(a)-Φy(b)|
          ≤ [2(Mrad+Lrad·R) + 10|p1|R + 10|p2|R]·‖a-b‖
```

Expand `2(Mrad+Lrad·R)`:
```
Mrad = |k1|R²+|k2|R⁴+|k3|R⁶
Lrad·R = 2|k1|R²+4|k2|R⁴+6|k3|R⁶
Mrad+Lrad·R = 3|k1|R²+5|k2|R⁴+7|k3|R⁶
2(Mrad+Lrad·R) = 6|k1|R²+10|k2|R⁴+14|k3|R⁶
```

`L θ R := 6*|k1|*R^2+10*|k2|*R^4+14*|k3|*R^6+10*|p1|*R+10*|p2|*R`. ✓ matches
`proof-plan.md`.

## Tripwire budget for this task

Per goal (each named `have`/lemma above): at most two `nlinarith`/`linarith`
attempts before falling back to an explicit `calc` with `ring`-verified
equalities interleaved with `abs`/monotonicity lemmas one step at a time. No
`field_simp` needed anywhere in this file (no division appears in `Φ`, `M`,
`L`, or the theorems — everything is polynomial/absolute-value, unlike the
`DistortionConversion*.lean` family). `positivity` is the preferred first
attempt for the two nonnegativity side facts (`0 ≤ M θ R`, `0 ≤ L θ R`)
before falling back to manual `add_nonneg`/`mul_nonneg` chains.
