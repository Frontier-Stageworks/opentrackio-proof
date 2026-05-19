# Proof Review — rational-decoder (Slice 5)

## Kernel status

`lake env lean opentrackio_parser/RationalDecoder.lean` — exit 0, no warnings.  
`lake build RationalDecoder` — exit 0 (3.5s, 3289 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No field strings outside `"num"` and `"denom"`.
- No changes to Slices 1–4C.

## Statement audit

| Name | Intended | Captured |
|---|---|---|
| `decodePositiveRational` | `.object` → lookup `"num"` and `"denom"` → parse as positive Nats → `PositiveRational` | Yes |
| `decodePositiveRational_sound` | successful decode → `0 < r.toReal` | Yes |

## Semantic review

**`decodePositiveRational`:** Complete rejection coverage:
- Non-object → `expectedObject`
- `"num"` absent → `missingField "num"`
- `"denom"` absent (num present) → `missingField "denom"`
- `"num"` not `.number` → `expectedNumber`
- `"denom"` not `.number` (num is a number) → `expectedNumber`
- `"num"` string not a Nat → `invalidRational "num"`
- `"denom"` string not a Nat → `invalidRational "denom"`
- `"num"` parses as 0 → `invalidRational "num"`
- `"denom"` parses as 0 → `invalidRational "denom"`
- Both positive Nats → `.ok { num := n, den := d, num_pos := hn, den_pos := hd }`

The simultaneous lookup `match j.lookup? "num", j.lookup? "denom" with` is
top-to-bottom: `none, _` catches all cases where "num" is absent (including when
"denom" is also absent), so "num" is always reported first when both are missing.

**Key construction step:** `if hn : 0 < n` and `if hd : 0 < d` are decision
proofs. The `hn` and `hd` bindings become the struct fields `num_pos` and
`den_pos` directly — no separate proof obligation at the call site.

**`decodePositiveRational_sound`:** Non-vacuous: the theorem asserts the decoder
never produces a non-positive rational. `positive_rational_toReal_pos r` covers
all `r : PositiveRational` by the type invariants. The hypothesis `_h` is
intentionally unused for the same reason as in 4B and 4C.

## Hard step identification

The key construction steps are the decision proofs `if hn : 0 < n` and `if hd : 0 < d`
in the decoder body. These are standard Lean 4 `if h : P then ... else ...` syntax
that binds the proof `h : P` in the positive branch. No hard proof steps in the
theorem itself.

## Anti-pattern scan

- No bare `simp`.
- No `norm_num` or `linarith`.
- No global annotations added.
- No proxy property proved — `0 < r.toReal` is the exact intended predicate.

## Contract compliance

1. ✅ `decodePositiveRational` compiles.
2. ✅ `decodePositiveRational_sound` compiles without `sorry`.
3. ✅ `lake env lean` exit 0, no warnings.
4. ✅ `lake build RationalDecoder` exit 0.
5. ✅ No field strings outside `"num"` and `"denom"`.
6. ✅ No excluded scope introduced.
