# Proof Capsule — rational-decoder (Slice 5)

## Parent

Slice 5 of `opentrack-parser-verification`.

## Task classification

**Medium** — one decoder with several rejection paths, one soundness theorem.

## Intent

Decode a `JsonValue` (expected: `{ "num": ..., "denom": ... }` object) into a
`PositiveRational`. Prove that any successfully decoded value has a positive
real value.

## Resolved ambiguities used

- A1: rational fields are `JsonValue.object` with required `"num"` and `"denom"`
  sub-fields, each a `JsonValue.number` whose string parses as a positive `Nat`.
- A7: invariants (`num_pos`, `den_pos`) live in the type; soundness delegates
  to `positive_rational_toReal_pos` from Slice 1.

## Formal statements (frozen)

```lean
def decodePositiveRational (j : JsonValue) : Except DecodeError PositiveRational

theorem decodePositiveRational_sound :
  decodePositiveRational j = .ok r → 0 < r.toReal
```

## Proof note

`positive_rational_toReal_pos r` (Slice 1) covers any `r : PositiveRational`
by construction. The decoder constructs `r` only when `0 < n` and `0 < d`
are established as decision proofs (`if hn : 0 < n`), which become the
struct fields `num_pos` and `den_pos`. The hypothesis `_h` is intentionally
unused in the soundness proof.

## Forbidden

- No `sorry`.
- No changes to Slices 1–4C.
- No field strings for fields outside `decodePositiveRational`'s own sub-fields
  (`"num"`, `"denom"`).
