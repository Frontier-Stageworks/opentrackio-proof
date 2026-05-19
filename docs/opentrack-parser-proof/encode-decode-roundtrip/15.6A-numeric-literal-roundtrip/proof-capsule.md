# Proof Capsule — numeric-literal-roundtrip (Slice 15.6A)

## Intent

Prove one reusable bridge theorem connecting `Nat.repr` to `String.toNat?`, matching
exactly the expression produced by `encodePositiveRational`. All later encoder slices
that encode `Nat` fields via `.number r.num.toString` will import and reuse this theorem.

## Scope

- One public theorem: `nat_repr_toNat?_some`
- Private helper lemmas as needed (bounded in scope to `Nat.toDigits 10` and `String.Slice`)
- No encoders or decoders defined here

## Frozen formal statement

```lean
theorem nat_repr_toNat?_some (n : Nat) :
    n.repr.toNat? = some n
```

## Why this matches the encoder expression

`encodePositiveRational` will produce `.number r.num.toString`. The chain is:
  `r.num.toString`
  = `ToString.toString r.num`   (by `ToString Nat` instance)
  = `Nat.repr r.num`            (by `Nat.repr` = `ToString.toString` for `Nat`)
  = `String.ofList (Nat.toDigits 10 r.num)`

`decodePositiveRational` calls `ns.toNat?` on the number string.
The roundtrip requires `(r.num.repr).toNat? = some r.num`, which is one application of
`nat_repr_toNat?_some`. Used once for `num`, once for `den`.

## Proof sub-goals (after unfolding)

After unfolding `Nat.repr`, `String.toNat?`, `String.Slice.toNat?`:

```
⊢ (if (String.ofList (Nat.toDigits 10 n)).toSlice.isNat = true then
      some (String.Slice.foldl
              (fun acc c => if c = '_' then acc else acc * 10 + (c.toNat - '0'.toNat))
              0
              (String.ofList (Nat.toDigits 10 n)).toSlice)
    else none) = some n
```

Two helper lemmas required:
1. `nat_toDigits_isNat` — `(String.ofList (Nat.toDigits 10 n)).toSlice.isNat = true`
2. `nat_toDigits_foldl` — the foldl accumulator over the decimal chars recovers `n`

The hard step is `nat_toDigits_foldl`: connecting the char-level fold to
`Nat.ofDigits_digits`. Stop and report if this expands into broad `Nat.toDigits` internals.

## Stop rules

- If any helper lemma requires more than induction on `n` plus `Nat.ofDigits_digits`,
  stop and report the exact helper lemmas still needed.
- Do not mix this proof with `encodePositiveRational_roundtrip` or `encodeTimecode_roundtrip`.
- Do not change `decodePositiveRational` or the encoder encoding shape.

## File

`opentrackio_parser/NumericLiteralRoundtrip.lean`
