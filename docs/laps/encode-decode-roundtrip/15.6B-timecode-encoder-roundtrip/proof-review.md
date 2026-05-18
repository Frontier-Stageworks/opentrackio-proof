# Proof Review — timecode-encoder-roundtrip (Slice 15.6B)

## Acceptance checks

| Check | Result |
|---|---|
| `lake env lean opentrackio_parser/TimecodeEncoder.lean` | exit 0, no warnings |
| `lake build TimecodeEncoder` | exit 0 |
| `encodePositiveRational_roundtrip` public, no `sorry` | ✓ |
| `encodeTimecode_roundtrip` public, no `sorry` | ✓ |

## Deviations from proof plan

None. Both theorems match the verified proof plan exactly.

## Key proof notes

**`encodePositiveRational_roundtrip`**: One `obtain` to destructure the record, then a
single `simp` call. `nat_repr_toNat?_some` fires on `n.repr.toNat?` via definitional
unfolding of `Nat.repr`.

**`encodeTimecode_roundtrip`**: Four cases from `rcases subFrame <;> rcases dropFrame`.
In each case, `simp` reduces the encoder, the nested `decodePositiveRational` roundtrip,
and all `lookup?` calls. The residual goals are `do`-bind chains with only `Except.ok`
values; these are definitionally equal to their RHS so `rfl` closes them.

**`r.num.repr` vs `r.num.toString`**: The encoder uses `r.num.repr` directly (not
`ToString.toString r.num`). Both are definitionally `Nat.repr r.num`, but using `.repr`
ensures `nat_repr_toNat?_some` matches syntactically without extra unfolding lemmas.

## Status: COMPLETE
