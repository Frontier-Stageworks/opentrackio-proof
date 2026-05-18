# Proof Review — synchronization-encoder (Slice 15.7)

## Acceptance checks

| Check | Result |
|---|---|
| `lake env lean opentrackio_parser/SynchronizationEncoder.lean` | exit 0, no warnings |
| `lake build SynchronizationEncoder` | exit 0 |
| `encodeSynchronization_roundtrip` public, no `sorry` | ✓ |

## Deviations from capsule

**Scope correction at Stop 2**: `encodeSyncOffsets` and `encodeSyncOffsets_roundtrip`
were already present in `LeafEncoders.lean` (Slice 15.1). The capsule was updated before
Stop 2 to reflect the actual scope — one encoder, one theorem.

## Key proof notes

The 64-case split (`rcases source` × 4, three optional field splits × 2 each) is handled
entirely by one chained `rcases ... <;> rcases ... <;> ... <;> simp [...] <;> rfl`.

The simp set uses the three nested roundtrip lemmas (`encodePositiveRational_roundtrip`,
`encodeSyncOffsets_roundtrip`, `encodePtpInfo_roundtrip`) as rewrite rules rather than
expanding the nested encoder definitions. This keeps each of the 64 sub-goals small and
avoids explosive unfolding of `encodePtpInfo`'s 8-field object.

`Except.map` is needed because optional fields are decoded via `(decodeFoo vj).map some`;
with the roundtrip lemma rewriting `decodeFoo (encodeFoo x)` to `.ok x`, simp needs
`Except.map` to then reduce `(.ok x).map some` to `.ok (some x)`.

`<;> rfl` closes the residual `do`-bind goals (definitionally equal to their RHS).

## Status: COMPLETE
