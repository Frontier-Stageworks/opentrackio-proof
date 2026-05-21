# Proof Review — transform-encoder (Slice 15.2)

## Acceptance criteria

| Criterion | Result |
|---|---|
| `lake env lean opentrackio_parser/TransformEncoder.lean` — exit 0, no warnings | PASS |
| `lake build TransformEncoder` — exit 0 | PASS |
| No `sorry` or forbidden constructs | PASS |
| All three roundtrip theorems green | PASS |

## Review

**Encoders**: All three follow the straightforward pattern — fixed-field objects for
`Vec3` and `Rotation`; dynamic list via `Option.map ... |>.toList` for `Transform`'s
optional `scale` and `id` fields.

**Proof deviations from plan**:
1. `simp [..., decodeNumberField]` left residual `Except.bind` chains (all `.ok` steps).
   Fixed by appending `; rfl` to each proof. The chains are definitionally equal and `rfl`
   uses kernel reduction to close them. This pattern applies to all future decoder roundtrip
   proofs involving `do` blocks.
2. `dif_pos hns` correctly discharged the `if h : nsval ≠ ""` guard in the `id = some ns`
   case; `obtain ⟨nsval, hns⟩ := ns` was necessary to expose `hns` as a named hypothesis.

**Established patterns for remaining slices**:
- `simp [encode, decode, JsonValue.lookup?, ...]; rfl` for all `do`-block decoder roundtrips.
- `dif_pos h` for discharging `dite` guards on `NonemptyString` fields.
- `obtain ⟨val, h⟩ := ns` before `simp [dif_pos h]` when `NonemptyString` appears.

## Verdict

ACCEPTED. Two proof deviations resolved at Stop 3; patterns recorded for future slices.
