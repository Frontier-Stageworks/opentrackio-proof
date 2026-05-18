# Proof Review — leaf-encoders (Slice 15.1)

## Acceptance criteria

| Criterion | Result |
|---|---|
| `lake env lean opentrackio_parser/LeafEncoders.lean` — exit 0, no warnings | PASS |
| `lake build LeafEncoders` — exit 0 | PASS |
| No `sorry` or forbidden constructs | PASS |
| All three roundtrip theorems green | PASS |

## Review

**Encoders**:
- `encodeTimestamp`: fixed two-field object; straightforward.
- `encodeLeaderPriorities`: fixed two-field object; straightforward.
- `encodeSyncOffsets`: dynamic list via `Option.map ... |>.toList` concatenation — omits absent fields.

**Proofs**:
- `encodeTimestamp_roundtrip` and `encodeLeaderPriorities_roundtrip`: `simp [encode, decode, JsonValue.lookup?]` closes directly on fixed-shape concrete objects.
- `encodeSyncOffsets_roundtrip`: required `obtain ⟨t, r, l⟩ := so` before `cases` to fully destructure the struct. `cases so.translation` (field-based) does not substitute `so.translation` in the goal — `obtain` is the correct form. After destructuring, `cases t <;> cases r <;> cases l` splits into 8 concrete shapes; `simp` closes all.

**Deviation from plan**: proof plan used `cases so.translation` which failed. Fixed to `obtain ⟨t, r, l⟩ := so; cases t <;> cases r <;> cases l`. Plan updated accordingly.

## Verdict

ACCEPTED. One proof deviation resolved at Stop 3; fix recorded here.
