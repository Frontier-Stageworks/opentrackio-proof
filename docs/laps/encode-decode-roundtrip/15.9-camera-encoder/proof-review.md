# Proof Review — camera-encoder (Slice 15.9)

## Acceptance checks

| Check | Result |
|---|---|
| `lake env lean opentrackio_parser/CameraEncoder.lean` | exit 0, no warnings |
| `lake build CameraEncoder` | exit 0 (826s, cached on recheck) |
| `encodeCamera_roundtrip` public, no `sorry` | ✓ |

## Deviations from plan

None. File matches the verified proof plan exactly.

## Key proof notes

The 4096-goal brute-force proof (2^12 from 12 optional fields) requires
`set_option maxHeartbeats 40000000` (200× default). The 10M limit (50× default)
was insufficient due to the combined cost of 12-field `JsonValue.lookup?` evaluation
across all goals.

`NonemptyString` fields are destructured as `⟨v, h⟩` so that `h : v ≠ ""` enters
the context. `simp [decodeOptionalString, *]` then fires `dif_pos h` to select the
`then` branch; proof irrelevance closes `⟨v, witness⟩ = ⟨v, h⟩`.

`encodeSensorPhysicalDimensions_roundtrip` and `encodeSensorResolution_roundtrip`
as simp rules prevent expansion of the sub-encoders in `encodeCamera_roundtrip`,
keeping each goal's simp work bounded.

The `<;> rfl` suffix closes residual `do`-bind goals (definitionally true).

## Status: COMPLETE
