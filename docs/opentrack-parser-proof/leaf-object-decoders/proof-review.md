# Proof Review — leaf-object-decoders (Slice 14.1)

## Kernel status

`lake env lean opentrackio_parser/LeafDecoders.lean` — exit 0, no warnings.
`lake build LeafDecoders` — exit 0 (7.5s, 3298 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions.
- No theorems (none required — all fields are raw strings).
- No changes to Slices 1–14.

## No plan deviations

All three decoders match the plan exactly.

## Decoder audit

| Decoder | Required fields | Optional fields | Error cases |
|---|---|---|---|
| `decodeTimestamp` | `seconds`, `nanoseconds` (`.number`) | — | `missingField`, `expectedNumber`, `expectedObject` |
| `decodeLeaderPriorities` | `priority1`, `priority2` (`.number`) | — | `missingField`, `expectedNumber`, `expectedObject` |
| `decodeSyncOffsets` | — | `translation`, `rotation`, `lensEncoders` (`.number`) | `expectedObject` only; absent/wrong-type fields → `none` |

`decodeSyncOffsets` uses pure `let` (no `←`) since all three fields are
optional and the function cannot fail once the outer `.object _` matches.

## Contract compliance

1. ✅ `lake env lean` exit 0, no warnings.
2. ✅ `lake build LeafDecoders` exit 0.
3. ✅ No `sorry` or forbidden constructs.
4. ✅ No changes to prior slices.
