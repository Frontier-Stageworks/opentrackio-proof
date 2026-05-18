# Proof Capsule — encode-decode-roundtrip-by-component (Slice 15)

## Intent

For each component type with a decoder, write a matching encoder and prove:

```
decode (encode x) = .ok x
```

`ProtocolInfo` / `ProtocolVersion` are already complete (Slice 14 / `VersionEncoder.lean`).
All other component types need new encoder functions and roundtrip theorems.

## Scope assessment

Eleven component types remain. Roundtrip proof difficulty varies:
- **Simple number-field structs** (`GlobalStage`, `Timestamp`, `LeaderPriorities`, `SyncOffsets`):
  encoder is straightforward; `simp [encodeX, decodeX, JsonValue.lookup?]` expected to close.
- **Enum fields** (`TimingMode`, `SyncSource`, `PtpProfile`, `PtpLeaderSource`):
  encoder is `JsonValue.string x.toStr`; roundtrip follows from existing soundness theorems.
- **PositiveRational**: encoder must produce `.object [("num", .number n), ("denom", .number d)]`;
  roundtrip proof reuses `decodePositiveRational` structure.
- **NonemptyString fields** (`leaderIdentity`, tracker fields, Transform id):
  encoder is `.string x.val`; roundtrip uses `x.nonempty` to close `if h : s ≠ ""`.
- **Deeply nested / array types** (`Camera`, `Lens`): high proof complexity; deferred to end.

## Sub-slice proposal

| # | Slug | Depends on |
|---|---|---|
| 15.1 | `leaf-encoders` | — |
| 15.2 | `transform-encoder` | 15.1 |
| 15.3 | `globalstage-encoder` | — |
| 15.4 | `tracker-encoder` | 15.1 |
| 15.5 | `ptpinfo-encoder` | 15.1 |
| 15.6 | `timecode-encoder` | 15.1 |
| 15.7 | `synchronization-encoder` | 15.5 |
| 15.8 | `timing-encoder` | 15.6, 15.7 |
| 15.9 | `camera-encoder` | — |
| 15.10 | `lens-encoder` | 15.9 |
| 15.11 | `sample-encoder` | 15.2, 15.3, 15.4, 15.8, 15.9, 15.10 |

**15.1 `leaf-encoders`**: `encodeTimestamp`, `encodeLeaderPriorities`, `encodeSyncOffsets`;
roundtrip theorems for each.

**15.2 `transform-encoder`**: `encodeVec3`, `encodeRotation`, `encodeTransform`;
roundtrip theorem for `Transform`.

**15.3 `globalstage-encoder`**: `encodeGlobalStage`; roundtrip theorem.

**15.4 `tracker-encoder`**: `encodeStaticTracker`, `encodeTracker`; roundtrip theorems.

**15.5 `ptpinfo-encoder`**: `encodePtpInfo`; roundtrip theorem.

**15.6 `timecode-encoder`**: `encodeTimecode`; roundtrip theorem.

**15.7 `synchronization-encoder`**: `encodeSynchronization`; roundtrip theorem.

**15.8 `timing-encoder`**: `encodeTiming`; roundtrip theorem.

**15.9 `camera-encoder`**: `encodeCamera` and supporting types; roundtrip theorem.

**15.10 `lens-encoder`**: `encodeLens`, `encodeStaticLens`; roundtrip theorems.

**15.11 `sample-encoder`**: `encodeSample`; top-level roundtrip theorem.

## Frozen formal statement (per sub-slice)

Each sub-slice produces one theorem of the form:

```lean
theorem encodeX_roundtrip (x : X) : decodeX (encodeX x) = .ok x
```

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions.
- No changes to Slices 1–14.8.

## Stop rule

At the first elaboration failure within any sub-slice, stop and diagnose before
attempting any fix.
