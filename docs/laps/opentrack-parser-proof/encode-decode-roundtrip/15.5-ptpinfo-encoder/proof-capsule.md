# Proof Capsule — ptpinfo-encoder (Slice 15.5)

## Intent

Provide `encodePtpInfo : PtpInfo → JsonValue` and prove that
`decodePtpInfo (encodePtpInfo p) = .ok p` for all `p : PtpInfo`.

## Scope

- One encoder: `encodePtpInfo`
- One roundtrip theorem: `encodePtpInfo_roundtrip`

## PtpInfo fields

| Field | Type | Encoding |
|---|---|---|
| `profile` | `PtpProfile` | `.string profile.toStr` |
| `domain` | `String` | `.number domain` |
| `leaderIdentity` | `NonemptyString` | `.string leaderIdentity.val` |
| `leaderPriorities` | `LeaderPriorities` | `encodeLeaderPriorities leaderPriorities` |
| `leaderAccuracy` | `String` | `.number leaderAccuracy` |
| `meanPathDelay` | `String` | `.number meanPathDelay` |
| `leaderTimeSource` | `Option PtpLeaderSource` | `(leaderTimeSource.map fun s => ("leaderTimeSource", .string s.toStr)).toList` |
| `vlan` | `Option String` | `(vlan.map fun s => ("vlan", .number s)).toList` |

Note: `domain`, `leaderAccuracy`, and `meanPathDelay` are `String` in the model (raw JSON number strings); they round-trip as `.number`.

## Frozen formal statement

```lean
theorem encodePtpInfo_roundtrip (p : PtpInfo) :
    decodePtpInfo (encodePtpInfo p) = .ok p
```

## Dependencies

- `LeafEncoders` (Slice 15.1) — `encodeLeaderPriorities`
- `PtpInfoDecoder` (Slice 14.4) — `decodePtpInfo`
- `TimingEnumDecoders` (Slice 7) — `PtpProfile.toStr`, `PtpLeaderSource.toStr`, soundness theorems

## Proof sketch

All public functions — no private-helper re-exposure needed.

1. `obtain` all fields from `p`.
2. `cases leaderTimeSource` and `cases vlan` to handle optional fields.
3. `rcases leaderIdentity with ⟨liv, lih⟩` to expose `lih : liv ≠ ""` for `dite` reduction.
4. `simp [encodePtpInfo, decodePtpInfo, JsonValue.lookup?,
          PtpProfile.toStr, PtpLeaderSource.toStr, encodeLeaderPriorities,
          decodeLeaderPriorities, *]`
5. `<;> rfl` closes residual bind chains.

## File

`opentrackio_parser/PtpInfoEncoder.lean`
