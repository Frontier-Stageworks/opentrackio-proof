# Proof Plan — ptpinfo-decoder (Slice 14.4)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/PtpInfoDecoder.lean` | `PtpInfoDecoder` |

Appended after `TrackerDecoder` in `lakefile.toml`.

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "PtpInfoDecoder"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  PtpInfoDecoder.lean — Slice 14.4: ptpinfo-decoder

  Decoder for PtpInfo. Six required fields, two optional.
  Uses decodeLeaderPriorities (Slice 14.1) and enum decoders (Slice 7).
  leaderIdentity enforced nonempty at construction. No theorems.

  Ref: docs/laps/ptpinfo-decoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import TransformModel
import TimingEnumDecoders
import LeafDecoders
import SampleModel
```

---

## Step 3 — `decodePtpInfo`

```lean
def decodePtpInfo (j : JsonValue) : Except DecodeError PtpInfo :=
  match j with
  | .object _ => do
      let profile ←
        match j.lookup? "profile" with
        | none    => .error (.missingField "profile")
        | some vj => decodePtpProfile vj
      let domain ←
        match j.lookup? "domain" with
        | none             => .error (.missingField "domain")
        | some (.number s) => .ok s
        | some _           => .error .expectedNumber
      let leaderIdentity ←
        match j.lookup? "leaderIdentity" with
        | none             => .error (.missingField "leaderIdentity")
        | some (.string s) =>
          if h : s ≠ "" then .ok ⟨s, h⟩
          else .error (.missingField "leaderIdentity")
        | some _           => .error .expectedString
      let leaderPriorities ←
        match j.lookup? "leaderPriorities" with
        | none    => .error (.missingField "leaderPriorities")
        | some vj => decodeLeaderPriorities vj
      let leaderAccuracy ←
        match j.lookup? "leaderAccuracy" with
        | none             => .error (.missingField "leaderAccuracy")
        | some (.number s) => .ok s
        | some _           => .error .expectedNumber
      let meanPathDelay ←
        match j.lookup? "meanPathDelay" with
        | none             => .error (.missingField "meanPathDelay")
        | some (.number s) => .ok s
        | some _           => .error .expectedNumber
      let leaderTimeSource ←
        match j.lookup? "leaderTimeSource" with
        | none    => .ok none
        | some vj => (decodePtpLeaderSource vj).map some
      let vlan :=
        match j.lookup? "vlan" with
        | some (.number s) => some s
        | _                => none
      return { profile, domain, leaderIdentity, leaderPriorities,
               leaderAccuracy, meanPathDelay, leaderTimeSource, vlan }
  | _ => .error .expectedObject
```

### Notes

- `decodePtpProfile` and `decodePtpLeaderSource` take a full `JsonValue`
  (not a raw string) — they pattern-match on `.string "..."` internally.
- `leaderIdentity` uses `if h : s ≠ "" then .ok ⟨s, h⟩` — same construction
  as `decodeIdField` in `TransformDecoder`.
- `vlan` is a pure `let` (no `←`) since it is optional and cannot fail.

---

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/PtpInfoDecoder.lean` — exit 0, no warnings.
2. `lake build PtpInfoDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
