# Proof Plan — compose-decoder-soundness / 12A: decodeSampleShell

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/SampleDecoder.lean` | `SampleDecoder` |

Appended after `SampleModel` in `lakefile.toml` (before `IntegrationSmoke`).

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "SampleDecoder"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  SampleDecoder.lean — Slice 12A: decodeSampleShell

  Defines decodeSample : JsonValue → Except DecodeError Sample.
  Wires existing component decoders to Sample fields. Fields with no
  decoder yet produce none. No theorems. No new structs.

  Ref: docs/laps/compose-decoder-soundness/proof-capsule-12a.md
-/

import Mathlib.Tactic
import DecodeError
import JsonRawModel
import RationalDecoder
import NonemptyArrayDecoder
import TransformDecoder
import ProtocolDecoder
import CameraDecoder
import LensDecoder
import SampleModel
```

---

## Step 3 — `decodeSample`

```lean
def decodeSample (j : JsonValue) : Except DecodeError Sample :=
  match j with
  | .object _ => do
      -- Fields wired to existing decoders
      let protocol ←
        match j.lookup? "protocol" with
        | none    => .ok none
        | some vj => (decodeProtocol vj).map some
      let lens ←
        match j.lookup? "lens" with
        | none    => .ok none
        | some vj => (decodeLens vj).map some
      let transforms ←
        match j.lookup? "transforms" with
        | none    => .ok none
        | some vj => (decodeNonemptyArray decodeTransform "transforms" vj).map some
      -- Raw optional string fields
      let sampleId :=
        match j.lookup? "sampleId" with
        | some (.string s) => some s
        | _                => none
      let sourceId :=
        match j.lookup? "sourceId" with
        | some (.string s) => some s
        | _                => none
      let sourceNumber :=
        match j.lookup? "sourceNumber" with
        | some (.number s) => some s
        | _                => none
      -- relatedSampleIds: optional array of strings
      let relatedSampleIds ←
        match j.lookup? "relatedSampleIds" with
        | none                => .ok none
        | some (.array elems) =>
          (elems.mapM (fun ej => match ej with
            | .string s => .ok s
            | _         => .error .expectedString)).map some
        | some _              => .error .expectedArray
      -- static sub-object: decode what we can; tracker deferred
      let staticInfo ←
        match j.lookup? "static" with
        | none    => .ok none
        | some sj =>
          match sj with
          | .object _ => do
              let duration ←
                match sj.lookup? "duration" with
                | none    => .ok none
                | some vj => (decodePositiveRational vj).map some
              let camera ←
                match sj.lookup? "camera" with
                | none    => .ok none
                | some vj => (decodeCamera vj).map some
              let slens ←
                match sj.lookup? "lens" with
                | none    => .ok none
                | some vj => (decodeStaticLens vj).map some
              return some { duration, camera, lens := slens, tracker := none }
          | _ => .error .expectedObject
      -- timing, tracker, globalStage deferred
      return { globalStage      := none
               lens             := lens
               protocol         := protocol
               relatedSampleIds := relatedSampleIds
               sampleId         := sampleId
               sourceId         := sourceId
               sourceNumber     := sourceNumber
               «static»         := staticInfo
               timing           := none
               tracker          := none
               transforms       := transforms }
  | _ => .error .expectedObject
```

### Notes

- `decodeNonemptyArray decodeTransform "transforms" vj` — the `context`
  argument is the string used in the `invalidLength` error.
- `sourceNumber` is a JSON number (integer), so `.number s`, not `.string s`.
- The nested `do` for `staticInfo` uses `sj.lookup?`; `sj` is matched as
  `.object _` first so `lookup?` is well-scoped.
- `slens` avoids shadowing the outer `lens` binding.
- `tracker := none` in `StaticInfo` — no `StaticTracker` decoder yet.

---

## Stop rule

At the first elaboration failure, stop. Do not introduce a new sub-decoder
mid-slice. If a name is not found, check the import and the exact definition
name in the source file.

---

## Acceptance criteria

1. `lake env lean opentrackio_parser/SampleDecoder.lean` — exit 0, no warnings.
2. `lake build SampleDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
4. No theorems in this file.
