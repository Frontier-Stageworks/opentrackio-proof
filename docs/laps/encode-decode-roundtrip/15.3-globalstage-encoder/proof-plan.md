# Proof Plan — globalstage-encoder (Slice 15.3)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/GlobalStageEncoder.lean` | `GlobalStageEncoder` |

Appended after `TransformEncoder` in `lakefile.toml`.

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "GlobalStageEncoder"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  GlobalStageEncoder.lean — Slice 15.3: globalstage-encoder

  Encoder for GlobalStage with roundtrip theorem.
  Six required number fields; no optional fields or invariant-carrying types.

  Ref: docs/laps/encode-decode-roundtrip/15.3-globalstage-encoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import SampleModel
import GlobalStageDecoder
```

---

## Step 3 — Encoder and roundtrip theorem

```lean
def encodeGlobalStage (g : GlobalStage) : JsonValue :=
  .object [("E",    .number g.E),
           ("N",    .number g.N),
           ("U",    .number g.U),
           ("lat0", .number g.lat0),
           ("lon0", .number g.lon0),
           ("h0",   .number g.h0)]

theorem encodeGlobalStage_roundtrip (g : GlobalStage) :
    decodeGlobalStage (encodeGlobalStage g) = .ok g := by
  simp [encodeGlobalStage, decodeGlobalStage, JsonValue.lookup?]; rfl
```

### Notes

- Fixed-shape object; `simp` reduces all six `lookup?` match arms.
- `rfl` closes the residual `Except.bind` chain (pattern from Slice 15.2).

---

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/GlobalStageEncoder.lean` — exit 0, no warnings.
2. `lake build GlobalStageEncoder` — exit 0.
3. No `sorry` or forbidden constructs.
4. Roundtrip theorem green.
