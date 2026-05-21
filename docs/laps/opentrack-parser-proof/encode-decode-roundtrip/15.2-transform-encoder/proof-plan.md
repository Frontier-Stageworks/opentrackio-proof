# Proof Plan — transform-encoder (Slice 15.2)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/TransformEncoder.lean` | `TransformEncoder` |

Appended after `LeafEncoders` in `lakefile.toml`.

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "TransformEncoder"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  TransformEncoder.lean — Slice 15.2: transform-encoder

  Encoders for Vec3, Rotation, and Transform with roundtrip theorems.
  Transform has two optional fields: scale (Option Vec3) and id (Option NonemptyString).
  The id roundtrip discharges the nonemptiness guard via ns.nonempty.

  Ref: docs/laps/encode-decode-roundtrip/15.2-transform-encoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import TransformModel
import TransformDecoder
```

---

## Step 3 — Encoders

```lean
def encodeVec3 (v : Vec3) : JsonValue :=
  .object [("x", .number v.x), ("y", .number v.y), ("z", .number v.z)]

def encodeRotation (r : Rotation) : JsonValue :=
  .object [("pan", .number r.pan), ("tilt", .number r.tilt), ("roll", .number r.roll)]

def encodeTransform (t : Transform) : JsonValue :=
  .object ([("translation", encodeVec3 t.translation),
            ("rotation",    encodeRotation t.rotation)] ++
           (t.scale.map fun s  => ("scale", encodeVec3 s)).toList ++
           (t.id.map    fun ns => ("id",    .string ns.val)).toList)
```

---

## Step 4 — Roundtrip theorems

```lean
theorem encodeVec3_roundtrip (v : Vec3) :
    decodeVec3 (encodeVec3 v) = .ok v := by
  simp [encodeVec3, decodeVec3, JsonValue.lookup?, decodeNumberField]

theorem encodeRotation_roundtrip (r : Rotation) :
    decodeRotation (encodeRotation r) = .ok r := by
  simp [encodeRotation, decodeRotation, JsonValue.lookup?, decodeNumberField]

theorem encodeTransform_roundtrip (t : Transform) :
    decodeTransform (encodeTransform t) = .ok t := by
  obtain ⟨tr, rot, sc, id⟩ := t
  cases sc <;> cases id with
  | none =>
    simp [encodeTransform, decodeTransform, JsonValue.lookup?,
          encodeVec3, decodeVec3, decodeNumberField,
          encodeRotation, decodeRotation, decodeIdField]
  | some ns =>
    obtain ⟨nsval, hns⟩ := ns
    simp [encodeTransform, decodeTransform, JsonValue.lookup?,
          encodeVec3, decodeVec3, decodeNumberField,
          encodeRotation, decodeRotation, decodeIdField, hns]
```

### Notes

- `encodeVec3_roundtrip` and `encodeRotation_roundtrip`: fixed-shape objects; `simp`
  with `decodeNumberField` reduces `.number s` match arms directly.
- `encodeTransform_roundtrip`: `obtain` destructs `Transform` fields; `cases sc` and
  `cases id` give concrete `none`/`some` shapes. For `id = some ns`, `obtain ⟨nsval, hns⟩ := ns`
  exposes `hns : nsval ≠ ""` so `simp [hns]` discharges `if h : nsval ≠ "" then ...`.
  The resulting `⟨nsval, hns⟩ = ⟨nsval, hns⟩` closes by `rfl`.
- If the combined `cases sc <;> cases id` tactic leaves unexpected goal shapes, split
  into explicit `| none => ... | some sc => ...` for `scale` first.

---

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/TransformEncoder.lean` — exit 0, no warnings.
2. `lake build TransformEncoder` — exit 0.
3. No `sorry` or forbidden constructs.
4. All three roundtrip theorems green.
