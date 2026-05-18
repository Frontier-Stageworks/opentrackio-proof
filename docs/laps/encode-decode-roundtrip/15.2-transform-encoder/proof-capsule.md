# Proof Capsule — transform-encoder (Slice 15.2)

## Intent

Define encoders for `Vec3`, `Rotation`, and `Transform` and prove
`decode (encode x) = .ok x` for each. The `Transform` encoder must handle
two optional fields (`scale : Option Vec3`, `id : Option NonemptyString`).
The `id` roundtrip requires discharging the `if h : s ≠ ""` guard using
`NonemptyString.nonempty`.

Note: the planned dependency on 15.1 (`LeafEncoders`) is incorrect —
`Transform` does not use `Timestamp`, `LeaderPriorities`, or `SyncOffsets`.
`TransformEncoder` imports `TransformDecoder` directly.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/TransformEncoder.lean` | `TransformEncoder` |

One new `[[lean_lib]]` entry appended after `LeafEncoders` in `lakefile.toml`.

## Imports

```lean
import DecodeError
import JsonRawModel
import TransformModel
import TransformDecoder
```

## Frozen formal statements

```lean
def encodeVec3      (v  : Vec3)      : JsonValue
def encodeRotation  (r  : Rotation)  : JsonValue
def encodeTransform (t  : Transform) : JsonValue

theorem encodeVec3_roundtrip      (v : Vec3)      : decodeVec3      (encodeVec3 v)      = .ok v
theorem encodeRotation_roundtrip  (r : Rotation)  : decodeRotation  (encodeRotation r)  = .ok r
theorem encodeTransform_roundtrip (t : Transform) : decodeTransform (encodeTransform t) = .ok t
```

## Encoder specification

```
encodeVec3 v      = .object [("x", .number v.x), ("y", .number v.y), ("z", .number v.z)]
encodeRotation r  = .object [("pan", .number r.pan), ("tilt", .number r.tilt), ("roll", .number r.roll)]
encodeTransform t = .object (
  [("translation", encodeVec3 t.translation), ("rotation", encodeRotation t.rotation)] ++
  (t.scale.map fun s  => ("scale", encodeVec3 s)).toList                               ++
  (t.id.map    fun ns => ("id",    .string ns.val)).toList
)
```

## Proof strategy

- `encodeVec3_roundtrip`, `encodeRotation_roundtrip`: `simp [encode, decode, JsonValue.lookup?, decodeNumberField]` on fixed-shape objects.
- `encodeTransform_roundtrip`: `obtain ⟨tr, rot, sc, id⟩ := t`, then `cases sc <;> cases id`. For the `id = some ns` case, additionally `obtain ⟨nsval, hns⟩ := ns` and `simp [hns]` to discharge the `if h : nsval ≠ ""` guard. The resulting `⟨nsval, hns⟩ = ns` closes by `rfl` (struct with proof-irrelevant Prop field).

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions.
- No changes to Slices 1–14.8.

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/TransformEncoder.lean` — exit 0, no warnings.
2. `lake build TransformEncoder` — exit 0.
3. No `sorry` or forbidden constructs.
4. All three roundtrip theorems green.
