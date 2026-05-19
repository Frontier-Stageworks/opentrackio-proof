# Proof Plan — camera-encoder (Slice 15.9)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/CameraEncoder.lean` | `CameraEncoder` |

Entry appended in `lakefile.toml` after `TimingEncoder`.

---

## Imports

```lean
import Mathlib
import CameraDecoder
import TimecodeEncoder
import NumericLiteralRoundtrip
```

`encodePositiveRational` / `encodePositiveRational_roundtrip` from `TimecodeEncoder` (15.6B).  
`nat_repr_toNat?_some` from `NumericLiteralRoundtrip` (15.6A).  
`decodeSensorPhysicalDimensions`, `decodeSensorResolution`, `decodeCamera`, `decodeOptionalString`
from `CameraDecoder` (9B).

---

## Encoder definitions

```lean
def encodeSensorPhysicalDimensions (spd : SensorPhysicalDimensions) : JsonValue :=
  .object [("height", .number spd.height),
           ("width",  .number spd.width)]

def encodeSensorResolution (sr : SensorResolution) : JsonValue :=
  .object [("height", .number sr.height.repr),
           ("width",  .number sr.width.repr)]

def encodeCamera (c : Camera) : JsonValue :=
  .object (
    (c.captureFrameRate.map fun r =>
      ("captureFrameRate", encodePositiveRational r)).toList ++
    (c.activeSensorPhysicalDimensions.map fun spd =>
      ("activeSensorPhysicalDimensions", encodeSensorPhysicalDimensions spd)).toList ++
    (c.activeSensorResolution.map fun sr =>
      ("activeSensorResolution", encodeSensorResolution sr)).toList ++
    (c.make.map            fun ns => ("make",            .string ns.val)).toList ++
    (c.model.map           fun ns => ("model",           .string ns.val)).toList ++
    (c.serialNumber.map    fun ns => ("serialNumber",    .string ns.val)).toList ++
    (c.firmwareVersion.map fun ns => ("firmwareVersion", .string ns.val)).toList ++
    (c.label.map           fun ns => ("label",           .string ns.val)).toList ++
    (c.anamorphicSqueeze.map fun r =>
      ("anamorphicSqueeze", encodePositiveRational r)).toList ++
    (c.isoSpeed.map      fun s => ("isoSpeed",    .number s)).toList ++
    (c.fdlLink.map       fun s => ("fdlLink",     .string s)).toList ++
    (c.shutterAngle.map  fun s => ("shutterAngle", .number s)).toList)
```

---

## Theorem: encodeSensorPhysicalDimensions_roundtrip

### Statement

```lean
theorem encodeSensorPhysicalDimensions_roundtrip (spd : SensorPhysicalDimensions) :
    decodeSensorPhysicalDimensions (encodeSensorPhysicalDimensions spd) = .ok spd
```

### Proof (VERIFIED via lake build CameraEncoder, exit 0)

```lean
theorem encodeSensorPhysicalDimensions_roundtrip (spd : SensorPhysicalDimensions) :
    decodeSensorPhysicalDimensions (encodeSensorPhysicalDimensions spd) = .ok spd := by
  obtain ⟨h, w⟩ := spd
  simp [encodeSensorPhysicalDimensions, decodeSensorPhysicalDimensions, JsonValue.lookup?]
```

### Why it closes

`decodeSensorPhysicalDimensions` matches `.object _`, looks up `"height"` and `"width"`, and
pattern-matches on `.number hs, .number ws` returning `{ height := hs, width := ws }`.
The encoder produces exactly that object with `.number spd.height` and `.number spd.width`.
After `obtain ⟨h, w⟩`, `spd.height = h` and `spd.width = w` are concrete.
`simp [JsonValue.lookup?]` evaluates the `find?` calls on the two-element list and closes.

---

## Theorem: encodeSensorResolution_roundtrip

### Statement

```lean
theorem encodeSensorResolution_roundtrip (sr : SensorResolution) :
    decodeSensorResolution (encodeSensorResolution sr) = .ok sr
```

### Proof (VERIFIED via lake build CameraEncoder, exit 0)

```lean
theorem encodeSensorResolution_roundtrip (sr : SensorResolution) :
    decodeSensorResolution (encodeSensorResolution sr) = .ok sr := by
  obtain ⟨h, w⟩ := sr
  simp [encodeSensorResolution, decodeSensorResolution,
        JsonValue.lookup?, nat_repr_toNat?_some]
```

### Why it closes

`decodeSensorResolution` calls `hs.toNat?` and `ws.toNat?` on the `.number` strings.
`nat_repr_toNat?_some` (Slice 15.6A) gives `sr.height.repr.toNat? = some sr.height`
and similarly for width. After `obtain ⟨h, w⟩`, these reduce to `h.repr.toNat? = some h`
and `w.repr.toNat? = some w`. `simp` closes the goal.

---

## Theorem: encodeCamera_roundtrip

### Statement

```lean
theorem encodeCamera_roundtrip (c : Camera) :
    decodeCamera (encodeCamera c) = .ok c
```

### Proof (VERIFIED via lake build CameraEncoder, exit 0, 826s, 40M heartbeats)

```lean
set_option maxHeartbeats 40000000

theorem encodeCamera_roundtrip (c : Camera) :
    decodeCamera (encodeCamera c) = .ok c := by
  obtain ⟨cfr, aspd, asr, mk, mdl, sn, fw, lbl, as_, iso, fdl, sa⟩ := c
  rcases cfr  with _ | cfr  <;>
  rcases aspd with _ | aspd <;>
  rcases asr  with _ | asr  <;>
  rcases mk   with _ | ⟨mkv, mkh⟩ <;>
  rcases mdl  with _ | ⟨mdv, mdh⟩ <;>
  rcases sn   with _ | ⟨snv, snh⟩ <;>
  rcases fw   with _ | ⟨fwv, fwh⟩ <;>
  rcases lbl  with _ | ⟨lblv, lblh⟩ <;>
  rcases as_  with _ | as_  <;>
  rcases iso  with _ | iso  <;>
  rcases fdl  with _ | fdl  <;>
  rcases sa   with _ | sa   <;>
  simp [encodeCamera, decodeCamera, decodeOptionalString,
        encodeSensorPhysicalDimensions_roundtrip,
        encodeSensorResolution_roundtrip,
        encodePositiveRational_roundtrip,
        JsonValue.lookup?, Except.map, *] <;> rfl
```

### Why it closes

1. `obtain` — destructures all 12 `Camera` fields.

2. `rcases` on all 12 optional fields:
   - Plain `Option T` (cfr, aspd, asr, as_, iso, fdl, sa): two-branch split (`_ | v`)
   - `Option NonemptyString` (mk, mdl, sn, fw, lbl): destructured as `_ | ⟨v, h⟩` to bring
     the `v ≠ ""` proof into context for `decodeOptionalString`'s `dif_pos`
   - Total: 2^12 = **4096 goals**

3. `simp [encodeCamera, decodeCamera]` — unfolds encoder (concrete object field list) and
   decoder (`do` block with `lookup?` calls).

4. Sub-object roundtrip lemmas — `encodeSensorPhysicalDimensions_roundtrip` and
   `encodeSensorResolution_roundtrip` rewrite nested decode-encode pairs without exposing
   sub-encoder internals.

5. `encodePositiveRational_roundtrip` — rewrites rational decode-encode for
   `captureFrameRate` and `anamorphicSqueeze` fields.

6. `decodeOptionalString` + `*` — unfolds the helper and uses the `NonemptyString` proof
   from context (`mkh`, `mdh`, `snh`, `fwh`, `lblh`) to fire `dif_pos` and close the
   branch. `dif_pos` selects the `then` branch; proof irrelevance unifies
   `⟨v, witness_h⟩ = ⟨v, context_h⟩`.

7. `Except.map` — reduces `(.ok x).map some` for optional field decode arms.

8. `<;> rfl` — closes residual `do`-bind goals (definitionally true).

### Heartbeat note

Default 200000 heartbeats times out. 10000000 (50× default) also times out due to the
4096-goal × 12-field-lookup simp cost. `set_option maxHeartbeats 40000000` (200× default)
is sufficient and verified (826s build time). Per LAPS capsule stop rule: slow-but-correct
is accepted. The `.olean` is cached; downstream consumers are unaffected.

---

## Acceptance criteria

1. `lake env lean opentrackio_parser/CameraEncoder.lean` — exit 0, no warnings.
2. `lake build CameraEncoder` — exit 0.
3. `encodeCamera_roundtrip` public, no `sorry`.
