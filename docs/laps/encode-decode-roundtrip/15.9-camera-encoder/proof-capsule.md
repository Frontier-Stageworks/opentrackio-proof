# Proof Capsule — camera-encoder (Slice 15.9)

## Scope

Three encoders and three roundtrip theorems:

| Artifact | Status |
|---|---|
| `encodeSensorPhysicalDimensions` | NEW |
| `encodeSensorResolution` | NEW |
| `encodeCamera` | NEW |
| `encodeSensorPhysicalDimensions_roundtrip` | NEW |
| `encodeSensorResolution_roundtrip` | NEW |
| `encodeCamera_roundtrip` | NEW |

File: `opentrackio_parser/CameraEncoder.lean`  
Library name: `CameraEncoder`  
Lakefile entry: after `CameraDecoder`

---

## Dependencies

| Import | Provides |
|---|---|
| `Mathlib` | tactics |
| `CameraDecoder` | `decodeCamera`, `decodeSensorPhysicalDimensions`, `decodeSensorResolution`, `decodeOptionalString` |
| `TimecodeEncoder` | `encodePositiveRational`, `encodePositiveRational_roundtrip` |
| `NumericLiteralRoundtrip` | `nat_repr_toNat?_some` |

---

## Data model (from CameraModel.lean)

```
structure SensorPhysicalDimensions where
  height : String   -- raw JSON number string
  width  : String

structure SensorResolution where
  height : Nat
  width  : Nat

structure Camera where
  captureFrameRate               : Option PositiveRational
  activeSensorPhysicalDimensions : Option SensorPhysicalDimensions
  activeSensorResolution         : Option SensorResolution
  make                           : Option NonemptyString
  model                          : Option NonemptyString
  serialNumber                   : Option NonemptyString
  firmwareVersion                : Option NonemptyString
  label                          : Option NonemptyString
  anamorphicSqueeze              : Option PositiveRational
  isoSpeed                       : Option String
  fdlLink                        : Option String
  shutterAngle                   : Option String
```

---

## Frozen formal statements

### encodeSensorPhysicalDimensions

```lean
def encodeSensorPhysicalDimensions (spd : SensorPhysicalDimensions) : JsonValue :=
  .object [("height", .number spd.height),
           ("width",  .number spd.width)]
```

**Roundtrip:**

```lean
theorem encodeSensorPhysicalDimensions_roundtrip (spd : SensorPhysicalDimensions) :
    decodeSensorPhysicalDimensions (encodeSensorPhysicalDimensions spd) = .ok spd
```

### encodeSensorResolution

```lean
def encodeSensorResolution (sr : SensorResolution) : JsonValue :=
  .object [("height", .number sr.height.repr),
           ("width",  .number sr.width.repr)]
```

**Roundtrip:**

```lean
theorem encodeSensorResolution_roundtrip (sr : SensorResolution) :
    decodeSensorResolution (encodeSensorResolution sr) = .ok sr
```

### encodeCamera

```lean
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

**Roundtrip:**

```lean
theorem encodeCamera_roundtrip (c : Camera) :
    decodeCamera (encodeCamera c) = .ok c
```

---

## Key proof notes

### encodeSensorPhysicalDimensions_roundtrip

`decodeSensorPhysicalDimensions` matches `.object _`, looks up `"height"` and `"width"`, and
pattern-matches on `.number hs, .number ws` to produce `{ height := hs, width := ws }`.
The encoder produces exactly that object. `simp [encodeSensorPhysicalDimensions,
decodeSensorPhysicalDimensions, JsonValue.lookup?]` closes the goal in one step.

### encodeSensorResolution_roundtrip

`decodeSensorResolution` calls `hs.toNat?` and `ws.toNat?` on the `.number` strings.
The encoder writes `sr.height.repr` and `sr.width.repr`. The bridge theorem
`nat_repr_toNat?_some` (Slice 15.6A) gives `sr.height.repr.toNat? = some sr.height` and
similarly for width. Strategy:

```lean
theorem encodeSensorResolution_roundtrip (sr : SensorResolution) :
    decodeSensorResolution (encodeSensorResolution sr) = .ok sr := by
  obtain ⟨h, w⟩ := sr
  simp [encodeSensorResolution, decodeSensorResolution,
        JsonValue.lookup?, nat_repr_toNat?_some]
```

### encodeCamera_roundtrip — NonemptyString fields

`decodeOptionalString` contains `if h : s ≠ "" then .ok (some ⟨s, h⟩) else .error ...`.
When the encoder writes `ns.val` (a `NonemptyString`), `ns.nonempty : ns.val ≠ ""` satisfies
the guard. `dif_pos ns.nonempty` selects the `then` branch, producing `some ⟨ns.val, h⟩`.
This equals `some ns` by proof irrelevance (`nonempty` is a `Prop`).

`simp [decodeOptionalString, dif_pos]` should close NonemptyString branches, with simp
unifying `⟨ns.val, h⟩ = ns` via the `NonemptyString.ext` or `Subtype`-style extensionality.

### encodeCamera_roundtrip — overall strategy

1. `obtain ⟨cfr, aspd, asr, mk, mdl, sn, fw, lbl, as_, iso, fdl, sa⟩ := c`
2. `rcases` all 12 optional fields — produces 2^12 = 4096 sub-goals.
3. Simp set:
   - `encodeCamera, decodeCamera` — unfolds encoder (concrete object) and decoder (`do` block)
   - `encodeSensorPhysicalDimensions_roundtrip, encodeSensorResolution_roundtrip` — rewrites sub-object decode-encode back to `.ok spd` / `.ok sr`
   - `encodePositiveRational_roundtrip` — rewrites rational decode-encode
   - `decodeOptionalString, dif_pos` — reduces NonemptyString field decoders
   - `JsonValue.lookup?` — resolves field lookups in the concrete object list
   - `Except.map` — reduces `(.ok x).map some`
4. `<;> rfl` — closes residual do-bind goals.

### Goal count and heartbeats

2^12 = 4096 goals. Each goal is structurally uniform (no enum splitting). The simp cost
per goal should be comparable to or lower than the timing encoder (which had 192 goals at
400000 heartbeats). A starting estimate of `set_option maxHeartbeats 800000` is reasonable;
the actual value will be confirmed during Stop 3.

---

## Out of scope

- Encoding / decoding the `Camera` struct inside a `Sample` — handled by `SampleEncoder` (15.11).
- No changes to any completed slice.

---

## Stop rule

This capsule is complete. Do NOT proceed to the proof plan until the user signs off.
