# Proof Capsule — timecode-encoder (Slice 15.6)

## Intent

Provide `encodePositiveRational : PositiveRational → JsonValue` and
`encodeTimecode : Timecode → JsonValue`, and prove roundtrip theorems for both.

`encodePositiveRational` is defined here (no prior encoder slice covers it) and will be
imported by future slices (15.7, 15.8) that encode `PositiveRational` fields.

## Scope

- Two encoders: `encodePositiveRational`, `encodeTimecode`
- Two roundtrip theorems: `encodePositiveRational_roundtrip`, `encodeTimecode_roundtrip`

## Timecode fields

| Field | Type | Encoding |
|---|---|---|
| `hours` | `String` | `.number hours` |
| `minutes` | `String` | `.number minutes` |
| `seconds` | `String` | `.number seconds` |
| `frames` | `String` | `.number frames` |
| `frameRate` | `PositiveRational` | `encodePositiveRational frameRate` |
| `subFrame` | `Option String` | `(subFrame.map fun s => ("subFrame", .number s)).toList` |
| `dropFrame` | `Option Bool` | `(dropFrame.map fun b => ("dropFrame", .bool b)).toList` |

## PositiveRational encoding

`decodePositiveRational` expects `.object [("num", .number ...), ("denom", .number ...)]`
where the strings parse as positive naturals via `.toNat?`.

```lean
def encodePositiveRational (r : PositiveRational) : JsonValue :=
  .object [("num", .number r.num.toString), ("denom", .number r.den.toString)]
```

Roundtrip relies on `Nat.toString` / `String.toNat?` being inverses, plus `r.num_pos` and
`r.den_pos` to discharge the positivity guards.

## Frozen formal statements

```lean
theorem encodePositiveRational_roundtrip (r : PositiveRational) :
    decodePositiveRational (encodePositiveRational r) = .ok r

theorem encodeTimecode_roundtrip (tc : Timecode) :
    decodeTimecode (encodeTimecode tc) = .ok tc
```

## Dependencies

- `RationalDecoder` (Slice 5) — `decodePositiveRational`, `PositiveRational`
- `TimecodeDecoder` (Slice 14.5) — `decodeTimecode`

## File

`opentrackio_parser/TimecodeEncoder.lean`
