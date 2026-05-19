# Proof Capsule — timecode-encoder-roundtrip (Slice 15.6B)

## Intent

Define `encodePositiveRational` and `encodeTimecode`, and prove roundtrip theorems for
both. The `PositiveRational` encoder is the foundational piece reused by every future
encoder slice that encodes a rational field.

## Scope

- Two encoders: `encodePositiveRational`, `encodeTimecode`
- Two roundtrip theorems: `encodePositiveRational_roundtrip`, `encodeTimecode_roundtrip`
- No decoder changes

## Frozen formal statements

```lean
def encodePositiveRational (r : PositiveRational) : JsonValue :=
  .object [("num",   .number r.num.toString),
           ("denom", .number r.den.toString)]

def encodeTimecode (tc : Timecode) : JsonValue :=
  .object (
    [("hours",     .number tc.hours),
     ("minutes",   .number tc.minutes),
     ("seconds",   .number tc.seconds),
     ("frames",    .number tc.frames),
     ("frameRate", encodePositiveRational tc.frameRate)] ++
    (tc.subFrame.map  fun s => ("subFrame",  .number s)).toList ++
    (tc.dropFrame.map fun b => ("dropFrame", .bool   b)).toList)

theorem encodePositiveRational_roundtrip (r : PositiveRational) :
    decodePositiveRational (encodePositiveRational r) = .ok r

theorem encodeTimecode_roundtrip (tc : Timecode) :
    decodeTimecode (encodeTimecode tc) = .ok tc
```

## Why the encodings match the decoders

### encodePositiveRational

`decodePositiveRational` expects `.object [("num", .number ns), ("denom", .number ds)]`
where `ns.toNat? = some n` and `ds.toNat? = some d` with `n > 0`, `d > 0`.

`r.num.toString = Nat.repr r.num` (by the `ToString Nat` instance). So:
- `r.num.toString.toNat? = some r.num` by `nat_repr_toNat?_some` (Slice 15.6A)
- `r.den.toString.toNat? = some r.den` by `nat_repr_toNat?_some`
- `r.num_pos` and `r.den_pos` discharge the positivity guards

### encodeTimecode

`decodeTimecode` uses `do`-notation `←` binds desugared to `Except.bind`.

| Timecode field | Encoding | Decoder match |
|---|---|---|
| `hours : String` | `.number tc.hours` | extracts string verbatim |
| `minutes : String` | `.number tc.minutes` | extracts string verbatim |
| `seconds : String` | `.number tc.seconds` | extracts string verbatim |
| `frames : String` | `.number tc.frames` | extracts string verbatim |
| `frameRate : PositiveRational` | `encodePositiveRational tc.frameRate` | `decodePositiveRational` on the sub-object |
| `subFrame : Option String` | `(some s → [("subFrame", .number s)], none → [])` | optional lookup |
| `dropFrame : Option Bool` | `(some b → [("dropFrame", .bool b)], none → [])` | optional lookup |

The `subFrame` and `dropFrame` fields are appended at the end; `lookup?` finds them
(or returns `none` when absent) correctly in all four `Option × Option` cases.

## Dependencies

- `RationalDecoder` — `decodePositiveRational`, `PositiveRational`
- `TimecodeDecoder` — `decodeTimecode`, `Timecode`
- `NumericLiteralRoundtrip` — `nat_repr_toNat?_some`

## File and lakefile placement

| File | Library name |
|---|---|
| `opentrackio_parser/TimecodeEncoder.lean` | `TimecodeEncoder` |

Entry appended in `lakefile.toml` after `TimecodeDecoder`.

## Stop rules

- Do not change `decodePositiveRational` or `decodeTimecode`
- Do not inline `nat_repr_toNat?_some` — import and reference the theorem
- If simp does not close a case after four lemma additions, stop and report the residual goal
