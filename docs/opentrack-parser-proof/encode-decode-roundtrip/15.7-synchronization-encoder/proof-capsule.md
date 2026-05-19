# Proof Capsule — synchronization-encoder (Slice 15.7)

## Intent

Define `encodeSyncOffsets` and `encodeSynchronization`, and prove roundtrip theorems
for both against the existing decoders (`decodeSyncOffsets`, `decodeSynchronization`).
`encodePositiveRational` and `encodePtpInfo` are imported from earlier slices and used
without re-proving; their roundtrip lemmas are used as simp lemmas.

## Scope

- One encoder: `encodeSynchronization`
- One roundtrip theorem: `encodeSynchronization_roundtrip`
- `encodeSyncOffsets` and `encodeSyncOffsets_roundtrip` already exist in `LeafEncoders`
  (Slice 15.1); imported, not re-defined here
- No decoder changes

## Frozen formal statements

```lean
def encodeSynchronization (sync : Synchronization) : JsonValue :=
  .object (
    [("locked", .bool sync.locked),
     ("source", .string sync.source.toStr)] ++
    (sync.frequency.map fun r => ("frequency", encodePositiveRational r)).toList ++
    (sync.offsets.map   fun o => ("offsets",   encodeSyncOffsets o)).toList ++
    (sync.present.map   fun b => ("present",   .bool b)).toList ++
    (sync.ptp.map       fun p => ("ptp",       encodePtpInfo p)).toList)

theorem encodeSynchronization_roundtrip (sync : Synchronization) :
    decodeSynchronization (encodeSynchronization sync) = .ok sync
```

## Why the encodings match the decoders

### encodeSyncOffsets

`decodeSyncOffsets` requires `.object _` and treats all three fields as optional via
`lookup?`. All three fields (`translation`, `rotation`, `lensEncoders`) are
`Option String` decoded as `.number s`. The encoder appends only the `some` fields.

### encodeSynchronization

`decodeSynchronization` requires `.object _` with `do`-binds:

| Field | Type | Required | Encoder |
|---|---|---|---|
| `locked` | `Bool` | ✓ | `.bool sync.locked` |
| `source` | `SyncSource` | ✓ | `.string sync.source.toStr` |
| `frequency` | `Option PositiveRational` | — | `encodePositiveRational r` when `some r` |
| `offsets` | `Option SyncOffsets` | — | `encodeSyncOffsets o` when `some o` |
| `present` | `Option Bool` | — | `.bool b` when `some b` (pure let, infallible) |
| `ptp` | `Option PtpInfo` | — | `encodePtpInfo p` when `some p` |

The `source` field is decoded by `decodeSyncSource`, which pattern-matches on the string
literal. The encoder uses `sync.source.toStr` to produce the correct literal.

The optional fields use `.map some` in the decoder (`(decodeFoo vj).map some`). After
applying the nested roundtrip lemma (`decodeFoo (encodeFoo x) = .ok x`), this reduces
to `(.ok x).map some = .ok (some x)`, which is what the bind consumes.

## Proof strategy

### encodeSynchronization_roundtrip

Case split on:
- `source : SyncSource` — 4 constructors (to make `source.toStr` a concrete string
  literal so `decodeSyncSource` reduces)
- `frequency : Option PositiveRational` — 2 cases
- `offsets : Option SyncOffsets` — 2 cases (use `encodeSyncOffsets_roundtrip`)
- `present : Option Bool` — 2 cases
- `ptp : Option PtpInfo` — 2 cases (use `encodePtpInfo_roundtrip`)

Total: 4 × 2⁴ = 64 goals, all closed by `simp` + `<;> rfl` for `do`-bind residuals.

Key simp lemmas: `encodePositiveRational_roundtrip`, `encodeSyncOffsets_roundtrip`,
`encodePtpInfo_roundtrip` (used as rewrite rules so nested decoders reduce without
expanding nested encoder definitions).

## Dependencies

- `SynchronizationDecoder` — `decodeSynchronization`
- `LeafEncoders` — `encodeSyncOffsets`, `encodeSyncOffsets_roundtrip`
- `TimecodeEncoder` — `encodePositiveRational`, `encodePositiveRational_roundtrip`
- `PtpInfoEncoder` — `encodePtpInfo`, `encodePtpInfo_roundtrip`

## File and lakefile placement

| File | Library name |
|---|---|
| `opentrackio_parser/SynchronizationEncoder.lean` | `SynchronizationEncoder` |

Entry appended in `lakefile.toml` after `SynchronizationDecoder`.

## Stop rules

- Do not change `decodeSynchronization` or `decodeSyncOffsets`
- If the 64-case simp approach is slow but correct, accept it — do not restructure the proof
- If `simp` leaves unsolved goals after four attempts to expand the simp set, stop and report
