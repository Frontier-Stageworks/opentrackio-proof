# Proof Review — camera-model (Slice 9A)

## Kernel status

`lake env lean opentrackio_parser/CameraModel.lean` — exit 0, no warnings.
`lake build CameraModel` — exit 0 (3.5s, 3288 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No decoder.
- No theorems.
- No `ValidCamera` predicate.
- No changes to Slices 1–8B.

## Statement audit

| Name | Intended | Captured |
|---|---|---|
| `SensorPhysicalDimensions` | `height width : String` (raw JSON number strings; bounds deferred) | Yes |
| `SensorResolution` | `height width : Nat` (integer; bounds deferred) | Yes |
| `Camera` | 12 `Option` fields per A4/A8 camera resolution | Yes |

## Field audit (Camera)

| Field | Type | Source |
|---|---|---|
| `captureFrameRate` | `Option PositiveRational` | A8 rational |
| `activeSensorPhysicalDimensions` | `Option SensorPhysicalDimensions` | A8 nested object |
| `activeSensorResolution` | `Option SensorResolution` | A8 nested object |
| `make` | `Option NonemptyString` | A8 string |
| `model` | `Option NonemptyString` | A8 string |
| `serialNumber` | `Option NonemptyString` | A8 string |
| `firmwareVersion` | `Option NonemptyString` | A8 string |
| `label` | `Option NonemptyString` | A8 string |
| `anamorphicSqueeze` | `Option PositiveRational` | A8 rational |
| `isoSpeed` | `Option String` | A8 deferred |
| `fdlLink` | `Option String` | A8 deferred |
| `shutterAngle` | `Option String` | A8 deferred |

All 12 fields match A8 camera normative key names and types exactly.

## Design note: invariants in types

`Option PositiveRational` fields carry positivity by type; `Option NonemptyString`
fields carry nonemptiness by type. `isoSpeed`, `fdlLink`, and `shutterAngle` are
`Option String` — their bounds and format constraints are deferred per the capsule.
No `ValidCamera` predicate is needed.

## Contract compliance

1. ✅ All three structs compile.
2. ✅ No `sorry` or forbidden constructs.
3. ✅ `lake env lean` exit 0, no warnings.
4. ✅ `lake build CameraModel` exit 0.
5. ✅ No decoder or theorems introduced.
6. ✅ All 12 Camera fields match A8 camera resolution.
