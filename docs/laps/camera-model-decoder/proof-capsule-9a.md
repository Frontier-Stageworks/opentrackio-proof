# Proof Capsule — camera-model (Slice 9A)

## Parent

Slice 9A of `opentrack-parser-verification`.

## Task classification

**Small** — three struct definitions, no decoder, no theorems.

## Intent

Define the Lean data model for the OpenTrackIO `static.camera` sub-tree.
All fields are `Option` per A4 (camera resolution). No decoder is written here;
that is Slice 9B.

## Resolved ambiguities used

- A4 (camera): all `static.camera` fields are optional for consumers. Missing
  fields decode to `none`; there are no schema defaults. When a nested object
  IS present, its internal fields are required.
- A8 (camera): full `static.camera` field tree with normative key names and
  types locked.

## Formal statements (frozen)

```lean
structure SensorPhysicalDimensions where
  height : String   -- raw JSON number string, minimum 0.0 (bounds deferred)
  width  : String

structure SensorResolution where
  height : Nat      -- integer [0, 2147483647]; bounds not enforced here
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

## Proof note

No theorems. No `ValidCamera` predicate. Invariants are carried entirely by the
field types: `PositiveRational` for rational fields, `NonemptyString` for
string-identity fields, plain `String` or `Nat` for the rest.

## Forbidden

- No decoder in this file.
- No `ValidCamera` predicate.
- No `sorry`.
- No changes to Slices 1–8B.

## Deferred

- Bounds validation for `SensorResolution` fields ([0, 2147483647])
- `minimum: 0.0` validation for `SensorPhysicalDimensions` fields
- Regex validation for `fdlLink`
- Bounded-real validation for `shutterAngle`
- Integer bounds for `isoSpeed`
