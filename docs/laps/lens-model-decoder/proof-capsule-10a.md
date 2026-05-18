# Proof Capsule — lens-model (Slice 10A)

## Parent

Slice 10A of `opentrack-parser-verification`.

## Task classification

**Medium** — seven sub-structs plus two top-level structs. No decoder. No theorems.

## Intent

Define the Lean data model for the OpenTrackIO `static.lens` and `lens` sub-trees.
All top-level fields are `Option` per A4 (lens resolution). The `FizOptions` type
carries the anyOf presence invariant. No decoder is written here; that is Slice 10B.

## Resolved ambiguities used

- A4 (lens): `static.lens` and `lens` optional; all immediate child fields optional;
  present nested objects satisfy their own required-field constraints;
  `distortion.model` absent → default `"Brown-Conrady D-U"`.
- A6: distortion arrays are nonempty; no fixed length.
- A8 (lens): full `static.lens` and `lens` field trees locked with normative key
  names and types.

## Formal statements (frozen)

```lean
structure FizOptions where
  focus      : Option String
  iris       : Option String
  zoom       : Option String
  anyPresent : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none

structure DistortionOffset where
  x : String
  y : String

structure ProjectionOffset where
  x : String
  y : String

structure ExposureFalloff where
  a1 : String
  a2 : Option String
  a3 : Option String

structure Distortion where
  radial     : NonemptyArray String
  tangential : Option (NonemptyArray String)
  overscan   : Option String
  model      : String   -- absent in JSON → "Brown-Conrady D-U"

structure StaticLens where
  distortionOverscanMax   : Option String
  undistortionOverscanMax : Option String
  make                    : Option NonemptyString
  model                   : Option NonemptyString
  serialNumber            : Option NonemptyString
  firmwareVersion         : Option NonemptyString
  nominalFocalLength      : Option String
  calibrationHistory      : Option (List NonemptyString)

structure Lens where
  custom              : Option (List String)
  distortion          : Option (NonemptyArray Distortion)
  distortionOffset    : Option DistortionOffset
  encoders            : Option FizOptions
  entrancePupilOffset : Option String
  exposureFalloff     : Option ExposureFalloff
  fStop               : Option String
  focusDistance       : Option String
  pinholeFocalLength  : Option String
  projectionOffset    : Option ProjectionOffset
  rawEncoders         : Option FizOptions
  tStop               : Option String
```

## Proof note

No theorems. No `ValidLens` predicate. Structural invariants are carried by
field types: `FizOptions.anyPresent` for the anyOf constraint, `NonemptyArray`
for nonempty arrays, `NonemptyString` for nonempty string items,
`PositiveRational` (not used here) for rational fields. Plain `String` holds
raw JSON numeric literals; bounds are deferred.

## Design decisions

- `Distortion.model : String` (not `Option String`) — the JSON-absent case
  maps to the default string value; the decoder handles this, not the type.
- `calibrationHistory : Option (List NonemptyString)` — the list may be empty
  if present; each element is nonempty by type; max-length bound deferred.
- `custom : Option (List String)` — the list may be empty; elements are raw
  JSON number strings.
- All numeric fields stored as `String` (raw JSON literals); bounds deferred.

## Forbidden

- No decoder in this file.
- No `ValidLens` predicate.
- No `sorry`.
- No changes to Slices 1–9.
