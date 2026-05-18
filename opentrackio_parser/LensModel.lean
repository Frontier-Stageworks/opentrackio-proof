/-
  LensModel.lean — Slice 10A: lens-model

  Defines the Lens and StaticLens data models for the OpenTrackIO lens sub-trees.
  All top-level fields are Option per A4 (lens resolution). No decoder. No theorems.

  A4: missing fields → none; distortion.model absent → "Brown-Conrady D-U".
  A6: distortion arrays are nonempty; no fixed length.
  A8: normative key names for all fields.
  Ref: docs/laps/lens-model-decoder/proof-capsule-10a.md
-/

import NonemptyArrayDecoder
import TransformModel

/-─────────────────────────────────────────────────────────────────────────────
  FizOptions

  Carries the anyOf presence invariant for encoders/rawEncoders: at least one
  of focus, iris, zoom must be present. Values are raw JSON numeric strings;
  bounds are deferred.
─────────────────────────────────────────────────────────────────────────────-/

structure FizOptions where
  focus      : Option String
  iris       : Option String
  zoom       : Option String
  anyPresent : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none

/-─────────────────────────────────────────────────────────────────────────────
  DistortionOffset

  Required x and y JSON numbers when the parent object is present.
─────────────────────────────────────────────────────────────────────────────-/

structure DistortionOffset where
  x : String
  y : String

/-─────────────────────────────────────────────────────────────────────────────
  ProjectionOffset

  Required x and y JSON numbers when the parent object is present.
─────────────────────────────────────────────────────────────────────────────-/

structure ProjectionOffset where
  x : String
  y : String

/-─────────────────────────────────────────────────────────────────────────────
  ExposureFalloff

  a1 is required when the parent is present; a2 and a3 are optional.
  All values are raw JSON numeric strings; bounds deferred.
─────────────────────────────────────────────────────────────────────────────-/

structure ExposureFalloff where
  a1 : String
  a2 : Option String
  a3 : Option String

/-─────────────────────────────────────────────────────────────────────────────
  Distortion

  radial is a nonempty array of raw JSON number strings.
  tangential is optional but nonempty if present.
  overscan is an optional raw JSON number string.
  model is a String (not Option): absent in JSON decodes to "Brown-Conrady D-U".
─────────────────────────────────────────────────────────────────────────────-/

structure Distortion where
  radial     : NonemptyArray String
  tangential : Option (NonemptyArray String)
  overscan   : Option String
  model      : String

/-─────────────────────────────────────────────────────────────────────────────
  StaticLens

  All 8 fields are Option per A4. Invariants carried by field types.
─────────────────────────────────────────────────────────────────────────────-/

structure StaticLens where
  distortionOverscanMax   : Option String
  undistortionOverscanMax : Option String
  make                    : Option NonemptyString
  model                   : Option NonemptyString
  serialNumber            : Option NonemptyString
  firmwareVersion         : Option NonemptyString
  nominalFocalLength      : Option String
  calibrationHistory      : Option (List NonemptyString)

/-─────────────────────────────────────────────────────────────────────────────
  Lens

  All 12 fields are Option per A4. Invariants carried by field types.
  encoders and rawEncoders use FizOptions to carry the anyPresent invariant.
─────────────────────────────────────────────────────────────────────────────-/

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
