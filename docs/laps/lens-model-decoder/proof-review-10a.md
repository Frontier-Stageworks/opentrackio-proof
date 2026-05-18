# Proof Review — lens-model (Slice 10A)

## Kernel status

`lake env lean opentrackio_parser/LensModel.lean` — exit 0, no warnings.
`lake build LensModel` — exit 0 (7.1s, 3290 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No decoder.
- No theorems.
- No `ValidLens` predicate.
- No changes to Slices 1–9.

## Statement audit

| Name | Intended | Captured |
|---|---|---|
| `FizOptions` | `focus iris zoom : Option String` + `anyPresent` disjunction proof field | Yes |
| `DistortionOffset` | `x y : String` (raw JSON numbers) | Yes |
| `ProjectionOffset` | `x y : String` (raw JSON numbers) | Yes |
| `ExposureFalloff` | `a1 : String` required; `a2 a3 : Option String` optional | Yes |
| `Distortion` | `radial : NonemptyArray String`; `tangential` optional nonempty; `overscan` optional; `model : String` (not Option) | Yes |
| `StaticLens` | 8 `Option` fields per A8 | Yes |
| `Lens` | 12 `Option` fields per A8 | Yes |

## Field audit — StaticLens

| Field | Type | Source |
|---|---|---|
| `distortionOverscanMax` | `Option String` | A8 number; bound deferred |
| `undistortionOverscanMax` | `Option String` | A8 number; bound deferred |
| `make` | `Option NonemptyString` | A8 string |
| `model` | `Option NonemptyString` | A8 string |
| `serialNumber` | `Option NonemptyString` | A8 string |
| `firmwareVersion` | `Option NonemptyString` | A8 string |
| `nominalFocalLength` | `Option String` | A8 plain number (not rational) |
| `calibrationHistory` | `Option (List NonemptyString)` | A8 array; list may be empty |

## Field audit — Lens

| Field | Type | Source |
|---|---|---|
| `custom` | `Option (List String)` | A8 array of numbers; list may be empty |
| `distortion` | `Option (NonemptyArray Distortion)` | A8 nonempty array |
| `distortionOffset` | `Option DistortionOffset` | A8 object with x/y |
| `encoders` | `Option FizOptions` | A8 anyOf constraint |
| `entrancePupilOffset` | `Option String` | A8 plain number |
| `exposureFalloff` | `Option ExposureFalloff` | A8 object with a1/a2/a3 |
| `fStop` | `Option String` | A8 plain number; bound deferred |
| `focusDistance` | `Option String` | A8 plain number |
| `pinholeFocalLength` | `Option String` | A8 plain number (not rational) |
| `projectionOffset` | `Option ProjectionOffset` | A8 object with x/y |
| `rawEncoders` | `Option FizOptions` | A8 anyOf constraint |
| `tStop` | `Option String` | A8 plain number; bound deferred |

## Design note: Distortion.model

`model : String` (not `Option String`). The JSON-absent case is handled at
decode time by substituting the string `"Brown-Conrady D-U"`. The type does
not represent absence — any constructed `Distortion` always has a model string.
This is the only field in the project with a schema-specified default value.

## Design note: FizOptions.anyPresent

`anyPresent : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none` carries the anyOf
presence invariant at the type level, following the project's invariants-in-types
pattern. No `ValidFizOptions` predicate is needed.

## Contract compliance

1. ✅ All seven structs compile.
2. ✅ No `sorry` or forbidden constructs.
3. ✅ `lake env lean` exit 0, no warnings.
4. ✅ `lake build LensModel` exit 0.
5. ✅ No decoder or theorems introduced.
6. ✅ All fields match A8 lens resolution exactly.
