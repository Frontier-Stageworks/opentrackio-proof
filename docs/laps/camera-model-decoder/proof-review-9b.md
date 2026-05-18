# Proof Review — camera-decoder (Slice 9B)

## Kernel status

`lake env lean opentrackio_parser/CameraDecoder.lean` — exit 0, no warnings.
`lake build CameraDecoder` — exit 0 (2.7s, 3292 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No `ValidCamera` predicate.
- No `Option.getD`.
- No `Except.bind` archaeology in the soundness proof.
- No changes to Slices 1–9A.

## Statement audit

| Name | Intended | Captured |
|---|---|---|
| `decodeSensorPhysicalDimensions` | object with `"height"`, `"width"` number fields → raw strings | Yes |
| `decodeSensorResolution` | object with `"height"`, `"width"` number fields → `Nat` via `toNat?` | Yes |
| `decodeOptionalString` | absent → `none`; nonempty string → `some ⟨s, h⟩`; empty/non-string → error | Yes |
| `decodeCamera` | all 12 fields optional; absent → `none`; present → delegate to sub-decoder | Yes |
| `decodeCamera_sound` | decoded `captureFrameRate`, when present, satisfies `0 < r.toReal` | Yes |

## Semantic review

**`decodeSensorPhysicalDimensions`:** Explicit `match j.lookup? "height"` and
`match j.lookup? "width"` before the value pattern. Both fields required when
the parent object is present. Number values stored as raw strings; no parsing.

**`decodeSensorResolution`:** Same lookup structure. Number strings parsed via
`String.toNat?`; `none` result → `invalidRational` error. Bounds ([0, 2147483647])
are deferred per the capsule.

**`decodeOptionalString`:** Takes `Option JsonValue` (already the result of
`lookup?`) rather than `JsonValue` directly. This avoids repeating the
absent-field pattern at each of the five call sites. The decision proof
`if h : s ≠ ""` is the load-bearing construction; `h` becomes the `nonempty`
field of `NonemptyString`. Empty strings produce `missingField key`.

**`decodeCamera`:** `do` block with inline `match` on each `lookup?` result.
All-optional field structure means no required-field nesting is needed at the
top level. Rational fields delegate to `decodePositiveRational` via `.map some`.
Nested-object fields delegate to `decodeSensorPhysicalDimensions` /
`decodeSensorResolution` via `.map some`. `isoSpeed` and `shutterAngle` match
`.number s`; `fdlLink` matches `.string s`.

**`decodeCamera_sound`:** Term proof `fun r _ => positive_rational_toReal_pos r`.
- `r : PositiveRational` from the universal quantifier
- `positive_rational_toReal_pos r : 0 < r.toReal` from Slice 5
- Both `_h` and the field-equality hypothesis are unused
- Non-vacuous: no `PositiveRational` can have `toReal ≤ 0` by construction;
  the theorem asserts the decoder never produces one

## Hard step identification

`if h : s ≠ "" then .ok (some ⟨s, h⟩)` in `decodeOptionalString` — the
decision proof becomes the `nonempty` struct field. No hard step in the theorem.

## Anti-pattern scan

- No bare `simp` or `simp_all`.
- No `omega` or arithmetic solvers.
- No global annotations.
- No proxy property.

## Contract compliance

1. ✅ All decoders compile.
2. ✅ `decodeCamera_sound` compiles without `sorry`.
3. ✅ `lake env lean` exit 0, no warnings.
4. ✅ `lake build CameraDecoder` exit 0.
5. ✅ No `Option.getD` or `Except.bind` archaeology.
6. ✅ No excluded scope introduced.
