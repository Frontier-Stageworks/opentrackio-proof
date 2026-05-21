# Proof Review — lens-decoder (Slice 10B)

## Kernel status

`lake env lean opentrackio_parser/LensDecoder.lean` — exit 0, no warnings.
`lake build LensDecoder` — exit 0 (3.1s, 3291 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No `ValidLens` predicate.
- No `Option.getD`.
- No `Except.bind` archaeology in the soundness proof.
- No numeric bounds enforcement.
- No changes to Slices 1–10A.

## Statement audit

| Name | Intended | Captured |
|---|---|---|
| `decodeNumberString` (private) | `.number s` → `.ok s`; else `expectedNumber` | Yes |
| `decodeOptionalString` (private) | absent → `none`; nonempty string → `some ⟨s, h⟩`; else error | Yes |
| `decodeCustom` (private) | array of numbers → `List String`; non-array → error | Yes |
| `decodeCalibrationHistory` (private) | array of nonempty strings → `List NonemptyString`; else error | Yes |
| `decodeFizOptions` | object; at least one of focus/iris/zoom required; absent/non-number → `none` | Yes |
| `decodeDistortionOffset` | object with required x, y number fields | Yes |
| `decodeProjectionOffset` | object with required x, y number fields | Yes |
| `decodeExposureFalloff` | object; a1 required; a2/a3 optional numbers | Yes |
| `decodeDistortion` | object; radial required nonempty; tangential optional nonempty; model with default | Yes |
| `decodeStaticLens` | all 8 fields optional; do block | Yes |
| `decodeLens` | all 12 fields optional; do block | Yes |
| `decodeLens_sound` | decoded encoders, when present, satisfies anyPresent | Yes |

## Semantic review

**`decodeFizOptions`:** The load-bearing step is `if h : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none`. Decidability holds via `DecidableEq (Option String)` and `instDecidableOr`. `h` becomes the `anyPresent` struct field directly — the invariant is established locally and not recovered later by tracing the lens decoder.

**`decodeDistortion`:** `model` uses monadic `←` with three cases:
- absent → `.ok "Brown-Conrady D-U"` (the schema default)
- present `.string s` → `.ok s`
- present non-string → `.error .expectedString`

This is stricter than a silent fallback: a present-but-wrong-type model field is an error, consistent with the project's field-type discipline.

**`decodeCalibrationHistory`:** Uses `List.mapM` with a per-element decision proof `if h : s ≠ ""`. Each nonempty string becomes `⟨s, h⟩ : NonemptyString`. Empty strings and non-strings produce errors.

**`decodeLens`:** Scalar optional number fields (`entrancePupilOffset`, `fStop`, `focusDistance`, `pinholeFocalLength`, `tStop`) use plain `let` (no `←`) — these cannot fail. Sub-object fields use monadic `←` via `.map some`. `distortion` delegates to `decodeNonemptyArray decodeDistortion`.

**`decodeLens_sound`:** Term proof `fun fiz _ => fiz.anyPresent`.
- `fiz : FizOptions` from the universal quantifier
- `fiz.anyPresent : fiz.focus ≠ none ∨ fiz.iris ≠ none ∨ fiz.zoom ≠ none` is the struct field
- Both `_h` and the field-equality hypothesis are unused
- Non-vacuous: no `FizOptions` can have all three fields `none` by construction

## Hard step identification

`if h : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none` in `decodeFizOptions` — the decision proof becomes the `anyPresent` struct field. No hard step in the theorem.

## Guardrail compliance

- No numeric bounds enforced (`[0.0, 1.0]`, `[0, 4294967295]`, minimum 1.0, exclusiveMinimum 0.0).
- No integer-vs-float distinction enforced (`encoders` and `rawEncoders` both use `Option String` raw values via `FizOptions`).
- No max string length enforced for `calibrationHistory` elements.
- Soundness theorem claims only `anyPresent` — no overclaiming.

## Anti-pattern scan

- No bare `simp` or `simp_all`.
- No `omega` or arithmetic solvers.
- No global annotations.
- No proxy property.

## Contract compliance

1. ✅ All decoders compile.
2. ✅ `decodeLens_sound` compiles without `sorry`.
3. ✅ `lake env lean` exit 0, no warnings.
4. ✅ `lake build LensDecoder` exit 0.
5. ✅ No `Option.getD` or `Except.bind` archaeology.
6. ✅ Guardrail respected — no overclaimed bounds or type distinctions.
7. ✅ No excluded scope introduced.
