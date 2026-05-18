# Proof Capsule — lens-decoder (Slice 10B)

## Parent

Slice 10B of `opentrack-parser-verification`.

## Task classification

**Large** — seven helper decoders, two top-level decoders, one soundness theorem.

## Intent

Decode a `JsonValue` into a `Lens` and a `JsonValue` into a `StaticLens`.
Prove that any successfully decoded `Lens` value has its `encoders` field, when
present, satisfy the `FizOptions.anyPresent` invariant.

## Resolved ambiguities used

- A4 (lens): optionality rules; `distortion.model` default `"Brown-Conrady D-U"`.
- A8 (lens): all normative key names and sub-object shapes.
- A6: distortion arrays use `decodeNonemptyArray` (Slice 6).
- Guardrail: soundness theorem must not overclaim numeric bounds,
  integer-vs-number distinctions, or max string lengths.

## Approach

Each sub-object gets a shallow helper decoder. `decodeFizOptions` constructs
`anyPresent` locally by matching which of `focus`/`iris`/`zoom` is present —
it does not recover this proof later by tracing the full lens decoder.

`decodeDistortion` handles the `model` default: absent `"model"` key →
`"Brown-Conrady D-U"` string; present key → use the string value.

All top-level `lens` and `static.lens` fields are optional — decoders use a
`do` block with inline `match` on `lookup?` results, same pattern as Slice 9B.

## Formal statements (frozen)

```lean
def decodeFizOptions       (j : JsonValue) : Except DecodeError FizOptions
def decodeDistortionOffset (j : JsonValue) : Except DecodeError DistortionOffset
def decodeProjectionOffset (j : JsonValue) : Except DecodeError ProjectionOffset
def decodeExposureFalloff  (j : JsonValue) : Except DecodeError ExposureFalloff
def decodeDistortion       (j : JsonValue) : Except DecodeError Distortion
def decodeStaticLens       (j : JsonValue) : Except DecodeError StaticLens
def decodeLens             (j : JsonValue) : Except DecodeError Lens

theorem decodeLens_sound
    (j : JsonValue) (l : Lens)
    (_h : decodeLens j = .ok l) :
    ∀ fiz, l.encoders = some fiz →
      fiz.focus ≠ none ∨ fiz.iris ≠ none ∨ fiz.zoom ≠ none
```

## Proof note

Proof: `fun fiz _ => fiz.anyPresent`.

`fiz : FizOptions` carries `anyPresent` as a struct field. Both `_h` and the
field-equality hypothesis are unused — the invariant is established at
construction time inside `decodeFizOptions`. Non-vacuous: no `FizOptions` can
have all three fields `none` by construction.

## Forbidden

- No `ValidLens` predicate.
- No `Option.getD`.
- No `Except.bind` archaeology in the soundness proof.
- No numeric bounds enforcement (`[0.0, 1.0]`, `[0, 4294967295]`, etc.).
- No `sorry`.
- No changes to Slices 1–10A.
