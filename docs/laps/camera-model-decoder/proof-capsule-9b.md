# Proof Capsule — camera-decoder (Slice 9B)

## Parent

Slice 9B of `opentrack-parser-verification`.

## Task classification

**Medium-Large** — four helper decoders, one top-level decoder, one soundness theorem.

## Intent

Decode a `JsonValue` into a `Camera`. Prove that any successfully decoded value
has its `captureFrameRate` field satisfy the `PositiveRational` positivity
invariant when present.

## Resolved ambiguities used

- A1: rational fields use `{ "num": ..., "denom": ... }` JSON object shape.
- A4 (camera): all top-level camera fields are optional; missing → `none`.
  Nested fields within a present object are required.
- A8 (camera): normative key names for all 12 fields.

## Approach

All 12 `Camera` fields are `Option`. The decoder uses a `do` block — no
required-field nesting is needed at the top level. Each field's `lookup?`
result is matched inline:

- Absent → `.ok none`
- Present → delegate to the appropriate sub-decoder or inline match

`PositiveRational` fields delegate to `decodePositiveRational` (Slice 5).
`NonemptyString` fields use a shared `decodeOptionalString` helper that applies
the `if h : s ≠ ""` decision proof. Nested-object fields use shallow
sub-decoders `decodeSensorPhysicalDimensions` and `decodeSensorResolution`.

The soundness theorem targets `captureFrameRate` as the representative
`PositiveRational` field. The decoder hypothesis is unused — positivity is
guaranteed by the `PositiveRational` type.

## Formal statements (frozen)

```lean
def decodeSensorPhysicalDimensions (j : JsonValue) : Except DecodeError SensorPhysicalDimensions
def decodeSensorResolution         (j : JsonValue) : Except DecodeError SensorResolution
def decodeOptionalString  (key : String) (jv : Option JsonValue) : Except DecodeError (Option NonemptyString)
def decodeCamera          (j : JsonValue) : Except DecodeError Camera

theorem decodeCamera_sound
    (j : JsonValue) (c : Camera)
    (_h : decodeCamera j = .ok c) :
    ∀ r, c.captureFrameRate = some r → 0 < r.toReal
```

## Proof note

Proof: `fun r _ => positive_rational_toReal_pos r`.

`r : PositiveRational` carries positivity by construction. Both `_h` and the
field-equality hypothesis are unused — the invariant is established at
construction time by `decodePositiveRational`. Non-vacuous: no `PositiveRational`
can have `toReal ≤ 0` by construction.

## Forbidden

- No `ValidCamera` predicate.
- No `Option.getD`.
- No `Except.bind` archaeology in the soundness proof.
- No `sorry`.
- No changes to Slices 1–9A.
