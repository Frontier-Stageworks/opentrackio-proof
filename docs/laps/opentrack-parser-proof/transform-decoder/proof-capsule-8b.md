# Proof Capsule — transform-decoder (Slice 8B)

## Parent

Slice 8B of `opentrack-parser-verification`.

## Task classification

**Medium** — three helper decoders, one top-level decoder, one soundness theorem.

## Intent

Decode a `JsonValue` into a `Transform`. Prove that any successfully decoded
value satisfies the id-nonemptiness invariant.

## Resolved ambiguities used

- A9: rotation is Euler pan/tilt/roll in degrees; no angle bounds.
- 8A: `NonemptyString` carries the id invariant at the type level.

## Approach

`id : Option NonemptyString` means any constructed `Transform` already satisfies
the invariant. The decoder constructs `NonemptyString` via a decision proof
`if h : s ≠ "" then .ok (some ⟨s, h⟩)`, exactly as `PositiveRational` uses
`if hn : 0 < n`. The soundness proof does not need to trace `Except` binds.

## Formal statements (frozen)

```lean
def decodeNumberField (ctx : String) (j : JsonValue) : Except DecodeError String
def decodeVec3        (j : JsonValue) : Except DecodeError Vec3
def decodeRotation    (j : JsonValue) : Except DecodeError Rotation
def decodeTransform   (j : JsonValue) : Except DecodeError Transform

theorem decodeTransform_sound
    (j : JsonValue) (t : Transform)
    (_h : decodeTransform j = .ok t) :
    ∀ ns, t.id = some ns → ns.val ≠ ""
```

## Proof note

Proof: `fun ns _ => ns.nonempty`.

`ns : NonemptyString` carries `nonempty : ns.val ≠ ""` as a struct field.
Both `_h` and the id-equality hypothesis are unused — the invariant is
established at construction time, not by decoder analysis. Non-vacuous for the
same reason as `decodeVersionValue_sound`: the theorem asserts the decoder
never produces an empty id string, which `NonemptyString` prevents by construction.

## Forbidden

- No `ValidTransform` predicate.
- No `Except.bind` / `split at h` on the `decodeTransform` body.
- No `sorry`.
- No changes to Slices 1–8A.
