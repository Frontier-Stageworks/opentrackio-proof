# Proof Capsule — transform-model (Slice 8A)

## Parent

Slice 8A of `opentrack-parser-verification` (model only; decoder deferred).

## Task classification

**Small** — struct definitions only. No decoder. No theorems.

## Intent

Define the Transform data model. The `id` nonemptiness invariant is carried by
the type `NonemptyString`, following the same pattern as `PositiveRational`
(invariants in types, not in separate `Valid` predicates).

## Resolved ambiguities used

- A9: rotation is Euler pan/tilt/roll in degrees. No quaternion. No angle bounds.

## Types (frozen)

```lean
structure NonemptyString where
  val      : String
  nonempty : val ≠ ""

structure Vec3 where
  x : String
  y : String
  z : String

structure Rotation where
  pan  : String
  tilt : String
  roll : String

structure Transform where
  translation : Vec3
  rotation    : Rotation
  scale       : Option Vec3
  id          : Option NonemptyString
```

`id : Option NonemptyString` means any `Transform` value that has an id
already carries the proof that the id string is nonempty. No separate
`ValidTransform` predicate is required.

## Forbidden

- No decoder.
- No theorems over `Transform`.
- No `Except.bind` reasoning.
- No `sorry`.
- No changes to Slices 1–7.

## Acceptance

- File builds clean.
- No `sorry`, `admit`, or `axiom`.
