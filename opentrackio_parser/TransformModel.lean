/-
  TransformModel.lean — Slice 8A: transform-model

  Defines the Transform data model. The id nonemptiness invariant is carried
  by NonemptyString, following the invariants-in-types pattern.

  A9: rotation is Euler pan/tilt/roll in degrees. No quaternion. No angle bounds.
  Ref: docs/laps/transform-decoder/proof-capsule-8a.md
-/

/-─────────────────────────────────────────────────────────────────────────────
  NonemptyString

  A String together with a proof that it is not empty.
  Carries the id-nonemptiness invariant at the type level.
─────────────────────────────────────────────────────────────────────────────-/

structure NonemptyString where
  val      : String
  nonempty : val ≠ ""

/-─────────────────────────────────────────────────────────────────────────────
  Vec3

  A triple of raw JSON number strings (x, y, z).
  Semantic float parsing is deferred to a later slice.
─────────────────────────────────────────────────────────────────────────────-/

structure Vec3 where
  x : String
  y : String
  z : String

/-─────────────────────────────────────────────────────────────────────────────
  Rotation

  Euler angles in degrees (pan, tilt, roll) as raw JSON number strings.
  Angles are unbounded: values outside [0, 360) are legal.
─────────────────────────────────────────────────────────────────────────────-/

structure Rotation where
  pan  : String
  tilt : String
  roll : String

/-─────────────────────────────────────────────────────────────────────────────
  Transform

  A camera or object transform with required translation and rotation,
  optional scale and id. Any value of this type is structurally valid:
  if id is present, it is a NonemptyString by construction.
─────────────────────────────────────────────────────────────────────────────-/

structure Transform where
  translation : Vec3
  rotation    : Rotation
  scale       : Option Vec3
  id          : Option NonemptyString
