/-
  ProtocolVersion.lean — Slice 4A: version-model

  Semantic model for the OpenTrackIO protocol version field.
  No JSON decoding. No field name strings.

  A11: version is a 3-component tuple (major, minor, patch), each in [0, 9].
  A13: ValidVersion encodes the digit-bound constraint from the schema.

  Ref: docs/laps/version-model/first-slice-contract.md
-/

import Mathlib.Tactic

/-─────────────────────────────────────────────────────────────────────────────
  Types
─────────────────────────────────────────────────────────────────────────────-/

abbrev VersionDigit := Fin 10

structure ProtocolVersion where
  major : VersionDigit
  minor : VersionDigit
  patch : VersionDigit

/-─────────────────────────────────────────────────────────────────────────────
  Validity predicate

  Expresses the published schema constraint: each component is an integer
  in [0, 9].  With VersionDigit := Fin 10, the bound is already enforced
  by the type; ValidVersion makes it an explicit, provable Prop.
─────────────────────────────────────────────────────────────────────────────-/

def ValidVersion (v : ProtocolVersion) : Prop :=
  v.major.val ≤ 9 ∧ v.minor.val ≤ 9 ∧ v.patch.val ≤ 9

/-─────────────────────────────────────────────────────────────────────────────
  Theorem — every ProtocolVersion satisfies ValidVersion

  Proof: Fin 10 carries isLt : val < 10 for each field.
  omega derives val ≤ 9 from val < 10 immediately.
─────────────────────────────────────────────────────────────────────────────-/

theorem protocolVersion_valid (v : ProtocolVersion) : ValidVersion v :=
  ⟨by omega, by omega, by omega⟩
