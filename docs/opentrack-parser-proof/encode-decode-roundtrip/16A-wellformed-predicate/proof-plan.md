# Slice 16A — Proof Plan
# wellformed-predicate

**Status:** VERIFIED — `lake build WellFormedSampleJson` exits 0, no warnings, 6.4s
**Date:** 2026-05-19

---

## Predicates defined

| Predicate | Visibility |
|---|---|
| `JsonValue.NoDupKeys` | private (via `mutual`) |
| `ndkFields` | private (via `mutual`) |
| `ndkArr` | private (via `mutual`) |
| `JsonValue.allKeysIn` | private |
| `WellFormedPositiveRational` | private |
| `WellFormedGlobalStage` | private |
| `WellFormedSensorPhysDims` | private |
| `WellFormedSensorResolution` | private |
| `WellFormedVec3` | private |
| `WellFormedRotation` | private |
| `WellFormedDistortionOffset` | private |
| `WellFormedProjectionOffset` | private |
| `WellFormedLeaderPriorities` | private |
| `WellFormedSyncOffsets` | private |
| `WellFormedFizOptions` | private |
| `WellFormedStaticTracker` | private |
| `WellFormedTracker` | private |
| `WellFormedTimestamp` | private |
| `WellFormedExposureFalloff` | private |
| `WellFormedDistortion` | private |
| `WellFormedProtocol` | private |
| `WellFormedCamera` | private |
| `WellFormedStaticLens` | private |
| `WellFormedStaticInfo` | private |
| `WellFormedTransform` | private |
| `WellFormedPtpInfo` | private |
| `WellFormedSynchronization` | private |
| `WellFormedTimecode` | private |
| `WellFormedLens` | private |
| `WellFormedTiming` | private |
| `WellFormedSampleJson` | **public** |

---

## Infrastructure

### `JsonValue.NoDupKeys` (mutual block)

Defined via three mutually recursive private definitions:

```lean
mutual
  private def JsonValue.NoDupKeys (j : JsonValue) : Prop :=
    match j with
    | .object fields => List.Nodup (fields.map Prod.fst) ∧ ndkFields fields
    | .array elems   => ndkArr elems
    | _              => True

  private def ndkFields (fields : List (String × JsonValue)) : Prop :=
    match fields with
    | [] => True
    | p :: ps => p.2.NoDupKeys ∧ ndkFields ps

  private def ndkArr (elems : List JsonValue) : Prop :=
    match elems with
    | [] => True
    | e :: es => e.NoDupKeys ∧ ndkArr es
end
```

Lean 4 handles the mutual structural recursion without `termination_by` annotations.

### `JsonValue.allKeysIn`

Takes `(j : JsonValue) (allowed : List String)` — receiver first for dot notation.
Vacuously true for non-object values.

---

## Deviation from capsule

**`private mutual` not valid Lean 4 syntax:** The capsule sketched `private mutual ... end`.
Lean 4 requires that visibility modifiers go on each `def` inside the `mutual` block, not on
the `mutual` keyword. Fixed to `mutual ... private def ... private def ... private def ... end`.

---

## Stop 2 checklist

- [x] All 29 predicate definitions compile
- [x] `WellFormedSampleJson` public; all helpers private
- [x] No `sorry`, `admit`, `axiom`, `unsafe`, `partial`
- [x] `lake build WellFormedSampleJson` exits 0, no warnings, 6.4s
