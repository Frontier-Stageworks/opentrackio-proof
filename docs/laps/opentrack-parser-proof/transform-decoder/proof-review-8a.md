# Proof Review — transform-model (Slice 8A)

## Kernel status

`lake build TransformModel` — exit 0 (170ms, 3 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No decoder.
- No theorems.
- No changes to Slices 1–7.

## Statement audit

| Name | Intended | Captured |
|---|---|---|
| `NonemptyString` | `String` with `nonempty : val ≠ ""` struct field | Yes |
| `Vec3` | triple of raw JSON number strings | Yes |
| `Rotation` | Euler angles (pan/tilt/roll) as raw strings; unbounded | Yes |
| `Transform` | translation + rotation required; scale + id optional | Yes |

## Design note: invariants in types

`id : Option NonemptyString` encodes the id-nonemptiness invariant at the type
level. Any `t : Transform` with `t.id = some ns` already carries `ns.nonempty`.
No `ValidTransform` predicate is needed. This follows the same pattern as
`PositiveRational` (Slice 1) and `Fin 10` (Slice 4A).

The decoder (future Slice 8B) will construct `NonemptyString` using a decision
proof `if h : s ≠ "" then ... { val := s, nonempty := h }`, exactly as
`PositiveRational` uses `if hn : 0 < n`.

## Contract compliance

1. ✅ All four structs compile.
2. ✅ No `sorry` or forbidden constructs.
3. ✅ `lake build TransformModel` exit 0.
4. ✅ id invariant carried by type, not predicate.
