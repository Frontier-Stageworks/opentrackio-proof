# Proof Review — version-model (Slice 4A)

## Kernel status

`lake env lean opentrackio_parser/ProtocolVersion.lean` — exit 0, no warnings.  
`lake build ProtocolVersion` — exit 0 (15s, 3286 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No `JsonValue`, no field name strings, no `Except`, no `DecodeError`.
- No protocol sample, camera, lens, transform.
- Slices 1–3 unchanged.

## Statement audit

| Name | Intended | Captured |
|---|---|---|
| `ValidVersion` | each component `val ≤ 9` per A13 | Yes — conjunction of three `≤ 9` props |
| `protocolVersion_valid` | every `ProtocolVersion` satisfies `ValidVersion` | Yes |

## Semantic review

`VersionDigit := Fin 10` encodes the schema bound `[0, 9]` in the type.
`ValidVersion` re-expresses it as a `Prop`, making the invariant available
as an explicit hypothesis to downstream decoder slices.

`protocolVersion_valid` is proved by `⟨by omega, by omega, by omega⟩`.
Each `omega` has `v.major.isLt : v.major.val < 10` in scope (from `Fin`)
and derives `v.major.val ≤ 9`. The proof has real content — it bridges
the type-level `< 10` to the spec-level `≤ 9`. Not vacuous.

## Hard step identification

No hard step. `Fin.isLt` supplies the only needed hypothesis; `omega` closes
each branch in one step.

## Hypothesis necessity

`protocolVersion_valid` has no hypotheses beyond `v : ProtocolVersion`.
All bounds come from the type. No vacuity risk.

## Anti-pattern scan

- No bare `simp`.
- No `norm_num` on literals.
- No proof-irrelevant `True` returned by `ValidVersion`.
- No global annotations added.

## Contract compliance

1. ✅ `VersionDigit`, `ProtocolVersion`, `ValidVersion` compile.
2. ✅ `protocolVersion_valid` compiles without `sorry`.
3. ✅ `lake env lean` exit 0.
4. ✅ `lake build ProtocolVersion` exit 0.
5. ✅ No excluded scope introduced.
6. ✅ A11, A12, A13 resolved and recorded before implementation.
