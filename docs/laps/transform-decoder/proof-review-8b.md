# Proof Review — transform-decoder (Slice 8B)

## Kernel status

`lake env lean opentrackio_parser/TransformDecoder.lean` — exit 0, no warnings.
`lake build TransformDecoder` — exit 0 (4.1s, 3289 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No `ValidTransform` predicate.
- No `Except.bind` lemma guessing or `split at h` on the `decodeTransform` body.
- No changes to Slices 1–8A.

## Statement audit

| Name | Intended | Captured |
|---|---|---|
| `decodeNumberField` | `.number s` → `.ok s`; else `invalidRational` | Yes |
| `decodeVec3` | object with `"x"`, `"y"`, `"z"` number fields | Yes |
| `decodeRotation` | object with `"pan"`, `"tilt"`, `"roll"` number fields | Yes |
| `decodeIdField` | absent → `none`; nonempty string → `some ⟨s, h⟩`; empty/non-string → error | Yes |
| `decodeTransform` | required translation + rotation; optional scale + id | Yes |
| `decodeTransform_sound` | decoded id, when present, has nonempty val | Yes |

## Semantic review

**`decodeIdField`:** The decision proof `if h : s ≠ ""` is the load-bearing
construction. `h : s ≠ ""` becomes the `nonempty` field of `NonemptyString`.
Empty strings produce `missingField "id"` (present but invalid).

**`decodeTransform`:** Required fields use explicit `match j.lookup? ... with`
before the `do` block, avoiding `Option.getD` entirely. Optional `scale` uses
`(decodeVec3 sj).map some`; optional `id` delegates to `decodeIdField`.

**`decodeTransform_sound`:** Term proof `fun ns _ => ns.nonempty`.
- `ns : NonemptyString` from the universal quantifier
- `ns.nonempty : ns.val ≠ ""` is the struct field
- Both `_h` and the id-equality hypothesis are unused
- Non-vacuous: no `NonemptyString` can have an empty `val` by construction;
  the theorem asserts the decoder never produces one

## Hard step identification

`if h : s ≠ "" then .ok (some ⟨s, h⟩)` in `decodeIdField` — the decision
proof becomes the struct field. No hard step in the theorem.

## Anti-pattern scan

- No bare `simp` or `simp_all`.
- No `omega` or arithmetic solvers.
- No global annotations.
- No proxy property.

## Contract compliance

1. ✅ All decoders compile.
2. ✅ `decodeTransform_sound` compiles without `sorry`.
3. ✅ `lake env lean` exit 0, no warnings.
4. ✅ `lake build TransformDecoder` exit 0.
5. ✅ No `Except.bind` archaeology.
6. ✅ No excluded scope introduced.
