# Proof Review — json-raw-model

## Kernel status

`lake env lean opentrackio_parser/JsonRawModel.lean` — exit 0, no warnings.  
`lake build JsonRawModel` — exit 0, build complete.

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No map or structure that collapses duplicate keys.
- No duplicate-key validator, `DecodeError`, or `Except`.
- No NoDupKeys predicate.
- No protocol schema or decoder.
- Slice 1 unchanged.

## Statement audit

| Theorem | Intended | Captured |
|---|---|---|
| `lookup?_some_implies_field_present` | `lookup? k j = some v → hasField k j` | Yes |
| `lookup?_none_implies_no_matching_field` | `lookup? k j = none → ¬ hasField k j` | Yes |

## Semantic review

`hasField` is defined as `lookup? k j ≠ none`. This makes the two theorems
exact converses of each other at the propositional level, which is the
intended relationship. No proxy property is proved.

`lookup?` is a first-match scan on a raw `List`. The A2 policy note is in
the module comment and in the capsule: this utility makes no uniqueness claim.

## Hard step identification

Neither theorem required a hard step. Both were closed by `simp only` plus
`Option.some_ne_none` (for Theorem 1) and a double-negation simplification
(for Theorem 2). The proof plan predicted this correctly.

## Hypothesis necessity

No hypotheses beyond the function arguments. No vacuity risk.

## Anti-pattern scan

- `simp only [...]` used, not bare `simp`.
- No global simp lemmas added.
- No automation hides the hard step (there was none).

## A2 policy

The module comment and proof capsule explicitly state that `lookup?` is a
raw utility and that normative field access under uniqueness is deferred.
The slice does not silently adopt first-wins semantics as normative.

## Contract compliance

1. ✅ `JsonValue` inductive compiles.
2. ✅ `lookup?` and `hasField` compile.
3. ✅ Both theorems compile without `sorry`.
4. ✅ `lake env lean` exit 0.
5. ✅ `lake build JsonRawModel` exit 0.
6. ✅ No excluded scope introduced.
7. ⬜ Work queue to be updated (next step).
