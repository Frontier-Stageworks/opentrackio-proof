# Proof Review — nonempty-array-decoder (Slice 6)

## Kernel status

`lake env lean opentrackio_parser/NonemptyArrayDecoder.lean` — exit 0, no warnings.  
`lake build NonemptyArrayDecoder` — exit 0 (9.3s, 3288 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No fixed-length assumptions (no Vec3, Vec6, exact-length checks).
- No changes to Slices 1–5.

## Statement audit

| Name | Intended | Captured |
|---|---|---|
| `NonemptyArray α` | generic `List α` with `nonempty : values ≠ []` struct field | Yes |
| `decodeNonemptyArray` | generic decoder; empty → `invalidLength`; nonempty → `v :: vs` | Yes |
| `decodeNonemptyArray_sound` | successful decode → `arr.values ≠ []` | Yes |

## Semantic review

**`decodeNonemptyArray`:** Complete rejection coverage:
- Non-array → `expectedArray`
- Empty array → `invalidLength context 1 0`
- Any element fails `decodeElem` → error propagated from element decoder
- At least one element, all succeed → `.ok { values := v :: vs, nonempty := _ }`

The split `hd :: tl` → decode head separately → `tl.mapM` → return `v :: vs`
is the correct structure. It avoids the need to reason about `mapM` length
preservation: `v :: vs` is literally a cons cell and `List.cons_ne_nil v vs`
is its nonemptiness proof.

**`decodeNonemptyArray_sound`:** `arr.nonempty` directly witnesses the invariant.
The hypothesis `_h` is intentionally unused — the struct field IS the proof.
This is non-vacuous: the decoder only produces a `NonemptyArray` via
`List.cons_ne_nil`, so the field is always genuinely populated.

## Hard step identification

`List.cons_ne_nil v vs` in the decoder body is the load-bearing construction.
It provides the `nonempty` field without requiring an external lemma about
`List.mapM` length preservation, which would be harder to work with.

## Anti-pattern scan

- No bare `simp`.
- No `omega`, `norm_num`, or other solvers.
- No global annotations.
- No proxy property — `arr.values ≠ []` is the exact invariant.

## Contract compliance

1. ✅ `NonemptyArray` and `decodeNonemptyArray` compile.
2. ✅ `decodeNonemptyArray_sound` compiles without `sorry`.
3. ✅ `lake env lean` exit 0, no warnings.
4. ✅ `lake build NonemptyArrayDecoder` exit 0.
5. ✅ No fixed-length assumptions introduced.
6. ✅ No excluded scope introduced.
