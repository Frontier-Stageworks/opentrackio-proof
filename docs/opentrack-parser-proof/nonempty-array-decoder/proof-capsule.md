# Proof Capsule — nonempty-array-decoder (Slice 6)

## Parent

Slice 6 of `opentrack-parser-verification`.

## Task classification

**Small** — one generic struct, one generic decoder, one soundness theorem.

## Intent

Define a `NonemptyArray α` type that carries a nonemptiness proof, and a generic
`decodeNonemptyArray` that decodes a JSON array with at least one element using a
caller-supplied element decoder. Prove that any successfully decoded value is
nonempty.

## Resolved ambiguities used

- A6: OpenTrackIO numeric arrays have `minItems: 1` and no `maxItems`. The right
  abstraction is a nonemptiness-carrying wrapper, not a fixed-length vector.

## Formal statements (frozen)

```lean
structure NonemptyArray (α : Type) where
  values   : List α
  nonempty : values ≠ []

def decodeNonemptyArray
    (decodeElem : JsonValue → Except DecodeError α)
    (context : String)
    (j : JsonValue) : Except DecodeError (NonemptyArray α)

theorem decodeNonemptyArray_sound
    (decodeElem : JsonValue → Except DecodeError α)
    (context : String) (j : JsonValue) (arr : NonemptyArray α)
    (_h : decodeNonemptyArray decodeElem context j = .ok arr) :
    arr.values ≠ []
```

## Proof note

`arr.nonempty` is the proof: the struct field directly witnesses the invariant.
`_h` is intentionally unused — nonemptiness is guaranteed at construction time,
not derived from inspecting `j`.

The key construction step in the decoder is splitting `hd :: tl` and returning
`{ values := v :: vs, nonempty := List.cons_ne_nil v vs }`. The `cons_ne_nil`
proof is the load-bearing step that makes the struct field non-trivially populated.

## Forbidden

- No `sorry`.
- No fixed-length assumptions (no `Vec3`, `Vec6`, or exact-length checks).
- No changes to Slices 1–5.
