# Proof Plan — nonempty-array-decoder (Slice 6)

## `NonemptyArray`

Generic struct carrying a `List α` plus a proof that the list is nonempty:

```lean
structure NonemptyArray (α : Type) where
  values   : List α
  nonempty : values ≠ []
```

No separate `ValidNonemptyArray` predicate. The invariant is the struct field.

## `decodeNonemptyArray`

Pattern: `.array []` → reject with `invalidLength`; `.array (hd :: tl)` →
decode head with `decodeElem`, decode tail elements with `tl.mapM decodeElem`,
return `v :: vs` directly — nonemptiness is proved by `List.cons_ne_nil v vs`.

```lean
def decodeNonemptyArray
    (decodeElem : JsonValue → Except DecodeError α)
    (context : String)
    (j : JsonValue) : Except DecodeError (NonemptyArray α) :=
  match j with
  | .array []        => .error (.invalidLength context 1 0)
  | .array (hd :: tl) => do
      let v  ← decodeElem hd
      let vs ← tl.mapM decodeElem
      return { values := v :: vs, nonempty := List.cons_ne_nil v vs }
  | _                => .error .expectedArray
```

Error coverage:
- Non-array input → `expectedArray`
- Empty array → `invalidLength context 1 0`
- Any element fails `decodeElem` → error propagated from the element decoder
- At least one element, all succeed → `.ok { values := v :: vs, nonempty := _ }`

## `decodeNonemptyArray_sound`

Goal shape: `arr.values ≠ []`  
Opening move: `exact arr.nonempty`

```lean
theorem decodeNonemptyArray_sound
    (decodeElem : JsonValue → Except DecodeError α)
    (context : String) (j : JsonValue) (arr : NonemptyArray α)
    (_h : decodeNonemptyArray decodeElem context j = .ok arr) :
    arr.values ≠ [] :=
  arr.nonempty
```

Hard step: `List.cons_ne_nil v vs` in the decoder body (not the theorem proof).
The theorem proof has no hard step — it reads out the struct field directly.

Automation budget: none needed.
