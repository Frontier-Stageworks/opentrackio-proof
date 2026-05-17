# Proof Capsule — json-raw-model

## Parent

Slice 2 of `opentrack-parser-verification`.  
Plan: [opentrack-parser-plan.md](../opentrack-parser-plan.md)

## Task classification

**Small** — one inductive type, two definitions, two theorems.

## Intent

Define a raw JSON AST that preserves object member order and duplicate keys
exactly as received. This is the raw layer: it can contain invalid data.
The semantic layer (later slices) is where validity is enforced.

`lookup?` is a first-match scan utility on the raw list. It is **not**
presented as normative field lookup. Normative lookup — where uniqueness is
guaranteed — requires a `NoDupKeys` proof and is deferred to a later slice.

## A2 resolution (duplicate-key policy)

**Policy:** OpenTrackIO-conforming JSON objects must have unique member names.
Duplicate keys are a decoding error, not first-wins or last-wins.

**Impact on this slice:**
- `JsonValue.object` holds a raw `List (String × JsonValue)` that may contain
  duplicate keys. The raw model does not enforce uniqueness.
- `lookup?` uses first-match as a raw list scan. This is a utility for later
  decoders, not a normative claim about semantics under duplicate keys.
- Uniqueness validation and normative lookup are deferred to a later slice.
  No `NoDupKeys` predicate or checker is defined here.

## Formal statements (frozen)

```lean
inductive JsonValue where
  | null
  | bool   : Bool   → JsonValue
  | number : String → JsonValue
  | string : String → JsonValue
  | array  : List JsonValue → JsonValue
  | object : List (String × JsonValue) → JsonValue

def JsonValue.lookup? : String → JsonValue → Option JsonValue
def JsonValue.hasField : String → JsonValue → Prop

theorem lookup?_some_implies_field_present :
  j.lookup? k = some v → j.hasField k

theorem lookup?_none_implies_no_matching_field :
  j.lookup? k = none → ¬ j.hasField k
```

Note: argument order (`k` before `j`) may be adjusted for dot-notation
ergonomics; if so, `hasField` signature must stay consistent with `lookup?`.

## Allowed changes

- Internal tactic proofs.
- Minor ergonomic adjustments to argument order, as long as theorems match intent.

## Forbidden changes

- No map, RBMap, HashMap, or any structure that collapses duplicate keys.
- No duplicate-key validator or checker.
- No `DecodeError` or `Except`.
- No NoDupKeys predicate.
- No protocol schema or decoder.
- No changes to Slice 1.
- No `sorry`, `admit`, or unsound axioms.
