# Proof Plan — json-raw-model

## Goal shape

Two definitions of form `def`, two theorems of form implication.  
No induction needed for the theorems if `lookup?` and `hasField` are defined
so that the relationship between them is definitionally transparent.

## Definitions

### `JsonValue.lookup?`

First-match scan on the object field list.  
Returns `none` for all non-object constructors.

```lean
def JsonValue.lookup? (k : String) : JsonValue → Option JsonValue
  | .object fields => (fields.find? (fun p => p.1 == k)).map Prod.snd
  | _             => none
```

`List.find?` is in Mathlib/core and is the right primitive.

### `JsonValue.hasField`

Defined as `lookup? k j ≠ none`, not as a separate membership predicate.
This makes `lookup?_some_implies_field_present` and its converse
provable by `simp`/`tauto` directly.

```lean
def JsonValue.hasField (k : String) (j : JsonValue) : Prop :=
  j.lookup? k ≠ none
```

## Theorems

### `lookup?_some_implies_field_present`

```
j.lookup? k = some v → j.hasField k
```

**Strategy:** unfold `hasField`, rewrite hypothesis, `simp`.  
`some v ≠ none` is closed by `simp` or `exact (Option.some_ne_none _).symm` /
`exact absurd rfl (Option.some_ne_none _)`.

Hard step: none.

### `lookup?_none_implies_no_matching_field`

```
j.lookup? k = none → ¬ j.hasField k
```

**Strategy:** unfold `hasField`, intro, contradiction from `= none` and `≠ none`.  
`simp` or `tauto` closes immediately.

Hard step: none.

## Automation budget

| Goal | Primary | Fallback |
|---|---|---|
| `some v ≠ none` | `simp` | `exact Option.some_ne_none _` |
| `¬ (none ≠ none)` | `simp` | `tauto` |

No `ring`, no `omega`, no `linarith`.

## Note on `hasField` definition choice

Defining `hasField` as `lookup? k j ≠ none` rather than as `∃ v, lookup? k j = some v`
is equivalent (by `Option.ne_none_iff_exists`) but makes the two theorems
one-liners. Either form is acceptable; prefer the simpler one.

## Definitions to unfold

- `JsonValue.hasField` (via `simp only`)
- `JsonValue.lookup?` if needed for case analysis

## Helper lemmas

None expected. If `List.find?` lemmas are needed, use standard Mathlib
`List.find?_some`, `List.find?_eq_none`.
