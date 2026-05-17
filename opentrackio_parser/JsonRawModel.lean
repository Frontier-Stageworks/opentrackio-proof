/-
  JsonRawModel.lean — Slice 2: json-raw-model

  Raw JSON AST for the OpenTrackIO parser verification plan.
  This is the raw layer: it preserves object member order and duplicate keys
  exactly as received. The semantic layer enforces validity.

  Ref: docs/laps/opentrack-parser-verification/first-slice-contract.md
  A2:  Duplicate keys are a decoding error in OpenTrackIO. Uniqueness
       validation is deferred to a later slice. `lookup?` here is a raw
       list utility, not normative field access.
-/

import Mathlib.Tactic

/-─────────────────────────────────────────────────────────────────────────────
  Raw JSON AST
─────────────────────────────────────────────────────────────────────────────-/

inductive JsonValue where
  | null
  | bool   : Bool   → JsonValue
  | number : String → JsonValue
  | string : String → JsonValue
  | array  : List JsonValue → JsonValue
  | object : List (String × JsonValue) → JsonValue
  deriving Repr

/-─────────────────────────────────────────────────────────────────────────────
  Raw lookup helper

  First-match scan on the object field list. Returns `none` for all
  non-object constructors and for objects that have no matching key.

  Note: this is a raw utility. Under the A2 policy, normative field lookup
  (where uniqueness is guaranteed) requires a NoDupKeys proof and is deferred
  to a later slice. Do not treat `lookup?` as normative on arbitrary objects.
─────────────────────────────────────────────────────────────────────────────-/

def JsonValue.lookup? (k : String) : JsonValue → Option JsonValue
  | .object fields => (fields.find? fun p => p.1 == k) |>.map Prod.snd
  | _              => none

/-─────────────────────────────────────────────────────────────────────────────
  Field presence predicate

  `hasField k j` holds iff `j` is an object containing at least one field
  with key `k`. Defined as `lookup? k j ≠ none` so that lookup theorems
  are immediately transparent.
─────────────────────────────────────────────────────────────────────────────-/

def JsonValue.hasField (k : String) (j : JsonValue) : Prop :=
  j.lookup? k ≠ none

/-─────────────────────────────────────────────────────────────────────────────
  Theorems
─────────────────────────────────────────────────────────────────────────────-/

/-
  Theorem 1 — A successful lookup implies the field is present.
-/
theorem lookup?_some_implies_field_present
    (j : JsonValue) (k : String) (v : JsonValue)
    (h : j.lookup? k = some v) :
    j.hasField k := by
  simp only [JsonValue.hasField, h]
  exact Option.some_ne_none v

/-
  Theorem 2 — A failed lookup implies the field is absent.
-/
theorem lookup?_none_implies_no_matching_field
    (j : JsonValue) (k : String)
    (h : j.lookup? k = none) :
    ¬ j.hasField k := by
  simp only [JsonValue.hasField, h, ne_eq, not_true, not_false_eq_true]
