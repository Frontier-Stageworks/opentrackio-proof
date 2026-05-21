# Proof Review — wellformed-predicate (Slice 16A)

## Acceptance checks

| Check | Result |
|---|---|
| `lake build WellFormedSampleJson` | exit 0, no warnings, 6.4s |
| `WellFormedSampleJson` public, no `sorry` | ✓ |
| All helpers private, no `sorry` | ✓ |

## Deviation from capsule

**`private mutual` not valid:** The capsule sketched `private mutual ... end`. Lean 4
requires visibility modifiers on each `def` inside the block individually, not on the
`mutual` keyword. All three mutual definitions carry their own `private` modifier.

## Key design notes

**`NoDupKeys` via `mutual` block:** Three mutually recursive private functions —
`JsonValue.NoDupKeys`, `ndkFields`, `ndkArr` — handle the `object`, `array`, and
base cases without requiring `termination_by` annotations. Lean 4 infers the structural
termination automatically.

**`allKeysIn` receiver order:** Defined as `(j : JsonValue) (allowed : List String)` so
that Lean 4 dot notation `j.allKeysIn [...]` inserts `j` at the first `JsonValue`-typed
argument. The capsule sketched the arguments in the opposite order; corrected at
implementation time.

**Tier-1 / Tier-2 organization:** Leaf predicates (no schema-object sub-fields) are
defined first; composites reference only already-defined predicates. No forward
references, no mutual recursion among the `WellFormed*` predicates themselves.

**`WellFormedStaticLens` all-optional:** All 8 StaticLens fields are optional; only
`allKeysIn` is asserted — no `hasField` conditions. `calibrationHistory` is a string
array, not a schema object, so no sub-predicate.

**`WellFormedLens` distortion array form:** `∀ arr, j.lookup? "distortion" = some (.array arr) → ∀ e ∈ arr, WellFormedDistortion e` handles the NonemptyArray-backed value without importing NonemptyArray infrastructure. The decoder enforces nonemptiness separately.

**NoDupKeys root-only:** `NoDupKeys` is recursive over the whole JSON tree, so asserting
it once at the root in `WellFormedSampleJson` covers all descendants. Per-type predicates
do not re-assert it.

**No `allKeysIn` on Sample:** `WellFormedSampleJson` does not call `allKeysIn` on `j`
itself. Top-level extension is permitted per A3.

## Status: COMPLETE
