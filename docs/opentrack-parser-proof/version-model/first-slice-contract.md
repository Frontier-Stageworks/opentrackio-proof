# First-Slice Contract — Slice 4A: version-model

## Parent task

- Task slug: `opentrack-parser-verification`
- Work queue: [work-queue.md](../opentrack-parser-verification/work-queue.md)
- Selected slice: `version-model` (Slice 4A)
- Status: **Ready to implement** — A11, A12, A13 resolved.

## Slice objective

> Define `VersionDigit`, `ProtocolVersion`, and `ValidVersion`. Prove that
> every `ProtocolVersion` satisfies `ValidVersion`. No JSON, no decoder.

---

## Resolved ambiguities

| ID | Decision |
|---|---|
| A11 | Version arity = 3 (major, minor, patch). Each component ∈ [0, 9]. |
| A12 | JSON shape = array of 3 integers. Noted for 4B/4C; not used here. |
| A13 | `ValidVersion` expresses `val ≤ 9` for each component. Not `True`. |

---

## Included work

- `abbrev VersionDigit := Fin 10`
- `structure ProtocolVersion` with fields `major minor patch : VersionDigit`
- `def ValidVersion (v : ProtocolVersion) : Prop := v.major.val ≤ 9 ∧ v.minor.val ≤ 9 ∧ v.patch.val ≤ 9`
- `theorem protocolVersion_valid (v : ProtocolVersion) : ValidVersion v`

## Excluded work

- No `decodeVersion`
- No `JsonValue` pattern matching
- No field name strings
- No `Except`, no `DecodeError`
- No protocol sample, camera, lens, transform
- No changes to Slices 1–3

---

## Allowed definitions

```lean
abbrev VersionDigit := Fin 10

structure ProtocolVersion where
  major : VersionDigit
  minor : VersionDigit
  patch : VersionDigit

def ValidVersion (v : ProtocolVersion) : Prop :=
  v.major.val ≤ 9 ∧ v.minor.val ≤ 9 ∧ v.patch.val ≤ 9
```

## Allowed theorem shapes

```lean
theorem protocolVersion_valid (v : ProtocolVersion) : ValidVersion v
```

## Existing definitions / theorems allowed

- All of Mathlib (via `import Mathlib.Tactic`)
- No imports from other parser slices needed

---

## Proof plan for `protocolVersion_valid`

**Goal shape:** conjunction of three `val ≤ 9` facts.

**Strategy:** `constructor` (or `refine ⟨?_, ?_, ?_⟩`), then close each
branch with `Nat.le_of_lt v.major.isLt` etc.

`v.major.isLt : v.major.val < 10` is the `Fin` constructor invariant.
`Nat.le_of_lt : n < m → n ≤ m - 1` — but `10 - 1 = 9` in ℕ, so
`Nat.le_of_lt v.major.isLt : v.major.val ≤ 9`.

Alternatively: `omega` from `v.major.isLt` in context.

**Automation budget:**
- `omega` — primary (has `isLt` in context, closes `val ≤ 9` immediately)
- `exact Nat.le_of_lt v.major.isLt` — explicit alternative
- No `simp`, no `linarith` expected

---

## Forbidden scope

- No `ValidVersion := True`
- No `valid_version_major_le := v.major = 1` (current-version pinning)
- No decoder
- No `sorry`

---

## Completion conditions

1. `VersionDigit`, `ProtocolVersion`, `ValidVersion` compile without `sorry`.
2. `protocolVersion_valid` compiles without `sorry`.
3. `lake env lean <file>` exits 0.
4. `lake build` succeeds if file is wired into package.
5. No excluded scope introduced.
6. Proof review accepts the result.
7. Work queue marks 4A complete.
8. Ambiguity register updated (done — A11, A12, A13 resolved above).
