# Proof Capsule — version-decoder (Slice 4B)

## Parent

Slice 4B of `opentrack-parser-verification`.

## Task classification

**Small** — two definitions, one theorem. First slice with `Except`-returning decoder.

## Intent

Decode a `JsonValue` (expected: array of 3 integer digits) into a `ProtocolVersion`.
Prove that any successfully decoded value satisfies `ValidVersion`.

## Resolved ambiguities used

- A11: 3-component version; each digit ∈ [0, 9] encoded as `Fin 10`.
- A12: JSON shape is `.array` of three `.number` string elements.
- A13: `ValidVersion` is non-vacuous; proof delegates to `protocolVersion_valid`.

## Formal statements (frozen)

```lean
def decodeVersionDigit : JsonValue → Except DecodeError VersionDigit
def decodeVersionValue  : JsonValue → Except DecodeError ProtocolVersion

theorem decodeVersionValue_sound :
  decodeVersionValue j = .ok v → ValidVersion v
```

## Proof note

`ValidVersion v` holds for all `v : ProtocolVersion` by `protocolVersion_valid`.
The decoder hypothesis establishes that `v` was produced by the decoder;
validity follows from the type invariant, not from case analysis on `j`.
This is non-vacuous: the theorem asserts the decoder never produces an
out-of-range version, which follows from `Fin 10` preventing it at
construction time.

## Forbidden

- No protocol field name strings in this slice (that is 4C).
- No `sorry`.
- No changes to Slices 1–4A.

---

## Proof plan

### `decodeVersionDigit`

Pattern: `.number s` → parse with `s.toNat?` → range-check with `if h : n < 10`.  
Errors: `expectedNumber` (wrong constructor), `invalidEnum "version" s` (bad value).

### `decodeVersionValue`

Pattern: `.array [a, b, c]` → sequence three `decodeVersionDigit` calls via `do`.  
Errors: `invalidLength "version" 3 xs.length` (wrong count), `expectedArray` (not array).

### `decodeVersionValue_sound`

```lean
theorem decodeVersionValue_sound (j : JsonValue) (v : ProtocolVersion)
    (h : decodeVersionValue j = .ok v) : ValidVersion v :=
  protocolVersion_valid v
```

Hard step: none. `protocolVersion_valid` is already proved in 4A.

Automation budget: none needed for the theorem. `omega` or `exact` for any auxiliary.
