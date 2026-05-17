# Proof Capsule — OpenTrackIO Parser Verification

## Task classification

**Large** — 16 slices, multi-month horizon. Cannot be attempted as a single LAPS task.  
This capsule documents the overall verification goal and governs slice decomposition.

## Mathematical goal

Prove that an OpenTrackIO JSON decoder is *sound*:

```lean
theorem decode_sample_sound :
  decodeSample j = Except.ok s →
  ValidSample s
```

That is: if the decoder accepts a JSON value and returns a sample `s`, then `s`
satisfies all required protocol invariants.

Later (conditional on spec decisions):

```lean
theorem decode_sample_complete :
  JsonConformsToOpenTrackIO j →
  ∃ s, decodeSample j = Except.ok s
```

## Proof strategy

Build bottom-up. Each slice produces one local soundness theorem before it is
composed into a higher-level decoder. Order enforced by the work queue.

1. Invariant-carrying value types (rational wrappers, fixed-length arrays, enums).
2. JSON raw model and error vocabulary.
3. Per-field and per-type decoders with local soundness.
4. Composed record decoders (Version, Camera, Lens, Transform).
5. Top-level `decodeSample` soundness by composition.
6. Error correctness (required fields).
7. Encoder and encode/decode roundtrip (one type at a time).
8. Normalization (only after canonical encoding is stable).
9. Executable/differential harness packaging (future, separate slice).

## Scope boundary

This project verifies semantic decoding from a Lean JSON AST. It does **not**:

- verify a byte-level parser;
- prove the camdkit Python implementation correct;
- verify the C++ mosys implementation;
- prove the battery-tester differential harness correct.

The differential harness is treated as a future packaging slice.

## Excluded until further notice

- `decodeSample` (Slice 12 — not before Slices 1–11 are complete)
- completeness theorem (Slice 16 or later)
- normalization theorem (Slice 16)
- byte/string-level parser
- unknown-field policy (ambiguity not yet resolved)
- duplicate-key semantics (ambiguity not yet resolved)

## Dependencies on camdkit spec

Slices 2–12 require that the normative JSON field names, value types, required/optional
status, and enumeration spellings are fixed by the OpenTrackIO spec.  
These are recorded as ambiguities in `ambiguity-register.md`.

## Lean toolchain

Same as the existing proof files: Lean 4 + Mathlib, pinned in `lean-toolchain` and `lakefile.toml`.
Only standard Mathlib tactics (`field_simp`, `ring`, `linarith`, `nlinarith`, `norm_num`,
`omega`, `simp`, `decide`) are allowed. No custom tactics or axioms.
