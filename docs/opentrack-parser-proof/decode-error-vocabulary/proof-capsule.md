# Proof Capsule — decode-error-vocabulary

## Parent

Slice 3 of `opentrack-parser-verification`.  
Plan: [opentrack-parser-plan.md](../opentrack-parser-plan.md)

## Task classification

**Small** — one inductive type, no theorems. Derives `Repr` and `DecidableEq`.

## Intent

Establish the vocabulary of structured reasons a decoder can reject input.
This is a pure definition slice; no decoder, no protocol model, no proofs.

The constructors track what can go wrong during OpenTrackIO decoding:
- Wrong JSON constructor for a field
- Missing required field
- Malformed rational value
- Unknown enum string
- Wrong-length array
- Duplicate object key (A2 policy: duplicate keys are a decoding error)

## A2 note

`duplicateKey : String → DecodeError` is added here because A2 is now resolved:
duplicate keys are a decoding error. The plan predated A2 resolution and
omitted this constructor. Adding it now is the correct place.

## Formal definition (frozen)

```lean
inductive DecodeError where
  | expectedObject
  | expectedArray
  | expectedString
  | expectedNumber
  | missingField    : String → DecodeError
  | duplicateKey    : String → DecodeError
  | invalidRational : String → DecodeError
  | invalidEnum     : String → String → DecodeError
  | invalidLength   : String → Nat → Nat → DecodeError
  deriving Repr, DecidableEq
```

## Theorems

None required. `DecidableEq` is derived, providing decidable equality
without a manual proof.

## Forbidden

- No decoder implementation.
- No soundness theorem.
- No protocol model.
- No changes to Slices 1–2.
- No `sorry`.
