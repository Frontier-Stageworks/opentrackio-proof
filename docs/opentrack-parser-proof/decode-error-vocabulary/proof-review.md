# Proof Review — decode-error-vocabulary

## Kernel status

`lake env lean opentrackio_parser/DecodeError.lean` — exit 0, no warnings.  
`lake build DecodeError` — exit 0 (3 jobs, 233ms).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No decoder, no protocol model, no soundness theorem.
- Slices 1–2 unchanged.

## Definition audit

All nine constructors from the capsule are present. `duplicateKey : String → DecodeError`
was added relative to the original plan — justified by A2 resolution (duplicate
keys are a decoding error). This is the correct place to introduce it.

`deriving Repr, DecidableEq` provides decidable equality without a manual proof,
which is needed by later decoder slices that pattern-match on errors.

## Semantic review

Each constructor names a distinct failure mode:

| Constructor | Meaning |
|---|---|
| `expectedObject` | JSON value is not an object where one was required |
| `expectedArray` | JSON value is not an array where one was required |
| `expectedString` | JSON value is not a string where one was required |
| `expectedNumber` | JSON value is not a number where one was required |
| `missingField k` | Required field `k` is absent from an object |
| `duplicateKey k` | Object contains more than one field with key `k` |
| `invalidRational s` | String `s` cannot be parsed as a valid rational |
| `invalidEnum field val` | Value `val` is not a legal enum string for field `field` |
| `invalidLength field expected actual` | Array length mismatch |

No constructor is redundant or misaligned with the intended decoding failure modes.

## Contract compliance

1. ✅ `DecodeError` compiles without `sorry`.
2. ✅ `lake env lean` exit 0.
3. ✅ `lake build DecodeError` exit 0.
4. ✅ No excluded scope introduced.
5. ✅ A2 addition (`duplicateKey`) documented in capsule.
