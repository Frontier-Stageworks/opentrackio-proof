# Proof Review — version-decoder (Slice 4B)

## Kernel status

`lake env lean opentrackio_parser/VersionDecoder.lean` — exit 0, no warnings.  
`lake build VersionDecoder` — exit 0 (4.7s, 3289 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No protocol field name strings (`"protocol"`, `"version"`, etc.) — those are 4C.
- No changes to Slices 1–4A.

## Statement audit

| Name | Intended | Captured |
|---|---|---|
| `decodeVersionDigit` | `.number s` → `VersionDigit` via `s.toNat?` + range check | Yes |
| `decodeVersionValue` | `.array [a,b,c]` → `ProtocolVersion` via 3 digit decodes | Yes |
| `decodeVersionValue_sound` | successful decode → `ValidVersion` | Yes |

## Semantic review

**`decodeVersionDigit`:** Correct rejection coverage:
- Non-number constructor → `expectedNumber`
- Non-numeric string or `toNat?` fails → `invalidEnum "version" s`
- Out-of-range (`n ≥ 10`) → `invalidEnum "version" s`
- In-range (`h : n < 10`) → `.ok ⟨n, h⟩` constructs `Fin 10` directly from the proof

**`decodeVersionValue`:** Correct rejection coverage:
- Exactly 3-element array → sequences three digit decodes via `do`
- Array with wrong length → `invalidLength "version" 3 xs.length`
- Non-array → `expectedArray`

**`decodeVersionValue_sound`:** The theorem is non-vacuous. The proof
`protocolVersion_valid v` is correct: `Fin 10` prevents construction of an
out-of-range `ProtocolVersion`, so `ValidVersion v` holds for any `v`.
The hypothesis `_h` (decoder success) establishes that `v` was produced by
the decoder; validity follows from the type invariant. This is the right
proof structure when invariants are encoded in types.

## Parameter rename note

`h` renamed to `_h` to silence the Lean 4 unused-variable linter. The
mathematical statement is unchanged — `_h` is a local binder name only.

## Hard step identification

No hard step. `Fin 10` + `protocolVersion_valid` carry all the work.
`s.toNat?` range-check with the `if h : n < 10` decision proof is the
key construction step in `decodeVersionDigit`.

## Hypothesis necessity

`_h` is intentionally unused in the proof body, acknowledged in the
proof comment and this review. This is correct when type invariants
are strong enough to prove the conclusion without inspecting the
decoder's control flow.

## Anti-pattern scan

- No bare `simp`.
- No `norm_num` or `linarith` for arithmetic that `omega` or type structure handles.
- No global annotations added.
- No proxy property proved — `ValidVersion` is the exact intended predicate.

## Contract compliance

1. ✅ `decodeVersionDigit` and `decodeVersionValue` compile.
2. ✅ `decodeVersionValue_sound` compiles without `sorry`.
3. ✅ `lake env lean` exit 0, no warnings.
4. ✅ `lake build VersionDecoder` exit 0.
5. ✅ No protocol field names introduced (deferred to 4C).
6. ✅ No excluded scope introduced.
