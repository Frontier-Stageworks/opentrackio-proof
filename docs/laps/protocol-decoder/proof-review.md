# Proof Review — protocol-decoder (Slice 4C)

## Kernel status

`lake env lean opentrackio_parser/ProtocolDecoder.lean` — exit 0, no warnings.  
`lake build ProtocolDecoder` — exit 0 (3.0s, 3290 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No field strings outside the `protocol` sub-object.
- No changes to Slices 1–4B.

## Statement audit

| Name | Intended | Captured |
|---|---|---|
| `ProtocolInfo` | struct with `name : String` and `version : ProtocolVersion` | Yes |
| `decodeProtocol` | `.object` → lookup `"name"` (string) → lookup `"version"` → delegate to `decodeVersionValue` | Yes |
| `decodeProtocol_sound` | successful decode → `ValidVersion p.version` | Yes |

## Semantic review

**`decodeProtocol`:** Correct rejection coverage:
- Non-object input → `expectedObject`
- Missing `"name"` field → `missingField "name"`
- `"name"` present but not a string → `expectedString`
- Missing `"version"` field → `missingField "version"`
- `"version"` present but malformed → error propagated from `decodeVersionValue`
- Both fields present and well-formed → `.ok { name := n, version := v }`

**`decodeProtocol_sound`:** Non-vacuous for the same reason as `decodeVersionValue_sound`
in Slice 4B: the theorem asserts the decoder never produces an out-of-range version,
which is guaranteed by `Fin 10`. The hypothesis `_h` is intentionally unused — validity
of `p.version` follows from the type invariant, not from inspection of `j`.

## Hard step identification

No hard step. `protocolVersion_valid p.version` carries all the work, delegating
to `Fin 10`'s `isLt` field as in 4A and 4B.

## Anti-pattern scan

- No bare `simp`.
- No `norm_num` or `linarith`.
- No global annotations added.
- No proxy property proved.

## Contract compliance

1. ✅ `ProtocolInfo`, `decodeProtocol` compile.
2. ✅ `decodeProtocol_sound` compiles without `sorry`.
3. ✅ `lake env lean` exit 0, no warnings.
4. ✅ `lake build ProtocolDecoder` exit 0.
5. ✅ No field strings outside the `protocol` sub-object.
6. ✅ No excluded scope introduced.
