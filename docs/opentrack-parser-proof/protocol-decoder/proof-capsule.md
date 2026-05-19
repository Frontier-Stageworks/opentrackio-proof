# Proof Capsule — protocol-decoder (Slice 4C)

## Parent

Slice 4C of `opentrack-parser-verification`.

## Task classification

**Small** — one struct, one decoder, one theorem.

## Intent

Decode a `JsonValue` (expected: object with required `"name"` string and `"version"`
array sub-fields) into a `ProtocolInfo`. Prove that any successfully decoded value
has a valid version.

## Resolved ambiguities used

- A8 (partial): normative sub-field keys are `"name"` (string) and `"version"` (array);
  both required when the `protocol` object is present.
- A11, A12, A13: inherited from Slice 4B via delegation to `decodeVersionValue`.

## Formal statements (frozen)

```lean
structure ProtocolInfo where
  name    : String
  version : ProtocolVersion

def decodeProtocol (j : JsonValue) : Except DecodeError ProtocolInfo

theorem decodeProtocol_sound :
  decodeProtocol j = .ok p → ValidVersion p.version
```

## Proof note

`ValidVersion p.version` holds for any `p : ProtocolInfo` by `protocolVersion_valid`.
The proof structure is identical to `decodeVersionValue_sound` in Slice 4B: the
decoder hypothesis `_h` establishes that `p` was produced by the decoder; validity
follows from the `Fin 10` type invariant, not from case analysis on `j`.

## Forbidden

- No `sorry`.
- No changes to Slices 1–4B.
- No field strings for fields outside the `protocol` sub-object (deferred to Slices 9–12).
