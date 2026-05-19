# Proof Capsule — encoder-version (Slice 14)

## Intent

Define encoders for `ProtocolVersion` and `ProtocolInfo` that produce the
exact `JsonValue` shape expected by the corresponding decoders. Prove
encode-then-decode roundtrip theorems: `decode (encode x) = .ok x`. No new
types. No changes to existing decoders.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/VersionEncoder.lean` | `VersionEncoder` |

One new `[[lean_lib]]` entry appended after `ErrorCorrectness` in `lakefile.toml`.

## Frozen formal statements

### E1 — Version digit encoder

```lean
def encodeVersionDigit (d : VersionDigit) : JsonValue :=
  .number (toString d.val)
```

### E2 — Version value encoder

```lean
def encodeVersionValue (v : ProtocolVersion) : JsonValue :=
  .array [encodeVersionDigit v.major, encodeVersionDigit v.minor, encodeVersionDigit v.patch]
```

### E3 — Protocol encoder

```lean
def encodeProtocol (p : ProtocolInfo) : JsonValue :=
  .object [("name", .string p.name), ("version", encodeVersionValue p.version)]
```

### R1 — Version digit roundtrip

```lean
theorem encodeVersionDigit_roundtrip (d : VersionDigit) :
    decodeVersionDigit (encodeVersionDigit d) = .ok d
```

### R2 — Version value roundtrip

```lean
theorem encodeVersionValue_roundtrip (v : ProtocolVersion) :
    decodeVersionValue (encodeVersionValue v) = .ok v
```

### R3 — Protocol roundtrip

```lean
theorem encodeProtocol_roundtrip (p : ProtocolInfo) :
    decodeProtocol (encodeProtocol p) = .ok p
```

## Proof strategy notes

**R1** is the load-bearing lemma. `decodeVersionDigit (.number (toString d.val))`
must reduce to `.ok d`. This requires `(toString d.val).toNat? = some d.val`
and `d.val < 10` (carried by `d.isLt`). The Mathlib lemma
`Nat.toNat?_toString` or `String.toNat?_ofNat` (exact name TBD at plan time)
closes the `toNat?` step; `d.isLt` closes the `< 10` guard; `Fin.ext` closes
`⟨d.val, _⟩ = d`. If the Mathlib lemma name is wrong, try `simp [toString,
Nat.repr]` or `decide` on the 10 concrete cases.

**R2** reduces to three applications of R1 plus `do`-bind simplification.

**R3** reduces to R2 plus `lookup?` evaluation on the two-element list.
`lookup?` on `[("name", ...), ("version", ...)]` is a linear scan; `simp
[JsonValue.lookup?]` should suffice.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No `open Classical`.
- No new types.
- No changes to Slices 1–13.

## Stop rule

R1 is the hardest theorem. If the `toNat?`/`toString` roundtrip lemma cannot
be found or `simp` cannot close it, stop and report before attempting R2 or R3.

## Acceptance criteria

1. `lake env lean opentrackio_parser/VersionEncoder.lean` — exit 0, no warnings.
2. `lake build VersionEncoder` — exit 0.
3. All three encoders and three roundtrip theorems compile without `sorry`.
