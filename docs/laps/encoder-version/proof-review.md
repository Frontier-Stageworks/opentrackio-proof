# Proof Review — encoder-version (Slice 14)

## Kernel status

`lake env lean opentrackio_parser/VersionEncoder.lean` — exit 0, no warnings.
`lake build VersionEncoder` — exit 0 (4.4s, 3291 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No `open Classical`.
- No new types.
- No changes to Slices 1–13.

## Plan deviations (recorded)

| Plan | Actual | Reason |
|---|---|---|
| R1: `fin_cases d <;> decide` | `fin_cases d <;> native_decide` | `toString (n : Nat)` does not reduce in the kernel; `native_decide` compiles to native code and succeeds |
| R2: `simp [... encodeVersionDigit_roundtrip]` | `simp [...]; rfl` | `simp` rewrites the three digit calls but leaves the `do`/`Except.bind` chain; `rfl` closes it since `Except.bind (.ok x) f = f x` is definitional |
| R2: `Except.bind` in simp args | Removed (unused, generated warning) | Lean already reduces `Except.bind` definitionally once the goal reaches `rfl` |

## Encoder audit

| Def | Shape produced | Used by |
|---|---|---|
| `encodeVersionDigit d` | `.number (toString d.val)` | `encodeVersionValue` |
| `encodeVersionValue v` | `.array [digit, digit, digit]` | `encodeProtocol` |
| `encodeProtocol p` | `.object [("name", .string p.name), ("version", ...)]` | R3 roundtrip |

## Theorem audit

| Theorem | Tactic | `sorry` | Notes |
|---|---|---|---|
| `encodeVersionDigit_roundtrip` | `fin_cases d <;> native_decide` | No | 10 concrete cases; `toString` only reduces via native code |
| `encodeVersionValue_roundtrip` | `simp [...]; rfl` | No | Chains R1 three times; `rfl` closes monadic residual |
| `encodeProtocol_roundtrip` | `simp [decodeProtocol, encodeProtocol, JsonValue.lookup?, encodeVersionValue_roundtrip]` | No | `lookup?` / `List.find?` reduces on concrete keys |

## Contract compliance

1. ✅ `lake env lean` exit 0, no warnings.
2. ✅ `lake build VersionEncoder` exit 0.
3. ✅ All three encoders and three roundtrip theorems compile without `sorry`.
4. ✅ No forbidden constructs.
5. ✅ No changes to prior slices.
