# Proof Plan — encoder-version (Slice 14)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/VersionEncoder.lean` | `VersionEncoder` |

Appended after `ErrorCorrectness` in `lakefile.toml`.

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "VersionEncoder"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  VersionEncoder.lean — Slice 14: encoder-version

  Encoders for ProtocolVersion and ProtocolInfo, and encode-then-decode
  roundtrip theorems. No new types. No changes to existing decoders.

  Ref: docs/laps/encoder-version/proof-capsule.md
-/

import Mathlib.Tactic
import DecodeError
import JsonRawModel
import ProtocolVersion
import VersionDecoder
import ProtocolDecoder
```

---

## Step 3 — Three encoders

```lean
def encodeVersionDigit (d : VersionDigit) : JsonValue :=
  .number (toString d.val)

def encodeVersionValue (v : ProtocolVersion) : JsonValue :=
  .array [encodeVersionDigit v.major, encodeVersionDigit v.minor, encodeVersionDigit v.patch]

def encodeProtocol (p : ProtocolInfo) : JsonValue :=
  .object [("name", .string p.name), ("version", encodeVersionValue p.version)]
```

---

## Step 4 — R1: Version digit roundtrip

`decodeVersionDigit (.number (toString d.val))` must parse the string back to
`d`. For `d : Fin 10` there are exactly 10 cases, all computable.

```lean
theorem encodeVersionDigit_roundtrip (d : VersionDigit) :
    decodeVersionDigit (encodeVersionDigit d) = .ok d := by
  fin_cases d <;> decide
```

`fin_cases d` opens 10 goals (d = 0 through 9). `decide` closes each by
kernel reduction: `toString 0 = "0"`, `"0".toNat? = some 0`, `0 < 10` → `⟨0, _⟩`.

---

## Step 5 — R2: Version value roundtrip

`encodeVersionValue v` produces `.array [encodeVersionDigit v.major, ...]`.
`decodeVersionValue` matches the 3-element array arm, binds three
`decodeVersionDigit` calls, and returns `{ major, minor, patch }`.

```lean
theorem encodeVersionValue_roundtrip (v : ProtocolVersion) :
    decodeVersionValue (encodeVersionValue v) = .ok v := by
  simp [decodeVersionValue, encodeVersionValue, encodeVersionDigit_roundtrip]
```

`simp` unfolds both defs, rewrites each `decodeVersionDigit (encodeVersionDigit v.X)`
to `.ok v.X` via `encodeVersionDigit_roundtrip`, then reduces the `Except.bind`
chain and closes `{ major := v.major, minor := v.minor, patch := v.patch } = v`
by `rfl`.

Fallback if `simp` cannot reduce the `do`/`bind` chain:

```lean
  unfold decodeVersionValue encodeVersionValue
  rw [encodeVersionDigit_roundtrip, encodeVersionDigit_roundtrip,
      encodeVersionDigit_roundtrip]
  rfl
```

---

## Step 6 — R3: Protocol roundtrip

`encodeProtocol p` produces `.object [("name", .string p.name), ("version", ...)]`.
`decodeProtocol` uses `lookup?` which calls `List.find?` with `==`.
On a two-element list the first lookup reduces to `some (.string p.name)` and
the second to `some (encodeVersionValue p.version)`.

```lean
theorem encodeProtocol_roundtrip (p : ProtocolInfo) :
    decodeProtocol (encodeProtocol p) = .ok p := by
  simp [decodeProtocol, encodeProtocol, JsonValue.lookup?,
        encodeVersionValue_roundtrip]
```

`simp` unfolds `decodeProtocol` and `encodeProtocol`, reduces both `lookup?`
calls via `List.find?` on concrete keys, rewrites the version sub-decode
via `encodeVersionValue_roundtrip`, and closes `{ name := p.name, version := p.version } = p`
by `rfl`.

Fallback if `lookup?`/`find?` reductions need explicit help:

```lean
  unfold decodeProtocol encodeProtocol
  simp [JsonValue.lookup?, List.find?, encodeVersionValue_roundtrip]
```

---

## Stop rule

R1 must pass before R2 or R3 are attempted. At each failure, diagnose before
trying an alternative.

## Acceptance criteria

1. `lake env lean opentrackio_parser/VersionEncoder.lean` — exit 0, no warnings.
2. `lake build VersionEncoder` — exit 0.
3. Three encoders and three roundtrip theorems compile without `sorry`.
