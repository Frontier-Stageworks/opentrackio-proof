# Proof Plan — timecode-encoder-roundtrip (Slice 15.6B)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/TimecodeEncoder.lean` | `TimecodeEncoder` |

Entry appended in `lakefile.toml` after `TimecodeDecoder`.

---

## Imports

```lean
import Mathlib
import RationalDecoder
import TimecodeDecoder
import NumericLiteralRoundtrip
```

---

## Encoder definitions

```lean
def encodePositiveRational (r : PositiveRational) : JsonValue :=
  .object [("num",   .number r.num.repr),
           ("denom", .number r.den.repr)]

def encodeTimecode (tc : Timecode) : JsonValue :=
  .object (
    [("hours",     .number tc.hours),
     ("minutes",   .number tc.minutes),
     ("seconds",   .number tc.seconds),
     ("frames",    .number tc.frames),
     ("frameRate", encodePositiveRational tc.frameRate)] ++
    (tc.subFrame.map  fun s => ("subFrame",  .number s)).toList ++
    (tc.dropFrame.map fun b => ("dropFrame", .bool   b)).toList)
```

Note: `r.num.repr` is `Nat.repr r.num`, definitionally equal to `ToString.toString r.num`.
Using `.repr` directly so `nat_repr_toNat?_some` fires without additional unfolding.

---

## Theorem 1: encodePositiveRational_roundtrip

### Statement

```lean
theorem encodePositiveRational_roundtrip (r : PositiveRational) :
    decodePositiveRational (encodePositiveRational r) = .ok r
```

### Proof (VERIFIED via lake env lean --stdin)

```lean
theorem encodePositiveRational_roundtrip (r : PositiveRational) :
    decodePositiveRational (encodePositiveRational r) = .ok r := by
  obtain ⟨n, d, hn, hd⟩ := r
  simp [encodePositiveRational, decodePositiveRational, JsonValue.lookup?,
        nat_repr_toNat?_some, hn, hd]
```

#### Why it closes

1. `obtain ⟨n, d, hn, hd⟩ := r` — destructures to `num = n`, `den = d`, `num_pos = hn`, `den_pos = hd`.
2. `simp [encodePositiveRational]` — unfolds the encoder to `.object [("num", .number n.repr), ("denom", .number d.repr)]`.
3. `simp [decodePositiveRational]` — unfolds the decoder; the `.object _` match fires.
4. `simp [JsonValue.lookup?]` — reduces `List.find?` on the concrete two-element list; "num" is found at index 0, "denom" at index 1.
5. `simp [nat_repr_toNat?_some]` — rewrites `n.repr.toNat?` to `some n` and `d.repr.toNat?` to `some d`.
6. `simp [hn, hd]` — eliminates the `if hn : 0 < n` and `if hd : 0 < d` guards via `if_pos`.
7. Goal reduces to `Except.ok { num := n, den := d, num_pos := hn, den_pos := hd } = Except.ok r`, which is true by `hn`, `hd`, and struct extensionality.

---

## Theorem 2: encodeTimecode_roundtrip

### Statement

```lean
theorem encodeTimecode_roundtrip (tc : Timecode) :
    decodeTimecode (encodeTimecode tc) = .ok tc
```

### Proof (VERIFIED via lake env lean --stdin)

```lean
theorem encodeTimecode_roundtrip (tc : Timecode) :
    decodeTimecode (encodeTimecode tc) = .ok tc := by
  obtain ⟨hours, minutes, seconds, frames, frameRate, subFrame, dropFrame⟩ := tc
  obtain ⟨fn, fd, fnp, fdp⟩ := frameRate
  rcases subFrame with _ | sf <;> rcases dropFrame with _ | df <;>
  simp [encodeTimecode, decodeTimecode, encodePositiveRational, decodePositiveRational,
        JsonValue.lookup?, nat_repr_toNat?_some, fnp, fdp] <;>
  rfl
```

#### Why it closes

1. `obtain` — destructures `tc` and `frameRate` to expose concrete fields.
2. `rcases subFrame ... <;> rcases dropFrame ...` — four cases for the optional fields:
   `(none, none)`, `(none, some df)`, `(some sf, none)`, `(some sf, some df)`.
   In each case the encoded object's field list is concrete.
3. `simp [encodeTimecode, decodeTimecode]` — unfolds both encoder and decoder; the `do` block
   in `decodeTimecode` is desugared and the lookups on the concrete field list are resolved.
4. `simp [encodePositiveRational, decodePositiveRational, ..., nat_repr_toNat?_some, fnp, fdp]` —
   handles the nested `frameRate` roundtrip inline (same mechanism as Theorem 1).
5. `<;> rfl` — closes the four residual goals. After `simp`, the remaining goals are of the form:
   ```
   (do let y ← Except.ok hours; ... Except.ok { hours := y, ... }) = Except.ok { hours := hours, ... }
   ```
   These are definitionally equal (`Except.bind (Except.ok a) f = f a` by `rfl`), so `rfl` closes.

#### Case count justification

- `none/none`: object ends at `("frameRate", ...)` — 5 fields. Both optional lookups return `none`. ✓
- `none/some df`: appends `("dropFrame", .bool df)` — lookup finds it. ✓
- `some sf/none`: appends `("subFrame", .number sf)` — lookup finds it. ✓
- `some sf/some df`: appends both — both lookups succeed. ✓

---

## Acceptance criteria

1. `lake env lean opentrackio_parser/TimecodeEncoder.lean` — exit 0, no warnings.
2. `lake build TimecodeEncoder` — exit 0.
3. Both theorems public, no `sorry`.

## Stop rules

- If `simp` does not reduce `List.find?` on the encoded object, stop and report the residual goal.
- If `rfl` fails on the `do`-bind residual, stop and report.
- Do not change `decodeTimecode` or `decodePositiveRational`.
