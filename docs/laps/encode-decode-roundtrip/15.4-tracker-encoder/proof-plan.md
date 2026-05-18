# Proof Plan — tracker-encoder (Slice 15.4)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/TrackerEncoder.lean` | `TrackerEncoder` |

Appended after `GlobalStageEncoder` in `lakefile.toml`.

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "TrackerEncoder"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  TrackerEncoder.lean — Slice 15.4: tracker-encoder

  Encoders for StaticTracker and Tracker with roundtrip theorems.
  All NonemptyString fields encoded as .string ns.val; omitted when none.
  Roundtrip proofs use rcases to expose nonemptiness hypotheses for dite reduction.

  Ref: docs/laps/encode-decode-roundtrip/15.4-tracker-encoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import TransformModel
import SampleModel
import TrackerDecoder
```

---

## Step 3 — Encoders

```lean
def encodeStaticTracker (st : StaticTracker) : JsonValue :=
  .object ((st.make.map            fun ns => ("make",            .string ns.val)).toList ++
           (st.model.map           fun ns => ("model",           .string ns.val)).toList ++
           (st.serialNumber.map    fun ns => ("serialNumber",    .string ns.val)).toList ++
           (st.firmwareVersion.map fun ns => ("firmwareVersion", .string ns.val)).toList)

def encodeTracker (t : Tracker) : JsonValue :=
  .object ((t.notes.map     fun ns => ("notes",     .string ns.val)).toList ++
           (t.recording.map fun b  => ("recording", .bool b)).toList         ++
           (t.slate.map     fun ns => ("slate",     .string ns.val)).toList  ++
           (t.status.map    fun ns => ("status",    .string ns.val)).toList)
```

---

## Step 4 — Roundtrip theorems

```lean
theorem encodeStaticTracker_roundtrip (st : StaticTracker) :
    decodeStaticTracker (encodeStaticTracker st) = .ok st := by
  obtain ⟨mk, mo, sn, fv⟩ := st
  rcases mk with _ | ⟨mkv, mkh⟩ <;>
  rcases mo with _ | ⟨mov, moh⟩ <;>
  rcases sn with _ | ⟨snv, snh⟩ <;>
  rcases fv with _ | ⟨fvv, fvh⟩ <;>
  simp [encodeStaticTracker, decodeStaticTracker, JsonValue.lookup?,
        decodeOptionalString, *] <;> rfl

theorem encodeTracker_roundtrip (t : Tracker) :
    decodeTracker (encodeTracker t) = .ok t := by
  obtain ⟨no, re, sl, st⟩ := t
  rcases no with _ | ⟨nov, noh⟩ <;>
  rcases sl with _ | ⟨slv, slh⟩ <;>
  rcases st with _ | ⟨stv, sth⟩ <;>
  cases re <;>
  simp [encodeTracker, decodeTracker, JsonValue.lookup?,
        decodeOptionalString, *] <;> rfl
```

### Notes

- `rcases ns with _ | ⟨v, h⟩` handles `Option NonemptyString` in one step,
  exposing `h : v ≠ ""` directly in the `some` branch without a separate `obtain`.
- `simp [*, ...]` includes the nonemptiness hypotheses (`mkh`, `moh`, etc.) so
  `simp` can reduce `dite (v ≠ "") ...` in `decodeOptionalString`.
- `<;> rfl` closes any residual `Except.bind` chains (pattern from Slice 15.2).
- `decodeOptionalString` is `private` in `TrackerDecoder` — it must be referenced
  by its full definition via `simp [decodeOptionalString]` using the unfolded form,
  or the `simp` call may need `show` to expose it. If private visibility blocks
  `simp`, unfold inline by adding the body as a local `have`.
- For `Tracker`, `re : Option Bool` uses plain `cases re` (no `rcases` destructuring
  needed since `Bool` has no proof fields).

---

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/TrackerEncoder.lean` — exit 0, no warnings.
2. `lake build TrackerEncoder` — exit 0.
3. No `sorry` or forbidden constructs.
4. Both roundtrip theorems green.
