# Proof Capsule — compose-decoder-soundness / 12B: composed-soundness

## Intent

Prove that any `Sample` returned by `decodeSample` has its invariant-carrying
fields inhabited by values that satisfy their invariants. Because invariants
live in the types (not in `Valid` predicates), every proof is a one-liner that
reads a struct field directly. The decoder hypothesis is unused in all theorems.
No bind archaeology.

## File and lakefile entry

12B adds theorems to the existing `SampleDecoder.lean`. No new file.
No new lakefile entry.

## Frozen formal statements

Five theorems, one per invariant-carrying component kind:

### T1 — Transforms nonemptiness

```lean
theorem decodeSample_transforms_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (ts : NonemptyArray Transform) (_ : s.transforms = some ts) :
    ts.values ≠ [] :=
  ts.nonempty
```

### T2 — Protocol version validity

```lean
theorem decodeSample_protocol_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (p : ProtocolInfo) (_ : s.protocol = some p) :
    ValidVersion p.version :=
  protocolVersion_valid p.version
```

### T3 — Lens encoders anyPresent

```lean
theorem decodeSample_lens_encoders_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (l : Lens) (_ : s.lens = some l)
    (fiz : FizOptions) (_ : l.encoders = some fiz) :
    fiz.focus ≠ none ∨ fiz.iris ≠ none ∨ fiz.zoom ≠ none :=
  fiz.anyPresent
```

### T4 — Static duration positivity

```lean
theorem decodeSample_static_duration_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (st : StaticInfo) (_ : s.«static» = some st)
    (r : PositiveRational) (_ : st.duration = some r) :
    0 < r.toReal :=
  positive_rational_toReal_pos r
```

### T5 — Static camera captureFrameRate positivity

```lean
theorem decodeSample_static_camera_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (st : StaticInfo) (_ : s.«static» = some st)
    (c : Camera) (_ : st.camera = some c)
    (r : PositiveRational) (_ : c.captureFrameRate = some r) :
    0 < r.toReal :=
  positive_rational_toReal_pos r
```

## Why these five

Each theorem targets one invariant-carrying type already proved by a component
decoder: `NonemptyArray` (Slice 6), `ProtocolVersion` (Slice 4A), `FizOptions`
(Slice 10), `PositiveRational` (Slice 1/5). These are the only structural
invariants present in the decoded `Sample` fields wired by 12A. Raw `String`
fields carry no formal invariant; `Bool` fields carry none; deferred fields are
`none` and excluded.

## Proof strategy

All five proofs read a struct field directly. Pattern:
- `ts.nonempty` — `NonemptyArray.nonempty : values ≠ []`
- `protocolVersion_valid p.version` — closes by `Fin 10` digit-bound
- `fiz.anyPresent` — `FizOptions.anyPresent : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none`
- `positive_rational_toReal_pos r` — closes by `num_pos` and `den_pos`

The decoder hypothesis `_h` is unnamed (`_`) in every theorem signature and
intentionally unused in every proof. No `Except.bind` tracing required.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No `open Classical`.
- No new decoders or structs.
- No changes to Slices 1–11.5 or to `decodeStaticInfo`/`decodeRelatedId`.

## Stop rule

If any theorem fails to type-check, diagnose the single failing theorem before
attempting any fix. Most likely failure: a name is wrong or a hypothesis is
miscounted. Do not restructure all five theorems at once.

## Acceptance criteria

1. `lake env lean opentrackio_parser/SampleDecoder.lean` — exit 0, no warnings.
2. `lake build SampleDecoder` — exit 0.
3. All five theorems check without `sorry`.
