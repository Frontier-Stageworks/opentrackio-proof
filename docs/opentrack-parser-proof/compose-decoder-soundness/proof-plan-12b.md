# Proof Plan — compose-decoder-soundness / 12B: composed-soundness

## File

Theorems appended to `opentrackio_parser/SampleDecoder.lean`.
No new file. No new lakefile entry.

---

## Step 1 — Append section header and five theorems

Add the following block after the closing line of `decodeSample`:

```lean
/-─────────────────────────────────────────────────────────────────────────────
  Composed soundness theorems

  All five proofs read a struct field directly. The decoder hypothesis _h
  is unused in every case — invariants live in the types, not in Valid
  predicates, so no Except.bind tracing is required.
─────────────────────────────────────────────────────────────────────────────-/

theorem decodeSample_transforms_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (ts : NonemptyArray Transform) (_ : s.transforms = some ts) :
    ts.values ≠ [] :=
  ts.nonempty

theorem decodeSample_protocol_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (p : ProtocolInfo) (_ : s.protocol = some p) :
    ValidVersion p.version :=
  protocolVersion_valid p.version

theorem decodeSample_lens_encoders_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (l : Lens) (_ : s.lens = some l)
    (fiz : FizOptions) (_ : l.encoders = some fiz) :
    fiz.focus ≠ none ∨ fiz.iris ≠ none ∨ fiz.zoom ≠ none :=
  fiz.anyPresent

theorem decodeSample_static_duration_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (st : StaticInfo) (_ : s.«static» = some st)
    (r : PositiveRational) (_ : st.duration = some r) :
    0 < r.toReal :=
  positive_rational_toReal_pos r

theorem decodeSample_static_camera_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (st : StaticInfo) (_ : s.«static» = some st)
    (c : Camera) (_ : st.camera = some c)
    (r : PositiveRational) (_ : c.captureFrameRate = some r) :
    0 < r.toReal :=
  positive_rational_toReal_pos r
```

---

## Stop rule

If any theorem fails, diagnose the single failing theorem only.
Do not touch the others until the failure is understood.

## Acceptance criteria

1. `lake env lean opentrackio_parser/SampleDecoder.lean` — exit 0, no warnings.
2. `lake build SampleDecoder` — exit 0.
3. All five theorems check without `sorry`.
