# Proof Review — sample-decoder-complete (Slice 14.8)

## Acceptance criteria

| Criterion | Result |
|---|---|
| `lake env lean opentrackio_parser/SampleDecoder.lean` — exit 0, no warnings | PASS |
| `lake build SampleDecoder` — exit 0 | PASS |
| No `sorry` or forbidden constructs | PASS |
| All five existing theorems still compile | PASS |

## Review

**Changes**: Three new imports added (`GlobalStageDecoder`, `TrackerDecoder`, `TimingDecoder`). `decodeStaticInfo` gains `stracker` via `decodeStaticTracker`. `decodeSample` gains three new `←` bindings for `globalStage`, `timing`, `tracker`; the `return` struct updated accordingly.

**`decodeStaticInfo`**: `tracker` now wired via `decodeStaticTracker` (Slice 14.3). Pattern is identical to `duration`, `camera`, `lens` — `←` + `.map some`.

**`decodeSample`**: All eleven `Sample` fields are now wired. `globalStage` via `decodeGlobalStage` (Slice 14.2), `timing` via `decodeTiming` (Slice 14.7), `tracker` via `decodeTracker` (Slice 14.3). No field remains `none` by default.

**Theorems**: All five existing soundness theorems compile unchanged. They reference `decodeSample` by name and prove properties of fields that were already wired in Slice 12A — the new fields are orthogonal.

**No new theorems**: The three newly wired fields are all `Option` with no additional struct-level invariants.

## Verdict

ACCEPTED. `decodeSample` is now complete — all fields wired.
