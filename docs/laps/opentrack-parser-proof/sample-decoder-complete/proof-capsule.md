# Proof Capsule — sample-decoder-complete (Slice 14.8)

## Intent

Complete `decodeSample` by wiring the three deferred fields (`globalStage`, `timing`,
`tracker`) and wiring `StaticInfo.tracker` inside `decodeStaticInfo`. This modifies the
existing `opentrackio_parser/SampleDecoder.lean` — no new file or lakefile entry.

Three new imports are added. The five existing soundness theorems are unchanged.
No new theorems.

## File

`opentrackio_parser/SampleDecoder.lean` — modified in place.

No new `[[lean_lib]]` entry; `SampleDecoder` is already registered.

## New imports

```lean
import GlobalStageDecoder
import TrackerDecoder
import TimingDecoder
```

## Frozen changes

### `decodeStaticInfo` — wire `tracker`

Replace `tracker := none` with:

```lean
      let stracker ←
        match sj.lookup? "tracker" with
        | none    => .ok none
        | some vj => (decodeStaticTracker vj).map some
      return { duration, camera, lens := slens, tracker := stracker }
```

### `decodeSample` — wire `globalStage`, `timing`, `tracker`

Replace the three `none` assignments with:

```lean
      let globalStage ←
        match j.lookup? "globalStage" with
        | none    => .ok none
        | some vj => (decodeGlobalStage vj).map some
      let timing ←
        match j.lookup? "timing" with
        | none    => .ok none
        | some vj => (decodeTiming vj).map some
      let tracker ←
        match j.lookup? "tracker" with
        | none    => .ok none
        | some vj => (decodeTracker vj).map some
```

And update the `return` struct to use these bindings instead of `none`.

## No new theorems

The five existing soundness theorems (`decodeSample_transforms_sound`,
`decodeSample_protocol_sound`, `decodeSample_lens_encoders_sound`,
`decodeSample_static_duration_sound`, `decodeSample_static_camera_sound`) are
unchanged. No new invariants are introduced by wiring `Option` fields.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions.
- No changes to Slices 1–14.7 other than `SampleDecoder.lean` itself.

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/SampleDecoder.lean` — exit 0, no warnings.
2. `lake build SampleDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
4. All five existing theorems still compile.
