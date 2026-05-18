# Proof Review — sample-model-shell (Slice 11)

## Kernel status

`lake env lean opentrackio_parser/SampleModel.lean` — exit 0, no warnings.
`lake build SampleModel` — exit 0 (7.6s, 3297 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No decoder.
- No theorems.
- No `ValidSample` predicate.
- No changes to Slices 1–10.

## Statement audit

| Name | Intended | Captured |
|---|---|---|
| `Timestamp` | `seconds nanoseconds : String` (required integers) | Yes |
| `SyncOffsets` | `translation rotation lensEncoders : Option String` | Yes |
| `LeaderPriorities` | `priority1 priority2 : String` (required integers) | Yes |
| `PtpInfo` | 6 required fields; 2 optional; `leaderIdentity : NonemptyString` | Yes |
| `Synchronization` | `locked : Bool` and `source : SyncSource` required; 4 optional | Yes |
| `Timecode` | 4 required integer strings + `frameRate : PositiveRational`; 2 optional | Yes |
| `Timing` | 7 optional fields | Yes |
| `StaticTracker` | 4 `Option NonemptyString` fields | Yes |
| `StaticInfo` | `duration camera lens tracker` all `Option` | Yes |
| `Tracker` | 3 `Option NonemptyString` + `recording : Option Bool` | Yes |
| `GlobalStage` | 6 required `String` fields | Yes |
| `Sample` | 11 `Option` fields; `«static» : Option StaticInfo` | Yes |

## Enum type name audit

| Field | Used type | Slice 7 name | Correct |
|---|---|---|---|
| `Synchronization.source` | `SyncSource` | `SyncSource` | ✅ |
| `PtpInfo.profile` | `PtpProfile` | `PtpProfile` | ✅ |
| `PtpInfo.leaderTimeSource` | `Option PtpLeaderSource` | `PtpLeaderSource` | ✅ |
| `Timing.mode` | `Option TimingMode` | `TimingMode` | ✅ |

Resolution message used `SynchronizationSource` and `PtpLeaderTimeSource` —
both corrected to the actual Slice 7 Lean names.

## Required-field audit

Fields that are non-optional when their parent object is present:

| Struct | Required fields |
|---|---|
| `Timestamp` | `seconds`, `nanoseconds` |
| `LeaderPriorities` | `priority1`, `priority2` |
| `PtpInfo` | `profile`, `domain`, `leaderIdentity`, `leaderPriorities`, `leaderAccuracy`, `meanPathDelay` |
| `Synchronization` | `locked`, `source` |
| `Timecode` | `hours`, `minutes`, `seconds`, `frames`, `frameRate` |
| `GlobalStage` | `E`, `N`, `U`, `lat0`, `lon0`, `h0` |

## Design note: `«static»` field name

`Sample.«static»` uses Lean 4 guillemet escaping because `static` has special
meaning as an attribute modifier. The JSON key remains `"static"`. The syntax
compiled without issue — exit 0, no warnings.

## Design note: invariants in types

- `PtpInfo.leaderIdentity : NonemptyString` — nonemptiness enforced at type
  level; MAC-pattern regex deferred per guardrail.
- `Timecode.frameRate : PositiveRational` — positivity enforced at type level.
- `Synchronization.frequency : Option PositiveRational` — positivity enforced
  when present.
- `StaticInfo.duration : Option PositiveRational` — same.
- `Bool` and `Option Bool` used directly for JSON boolean fields
  (`locked`, `present`, `recording`, `dropFrame`). `JsonValue.bool` constructor
  exists in the raw model (Slice 2); decoder use is deferred to a later slice.

## Deferred (confirmed absent)

- UUID regex for `sampleId`, `sourceId`, `relatedSampleIds` elements ✓
- MAC-pattern proof for `PtpInfo.leaderIdentity` ✓
- Numeric/integer bounds for all raw `String` fields ✓
- Max string lengths ✓
- Unknown-field policy (A3) ✓

## Contract compliance

1. ✅ All twelve structs compile.
2. ✅ No `sorry` or forbidden constructs.
3. ✅ `lake env lean` exit 0, no warnings.
4. ✅ `lake build SampleModel` exit 0.
5. ✅ No decoder or theorems introduced.
6. ✅ All fields match A4/A8 sample resolution exactly.
7. ✅ Correct Slice 7 enum names used throughout.
8. ✅ `«static»` guillemet syntax accepted by Lean 4.
