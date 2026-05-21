# Proof Capsule — sample-model-shell (Slice 11)

## Parent

Slice 11 of `opentrack-parser-verification`.

## Task classification

**Medium** — twelve structs, no decoder, no theorems.

## Intent

Define the complete Lean data model for the OpenTrackIO sample shell. All
top-level fields are `Option`. Existing invariant-carrying types are reused.
JSON numbers and integers without a wrapper are stored as raw `String`. JSON
booleans are `Bool` or `Option Bool`. No decoder is written here.

## Resolved ambiguities used

- A4 (sample): all fields optional; present nested objects enforce required subfields.
- A8 (sample): full field tree locked for Slice 11.
- A1: rational fields use `{ "num": ..., "denom": ... }` shape → `PositiveRational`.
- A5: timing enums use exact Lean names from Slice 7.

## Formal statements (frozen)

Structs in dependency order. All fields follow A4/A8 type mapping.

```lean
-- Timestamp (timing.sampleTimestamp, timing.recordedTimestamp)
structure Timestamp where
  seconds     : String
  nanoseconds : String

-- SyncOffsets (timing.synchronization.offsets)
structure SyncOffsets where
  translation  : Option String
  rotation     : Option String
  lensEncoders : Option String

-- LeaderPriorities (timing.synchronization.ptp.leaderPriorities)
structure LeaderPriorities where
  priority1 : String
  priority2 : String

-- PtpInfo (timing.synchronization.ptp)
structure PtpInfo where
  profile          : PtpProfile          -- required enum; Slice 7 type
  domain           : String              -- required integer → raw String
  leaderIdentity   : NonemptyString      -- required; MAC-like; regex deferred
  leaderPriorities : LeaderPriorities    -- required sub-object
  leaderAccuracy   : String              -- required number → raw String
  meanPathDelay    : String              -- required number → raw String
  leaderTimeSource : Option PtpLeaderSource  -- optional enum; Slice 7 type
  vlan             : Option String       -- optional integer → raw String

-- Synchronization (timing.synchronization)
structure Synchronization where
  locked    : Bool                       -- required boolean
  source    : SyncSource                 -- required enum; Slice 7 type
  frequency : Option PositiveRational    -- optional rational
  offsets   : Option SyncOffsets         -- optional sub-object
  present   : Option Bool                -- optional boolean
  ptp       : Option PtpInfo             -- optional sub-object

-- Timecode (timing.timecode)
structure Timecode where
  hours     : String                     -- required integer → raw String
  minutes   : String                     -- required integer → raw String
  seconds   : String                     -- required integer → raw String
  frames    : String                     -- required integer → raw String
  frameRate : PositiveRational           -- required rational
  subFrame  : Option String              -- optional integer → raw String
  dropFrame : Option Bool                -- optional boolean

-- Timing
structure Timing where
  mode               : Option TimingMode         -- optional enum; Slice 7 type
  recordedTimestamp  : Option Timestamp          -- optional sub-object
  sampleRate         : Option PositiveRational   -- optional rational
  sampleTimestamp    : Option Timestamp          -- optional sub-object
  sequenceNumber     : Option String             -- optional integer → raw String
  synchronization    : Option Synchronization    -- optional sub-object
  timecode           : Option Timecode           -- optional sub-object

-- StaticTracker (static.tracker)
structure StaticTracker where
  make            : Option NonemptyString
  model           : Option NonemptyString
  serialNumber    : Option NonemptyString
  firmwareVersion : Option NonemptyString

-- StaticInfo (static)
structure StaticInfo where
  duration : Option PositiveRational   -- optional rational
  camera   : Option Camera             -- Slice 9 type
  lens     : Option StaticLens         -- Slice 10 type
  tracker  : Option StaticTracker      -- sub-object above

-- Tracker (top-level tracker)
structure Tracker where
  notes     : Option NonemptyString
  recording : Option Bool
  slate     : Option NonemptyString
  status    : Option NonemptyString

-- GlobalStage
structure GlobalStage where
  E    : String
  N    : String
  U    : String
  lat0 : String
  lon0 : String
  h0   : String

-- Sample (top-level)
structure Sample where
  globalStage      : Option GlobalStage
  lens             : Option Lens                     -- Slice 10 type
  protocol         : Option ProtocolInfo             -- Slice 4C type
  relatedSampleIds : Option (List String)
  sampleId         : Option String
  sourceId         : Option String
  sourceNumber     : Option String
  «static»         : Option StaticInfo
  timing           : Option Timing
  tracker          : Option Tracker
  transforms       : Option (NonemptyArray Transform) -- Slice 8 type
```

## Proof note

No theorems. No `ValidSample` predicate. Invariants are carried by field types:
`PositiveRational`, `NonemptyString`, `NonemptyArray`, and timing enums from
Slice 7. `Bool` is used directly for JSON boolean fields.

## Design decisions

- `static` is a Lean attribute keyword in some contexts; `«static»` (guillemet
  escaping) is used as the field name to avoid ambiguity. The JSON key is still
  `"static"`.
- `Timecode.seconds` shadows the Lean core name `seconds` in no outer scope —
  acceptable as a struct field.
- `SyncSource` and `PtpLeaderSource` are the correct Slice 7 Lean names
  (the resolution message used `SynchronizationSource` and `PtpLeaderTimeSource`
  which were not the implemented names).
- `Synchronization.locked` and `Synchronization.source` are non-optional —
  they are required when the parent object is present.
- `PtpInfo.leaderIdentity` is `NonemptyString` — nonemptiness enforced;
  MAC-pattern regex deferred.

## Deferred

- UUID regex for `sampleId`, `sourceId`, `relatedSampleIds` elements
- MAC-pattern regex for `PtpInfo.leaderIdentity`
- Numeric bounds for all raw `String` number fields
- Integer bounds for all raw `String` integer fields
- Max string lengths
- Unknown-field policy (A3)

## Forbidden

- No decoder in this file.
- No `ValidSample` predicate.
- No `sorry`.
- No changes to Slices 1–10.
