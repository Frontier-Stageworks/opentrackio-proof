# Proof Plan — sample-model-shell (Slice 11)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/SampleModel.lean` | `SampleModel` |

One new `[[lean_lib]]` entry added to `lakefile.toml`.

---

## Imports

```lean
import RationalValueWrappers
import TransformModel
import NonemptyArrayDecoder
import TimingEnumDecoders
import ProtocolDecoder
import CameraModel
import LensModel
```

`ProtocolDecoder` is imported for `ProtocolInfo`. `TimingEnumDecoders` provides
`TimingMode`, `SyncSource`, `PtpProfile`, `PtpLeaderSource`. `TransformModel`
provides `NonemptyString` and `Transform`. `NonemptyArrayDecoder` provides
`NonemptyArray`.

---

## Structs (in dependency order)

### Step 1. `Timestamp`

```lean
structure Timestamp where
  seconds     : String
  nanoseconds : String
```

Used for `timing.sampleTimestamp` and `timing.recordedTimestamp`.

### Step 2. `SyncOffsets`

```lean
structure SyncOffsets where
  translation  : Option String
  rotation     : Option String
  lensEncoders : Option String
```

### Step 3. `LeaderPriorities`

```lean
structure LeaderPriorities where
  priority1 : String
  priority2 : String
```

### Step 4. `PtpInfo`

```lean
structure PtpInfo where
  profile          : PtpProfile
  domain           : String
  leaderIdentity   : NonemptyString
  leaderPriorities : LeaderPriorities
  leaderAccuracy   : String
  meanPathDelay    : String
  leaderTimeSource : Option PtpLeaderSource
  vlan             : Option String
```

Six required fields (no `Option`); two optional.

### Step 5. `Synchronization`

```lean
structure Synchronization where
  locked    : Bool
  source    : SyncSource
  frequency : Option PositiveRational
  offsets   : Option SyncOffsets
  present   : Option Bool
  ptp       : Option PtpInfo
```

`locked` and `source` are required (no `Option`) — they are required subfields
when the parent object is present.

### Step 6. `Timecode`

```lean
structure Timecode where
  hours     : String
  minutes   : String
  seconds   : String
  frames    : String
  frameRate : PositiveRational
  subFrame  : Option String
  dropFrame : Option Bool
```

`hours`, `minutes`, `seconds`, `frames`, `frameRate` are required (no `Option`).

### Step 7. `Timing`

```lean
structure Timing where
  mode              : Option TimingMode
  recordedTimestamp : Option Timestamp
  sampleRate        : Option PositiveRational
  sampleTimestamp   : Option Timestamp
  sequenceNumber    : Option String
  synchronization   : Option Synchronization
  timecode          : Option Timecode
```

### Step 8. `StaticTracker`

```lean
structure StaticTracker where
  make            : Option NonemptyString
  model           : Option NonemptyString
  serialNumber    : Option NonemptyString
  firmwareVersion : Option NonemptyString
```

### Step 9. `StaticInfo`

```lean
structure StaticInfo where
  duration : Option PositiveRational
  camera   : Option Camera
  lens     : Option StaticLens
  tracker  : Option StaticTracker
```

### Step 10. `Tracker`

```lean
structure Tracker where
  notes     : Option NonemptyString
  recording : Option Bool
  slate     : Option NonemptyString
  status    : Option NonemptyString
```

### Step 11. `GlobalStage`

```lean
structure GlobalStage where
  E    : String
  N    : String
  U    : String
  lat0 : String
  lon0 : String
  h0   : String
```

All six fields are required when the parent is present (no `Option`).

### Step 12. `Sample`

```lean
structure Sample where
  globalStage      : Option GlobalStage
  lens             : Option Lens
  protocol         : Option ProtocolInfo
  relatedSampleIds : Option (List String)
  sampleId         : Option String
  sourceId         : Option String
  sourceNumber     : Option String
  «static»         : Option StaticInfo
  timing           : Option Timing
  tracker          : Option Tracker
  transforms       : Option (NonemptyArray Transform)
```

`«static»` uses guillemet escaping because `static` has special meaning as a
Lean attribute modifier. The JSON key is still `"static"`.

---

## Stop rule

If any struct fails to elaborate, identify which field is the problem before
attempting any fix. The most likely issues are:

- `«static»` field name syntax — if guillemets are not accepted in structure
  field position, rename to `staticInfo` and note the deviation.
- `Timecode.seconds` — shadowing of a core name is unlikely to be an issue
  in struct field position, but if it is, rename to `secs`.
- Import cycles — if `ProtocolDecoder` or `LensModel` introduce a cycle,
  investigate before adding any new import.
