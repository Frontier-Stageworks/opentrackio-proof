/-
  SampleModel.lean — Slice 11: sample-model-shell

  Defines the complete Lean data model for the OpenTrackIO sample shell.
  All top-level Sample fields are Option per A4. Existing invariant-carrying
  types are reused. JSON numbers/integers without a wrapper are raw String.
  JSON booleans are Bool or Option Bool. No decoder. No theorems.

  A4: all fields optional; present nested objects enforce required subfields.
  A8: full sample field tree locked for Slice 11.
  Ref: docs/laps/sample-model-shell/proof-capsule.md
-/

import RationalValueWrappers
import TransformModel
import NonemptyArrayDecoder
import TimingEnumDecoders
import ProtocolDecoder
import CameraModel
import LensModel

/-─────────────────────────────────────────────────────────────────────────────
  Timestamp

  Used for timing.sampleTimestamp and timing.recordedTimestamp.
  Both seconds and nanoseconds are required integers stored as raw String.
─────────────────────────────────────────────────────────────────────────────-/

structure Timestamp where
  seconds     : String
  nanoseconds : String

/-─────────────────────────────────────────────────────────────────────────────
  SyncOffsets

  timing.synchronization.offsets — all three fields optional numbers.
─────────────────────────────────────────────────────────────────────────────-/

structure SyncOffsets where
  translation  : Option String
  rotation     : Option String
  lensEncoders : Option String

/-─────────────────────────────────────────────────────────────────────────────
  LeaderPriorities

  timing.synchronization.ptp.leaderPriorities — both fields required integers.
─────────────────────────────────────────────────────────────────────────────-/

structure LeaderPriorities where
  priority1 : String
  priority2 : String

/-─────────────────────────────────────────────────────────────────────────────
  PtpInfo

  timing.synchronization.ptp — six required fields, two optional.
  leaderIdentity is NonemptyString; MAC-pattern regex is deferred.
─────────────────────────────────────────────────────────────────────────────-/

structure PtpInfo where
  profile          : PtpProfile
  domain           : String
  leaderIdentity   : NonemptyString
  leaderPriorities : LeaderPriorities
  leaderAccuracy   : String
  meanPathDelay    : String
  leaderTimeSource : Option PtpLeaderSource
  vlan             : Option String

/-─────────────────────────────────────────────────────────────────────────────
  Synchronization

  timing.synchronization — locked and source are required when parent present.
─────────────────────────────────────────────────────────────────────────────-/

structure Synchronization where
  locked    : Bool
  source    : SyncSource
  frequency : Option PositiveRational
  offsets   : Option SyncOffsets
  present   : Option Bool
  ptp       : Option PtpInfo

/-─────────────────────────────────────────────────────────────────────────────
  Timecode

  timing.timecode — hours/minutes/seconds/frames/frameRate required.
─────────────────────────────────────────────────────────────────────────────-/

structure Timecode where
  hours     : String
  minutes   : String
  seconds   : String
  frames    : String
  frameRate : PositiveRational
  subFrame  : Option String
  dropFrame : Option Bool

/-─────────────────────────────────────────────────────────────────────────────
  Timing

  All seven fields are Option for consumers.
─────────────────────────────────────────────────────────────────────────────-/

structure Timing where
  mode              : Option TimingMode
  recordedTimestamp : Option Timestamp
  sampleRate        : Option PositiveRational
  sampleTimestamp   : Option Timestamp
  sequenceNumber    : Option String
  synchronization   : Option Synchronization
  timecode          : Option Timecode

/-─────────────────────────────────────────────────────────────────────────────
  StaticTracker

  static.tracker — four optional nonempty string fields.
─────────────────────────────────────────────────────────────────────────────-/

structure StaticTracker where
  make            : Option NonemptyString
  model           : Option NonemptyString
  serialNumber    : Option NonemptyString
  firmwareVersion : Option NonemptyString

/-─────────────────────────────────────────────────────────────────────────────
  StaticInfo

  static — reuses Camera (Slice 9), StaticLens (Slice 10), StaticTracker.
─────────────────────────────────────────────────────────────────────────────-/

structure StaticInfo where
  duration : Option PositiveRational
  camera   : Option Camera
  lens     : Option StaticLens
  tracker  : Option StaticTracker

/-─────────────────────────────────────────────────────────────────────────────
  Tracker

  Top-level tracker — dynamic fields distinct from static.tracker.
─────────────────────────────────────────────────────────────────────────────-/

structure Tracker where
  notes     : Option NonemptyString
  recording : Option Bool
  slate     : Option NonemptyString
  status    : Option NonemptyString

/-─────────────────────────────────────────────────────────────────────────────
  GlobalStage

  All six fields required when parent object is present.
─────────────────────────────────────────────────────────────────────────────-/

structure GlobalStage where
  E    : String
  N    : String
  U    : String
  lat0 : String
  lon0 : String
  h0   : String

/-─────────────────────────────────────────────────────────────────────────────
  Sample

  Top-level sample. All eleven fields are Option per A4.
  «static» uses guillemet escaping; the JSON key is "static".
─────────────────────────────────────────────────────────────────────────────-/

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
