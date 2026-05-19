/-
  HarnessAdapter.lean — Slice 18: battery-tester-lean-adapter

  Extracts the 18 battery-tester comparison fields from a decoded Sample and
  renders them as TSV (tab-separated "field\tvalue\n" lines).

  Called from a generated Lean runner via:
    lake env lean --run <generated-runner>.lean

  No new proofs. No sorry, admit, axiom, unsafe, partial.
  Ref: docs/opentrack-parser-proof/executable-harness/slice18-lean-adapter.md
-/

import SampleDecoder

/-─────────────────────────────────────────────────────────────────────────────
  Helpers
─────────────────────────────────────────────────────────────────────────────-/

private def opt (v : Option String) : String := v.getD "null"

private def renderVersion (v : ProtocolVersion) : String :=
  s!"{v.major.val}.{v.minor.val}.{v.patch.val}"

private def padTwo (s : String) : String :=
  if s.length < 2 then "0" ++ s else s

private def renderTimecode (tc : Timecode) : String :=
  s!"{padTwo tc.hours}:{padTwo tc.minutes}:{padTwo tc.seconds}:{padTwo tc.frames}"

private def renderRational (r : PositiveRational) : String :=
  s!"{r.num}/{r.den}"

private def findCamera (ts : List Transform) : Option Transform :=
  ts.find? (fun t => t.id.map (·.val) == some "Camera")

/-─────────────────────────────────────────────────────────────────────────────
  renderComparisonFields

  Decodes j, then extracts all 18 comparison fields.
  Fields absent from the decoded Sample are emitted as "null".
  On decode failure, all 18 fields are emitted as "null".
  Output: one "field\tvalue" line per field, joined by newlines.
─────────────────────────────────────────────────────────────────────────────-/

def renderComparisonFields (j : JsonValue) : String :=
  let nullRow (k : String) : String × String := (k, "null")
  let fields : List (String × String) :=
    match decodeSample j with
    | .error _ =>
      [ nullRow "protocol.name",
        nullRow "protocol.version",
        nullRow "tracker.slate",
        nullRow "tracker.serialNumber",
        nullRow "timing.timecode",
        nullRow "timing.sampleTimestamp.seconds",
        nullRow "timing.sampleTimestamp.nanoseconds",
        nullRow "timing.sampleRate",
        nullRow "camera.activeSensorResolution.width",
        nullRow "camera.activeSensorResolution.height",
        nullRow "transforms.Camera.translation.x",
        nullRow "transforms.Camera.translation.y",
        nullRow "transforms.Camera.translation.z",
        nullRow "transforms.Camera.rotation.pan",
        nullRow "transforms.Camera.rotation.tilt",
        nullRow "transforms.Camera.rotation.roll",
        nullRow "lens.focusDistance",
        nullRow "lens.pinholeFocalLength" ]
    | .ok s =>
      let proto  := s.protocol
      let trk    := s.tracker
      let sTrk   := s.«static».bind (·.tracker)
      let tim    := s.timing
      let tsList := s.transforms.map (·.values) |>.getD []
      let camTf  := findCamera tsList
      let lens   := s.lens
      let sCam   := s.«static».bind (·.camera)
      let sts    := tim.bind (·.sampleTimestamp)
      [ ("protocol.name",
          opt (proto.map (·.name))),
        ("protocol.version",
          opt (proto.map (fun p => renderVersion p.version))),
        ("tracker.slate",
          opt (trk.bind (·.slate) |>.map (·.val))),
        ("tracker.serialNumber",
          opt (sTrk.bind (·.serialNumber) |>.map (·.val))),
        ("timing.timecode",
          opt (tim.bind (·.timecode) |>.map renderTimecode)),
        ("timing.sampleTimestamp.seconds",
          opt (sts.map (·.seconds))),
        ("timing.sampleTimestamp.nanoseconds",
          opt (sts.map (·.nanoseconds))),
        ("timing.sampleRate",
          opt (tim.bind (·.sampleRate) |>.map renderRational)),
        ("camera.activeSensorResolution.width",
          opt (sCam.bind (·.activeSensorResolution) |>.map (fun r => toString r.width))),
        ("camera.activeSensorResolution.height",
          opt (sCam.bind (·.activeSensorResolution) |>.map (fun r => toString r.height))),
        ("transforms.Camera.translation.x",
          opt (camTf.map (·.translation.x))),
        ("transforms.Camera.translation.y",
          opt (camTf.map (·.translation.y))),
        ("transforms.Camera.translation.z",
          opt (camTf.map (·.translation.z))),
        ("transforms.Camera.rotation.pan",
          opt (camTf.map (·.rotation.pan))),
        ("transforms.Camera.rotation.tilt",
          opt (camTf.map (·.rotation.tilt))),
        ("transforms.Camera.rotation.roll",
          opt (camTf.map (·.rotation.roll))),
        ("lens.focusDistance",
          opt (lens.bind (·.focusDistance))),
        ("lens.pinholeFocalLength",
          opt (lens.bind (·.pinholeFocalLength))) ]
  String.intercalate "\n" (fields.map (fun (k, v) => k ++ "\t" ++ v))
