#!/usr/bin/env python3
"""
adapters/python_adapter.py
Wraps opentrackio_lib.py from camdkit and emits a normalized JSON object to stdout.
All values are raw from the JSON fixture (default unit multipliers are 1.0).
"""

import json
import sys
from pathlib import Path

_PARSER_DIR = Path(__file__).resolve().parents[3] / "ris-osvp-metadata-camdkit/src/test/python/parser"
sys.path.insert(0, str(_PARSER_DIR))

from opentrackio_lib import OpenTrackIOProtocol, Translation, Rotation  # noqa: E402


def main():
    if len(sys.argv) < 2:
        print("Usage: python_adapter.py <fixture.json>", file=sys.stderr)
        sys.exit(1)

    fixture_path = Path(sys.argv[1])
    if not fixture_path.exists():
        print(f"Fixture not found: {fixture_path}", file=sys.stderr)
        sys.exit(1)

    proto = OpenTrackIOProtocol()
    proto.parse_json(fixture_path.read_text())

    out = {}

    # Protocol
    out["protocol.name"] = proto.get_protocol_name()
    out["protocol.version"] = proto.get_protocol_version()

    # Tracker
    out["tracker.slate"] = proto.get_slate()
    out["tracker.serialNumber"] = proto.get_tracking_device_serial_number()

    # Timing
    out["timing.timecode"] = proto.get_timecode()

    if proto.validate_dict_elements(proto.pd, ["timing", "sampleTimestamp", "seconds"]):
        out["timing.sampleTimestamp.seconds"] = int(
            proto.pd["timing"]["sampleTimestamp"]["seconds"]
        )
        out["timing.sampleTimestamp.nanoseconds"] = int(
            proto.pd["timing"]["sampleTimestamp"]["nanoseconds"]
        )
    else:
        out["timing.sampleTimestamp.seconds"] = None
        out["timing.sampleTimestamp.nanoseconds"] = None

    out["timing.sampleRate"] = proto.get_timecode_framerate()

    # Camera sensor resolution (reads from static.camera.*)
    out["camera.activeSensorResolution.width"] = proto.get_sensor_dimension_width()
    out["camera.activeSensorResolution.height"] = proto.get_sensor_dimension_height()

    # Transforms — default cameraname="Camera"
    out["transforms.Camera.translation.x"] = proto.get_camera_translation(Translation.X)
    out["transforms.Camera.translation.y"] = proto.get_camera_translation(Translation.Y)
    out["transforms.Camera.translation.z"] = proto.get_camera_translation(Translation.Z)
    out["transforms.Camera.rotation.pan"] = proto.get_camera_rotation(Rotation.PAN)
    out["transforms.Camera.rotation.tilt"] = proto.get_camera_rotation(Rotation.TILT)
    out["transforms.Camera.rotation.roll"] = proto.get_camera_rotation(Rotation.ROLL)

    # Lens — get_focal_length() reads lens.focalLength (wrong key; should be pinholeFocalLength)
    # This is existing behavior in opentrackio_lib.py and will surface as DIVERGE in the harness.
    out["lens.focusDistance"] = proto.get_focus_distance()
    out["lens.pinholeFocalLength"] = proto.get_focal_length()

    print(json.dumps(out))


if __name__ == "__main__":
    main()
