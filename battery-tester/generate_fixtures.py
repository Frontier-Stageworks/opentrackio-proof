#!/usr/bin/env python3
"""
generate_fixtures.py
Generates a parametric corpus of OpenTrackIO v1.0.1 JSON fixtures for battery-tester.
Writes to fixtures/generated/. One-variable-at-a-time design: each fixture varies one
comparison field across boundary and mid-range values while holding all others at base.
"""

import json
import sys
import uuid
from fractions import Fraction
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_CAMDKIT_SRC = _HERE.parents[1] / "ris-osvp-metadata-camdkit/src/main/python"
sys.path.insert(0, str(_CAMDKIT_SRC))

from camdkit.model import Clip, OPENTRACKIO_PROTOCOL_NAME, OPENTRACKIO_PROTOCOL_VERSION
from camdkit.examples import _unwrap_clip_to_pseudo_frame
from camdkit.transform_types import Vector3, Rotator3, Transform
from camdkit.timing_types import Timecode, Timestamp, TimingMode
from camdkit.numeric_types import StrictlyPositiveRational
from camdkit.camera_types import SenselDimensions as Dimensions
from camdkit.versioning_types import VersionedProtocol

OUTPUT_DIR = _HERE / "fixtures" / "generated"

# Base values — held constant in every fixture unless the variant overrides that field
BASE = dict(
    tx=1.0, ty=2.0, tz=3.0,
    pan=180.0, tilt=90.0, roll=45.0,
    focus=10.0, focal=24.305,
    rate=(24, 1),
    tc=(1, 2, 3, 4),
    ts=(1718806554, 500000000),
    res=(3840, 2160),
    slate="A101_A_4",
    serial="1234567890A",
    with_timestamp=True,
    with_resolution=True,
    with_serial=True,
    with_focal=True,
)

# Each entry: label (→ filename stem) + field overrides applied on top of BASE
VARIANTS = [
    # Translation X — 0, +, -, large+, large-
    *[{"label": f"tx_{i:02d}", "tx": v} for i, v in enumerate([0.0, 1.0, -1.0, 100.0, -100.0])],
    # Translation Y
    *[{"label": f"ty_{i:02d}", "ty": v} for i, v in enumerate([0.0, 2.0, -2.0, 50.0, -50.0])],
    # Translation Z
    *[{"label": f"tz_{i:02d}", "tz": v} for i, v in enumerate([0.0, 3.0, -3.0, 20.0, -20.0])],
    # Rotation pan — 0, ±90, near-boundary
    *[{"label": f"pan_{i:02d}", "pan": v} for i, v in enumerate([0.0, 90.0, -90.0, 179.999, -179.999])],
    # Rotation tilt
    *[{"label": f"tilt_{i:02d}", "tilt": v} for i, v in enumerate([0.0, 45.0, -45.0, 89.0, -89.0])],
    # Rotation roll
    *[{"label": f"roll_{i:02d}", "roll": v} for i, v in enumerate([0.0, 45.0, -45.0, 179.0, -179.0])],
    # Focus distance — near (0.3m), mid, far
    *[{"label": f"focus_{i:02d}", "focus": v} for i, v in enumerate([0.3, 1.0, 5.0, 10.0, 100.0])],
    # Pinhole focal length — common prime focal lengths
    *[{"label": f"focal_{i:02d}", "focal": v} for i, v in enumerate([14.0, 24.305, 35.0, 50.0, 85.0, 135.0])],
    # Sample rate — common broadcast and cinema rates
    *[{"label": f"rate_{i:02d}", "rate": v} for i, v in enumerate([(24, 1), (25, 1), (30, 1), (60, 1), (24000, 1001)])],
    # Timecode hours — midnight, 1am, noon, end-of-day
    *[{"label": f"tc_h_{i:02d}", "tc": (h, 2, 3, 4)} for i, h in enumerate([0, 1, 12, 23])],
    # Timecode minutes — boundaries
    *[{"label": f"tc_m_{i:02d}", "tc": (1, m, 3, 4)} for i, m in enumerate([0, 1, 30, 59])],
    # Timecode seconds
    *[{"label": f"tc_s_{i:02d}", "tc": (1, 2, s, 4)} for i, s in enumerate([0, 1, 30, 59])],
    # Timecode frames — 0, 1, mid, near-max for 24fps
    *[{"label": f"tc_f_{i:02d}", "tc": (1, 2, 3, f)} for i, f in enumerate([0, 1, 12, 23])],
    # Sample timestamp seconds — epoch 0, mid, realistic
    *[{"label": f"ts_sec_{i:02d}", "ts": (s, 500000000)} for i, s in enumerate([0, 1000000, 1718806554])],
    # Sample timestamp nanoseconds — 0, half-second, near-max
    *[{"label": f"ts_ns_{i:02d}", "ts": (1718806554, ns)} for i, ns in enumerate([0, 500000000, 999999999])],
    # Sensor resolution — HD, 4K, DCI 4K, 8K
    *[{"label": f"res_{i:02d}", "res": v} for i, v in enumerate([(1920, 1080), (3840, 2160), (4096, 3072), (7680, 4320)])],
    # Optional fields absent — each omitted in isolation
    {"label": "no_timestamp",  "with_timestamp": False},
    {"label": "no_resolution", "with_resolution": False},
    {"label": "no_serial",     "with_serial": False},
    {"label": "no_focal",      "with_focal": False},
]


def build_clip(p: dict) -> dict:
    rate_num, rate_denom = p["rate"]
    tc_h, tc_m, tc_s, tc_f = p["tc"]
    ts_sec, ts_nano = p["ts"]
    res_w, res_h = p["res"]

    clip = Clip()
    clip.sample_id = (uuid.uuid4().urn,)
    clip.source_id = (uuid.uuid4().urn,)
    clip.source_number = (1,)
    clip.protocol = (VersionedProtocol(OPENTRACKIO_PROTOCOL_NAME, OPENTRACKIO_PROTOCOL_VERSION),)

    clip.tracker_status = ("Optical Good",)
    clip.tracker_recording = (False,)
    clip.tracker_slate = (p["slate"],)
    if p["with_serial"]:
        clip.tracker_serial_number = p["serial"]

    clip.timing_mode = (TimingMode.INTERNAL,)
    clip.timing_sample_rate = (Fraction(rate_num, rate_denom),)
    clip.timing_timecode = (Timecode(
        hours=tc_h, minutes=tc_m, seconds=tc_s, frames=tc_f,
        frame_rate=StrictlyPositiveRational(rate_num, rate_denom),
    ),)
    if p["with_timestamp"]:
        clip.timing_sample_timestamp = (Timestamp(ts_sec, ts_nano),)

    clip.transforms = ((Transform(
        translation=Vector3(x=p["tx"], y=p["ty"], z=p["tz"]),
        rotation=Rotator3(pan=p["pan"], tilt=p["tilt"], roll=p["roll"]),
        id="Camera",
    ),),)

    clip.lens_focus_distance = (p["focus"],)
    if p["with_focal"]:
        clip.lens_pinhole_focal_length = (p["focal"],)

    if p["with_resolution"]:
        clip.active_sensor_resolution = Dimensions(width=res_w, height=res_h)

    return _unwrap_clip_to_pseudo_frame(clip.to_json(0))


def main():
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    for f in OUTPUT_DIR.glob("*.json"):
        f.unlink()

    count = 0
    for variant in VARIANTS:
        label = variant["label"]
        overrides = {k: v for k, v in variant.items() if k != "label"}
        p = {**BASE, **overrides}
        data = build_clip(p)
        (OUTPUT_DIR / f"{label}.json").write_text(json.dumps(data, indent=2))
        count += 1

    print(f"Generated {count} fixtures → {OUTPUT_DIR}")


if __name__ == "__main__":
    main()
