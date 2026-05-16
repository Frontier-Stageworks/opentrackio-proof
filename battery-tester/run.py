#!/usr/bin/env python3
"""
battery-tester/run.py
Differential test harness for OpenTrackIO parser implementations.
Runs all three adapters on each fixture, compares field-by-field, writes report.
"""

import argparse
import json
import subprocess
import sys
from datetime import date
from pathlib import Path
from typing import Optional

FLOAT_TOLERANCE = 1e-9

_HERE = Path(__file__).resolve().parent        # battery-tester/
_CAMDKIT = _HERE.parents[1] / "ris-osvp-metadata-camdkit"  # github/ris-osvp-metadata-camdkit
_CPP_FORK = _HERE.parents[1] / "opentrackio-cpp"           # github/opentrackio-cpp

FIXTURES_DIR = _HERE / "fixtures"
FIXTURES = [
    "complete_static_example.json",
    "complete_dynamic_example.json",
    "recommended_static_example.json",
    "recommended_dynamic_example.json",
]

# Each adapter: name, command list ("{fixture}" is replaced with the path)
ADAPTERS = [
    {
        "name": "python",
        "cmd": [sys.executable, str(_HERE / "adapters/python_adapter.py"), "{fixture}"],
    },
    {
        "name": "cpp-mosys",
        "cmd": [
            str(_CPP_FORK / "build/tools/dump_sample/dump_sample"),
            "{fixture}",
        ],
    },
]

COMPARISON_FIELDS = [
    "protocol.name",
    "protocol.version",
    "tracker.slate",
    "tracker.serialNumber",
    "timing.timecode",
    "timing.sampleTimestamp.seconds",
    "timing.sampleTimestamp.nanoseconds",
    "timing.sampleRate",
    "camera.activeSensorResolution.width",
    "camera.activeSensorResolution.height",
    "transforms.Camera.translation.x",
    "transforms.Camera.translation.y",
    "transforms.Camera.translation.z",
    "transforms.Camera.rotation.pan",
    "transforms.Camera.rotation.tilt",
    "transforms.Camera.rotation.roll",
    "lens.focusDistance",
    "lens.pinholeFocalLength",
]


def resolve_report_path() -> Path:
    today = date.today().isoformat()
    n = 1
    while True:
        p = Path(f"battery-tester-{today}-{n}.txt")
        if not p.exists():
            return p
        n += 1


def run_adapter(adapter: dict, fixture_path: Path) -> Optional[dict]:
    cmd = [c.replace("{fixture}", str(fixture_path)) for c in adapter["cmd"]]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
        if result.returncode != 0:
            return None
        return json.loads(result.stdout)
    except FileNotFoundError:
        return None
    except (subprocess.TimeoutExpired, json.JSONDecodeError):
        return None


def compare_values(a, b) -> bool:
    if a is None or b is None:
        return False
    if isinstance(a, float) and isinstance(b, float):
        return abs(a - b) <= FLOAT_TOLERANCE
    if isinstance(a, (int, float)) and isinstance(b, (int, float)):
        return abs(float(a) - float(b)) <= FLOAT_TOLERANCE
    return a == b


def compare_samples(samples: dict) -> list:
    comparisons = []
    adapter_names = list(samples.keys())
    for field in COMPARISON_FIELDS:
        values = {}
        for source, sample in samples.items():
            values[source] = sample.get(field) if sample is not None else None

        non_null = [v for v in values.values() if v is not None]
        if not non_null:
            verdict = "MISSING"
        elif len(non_null) < len(values):
            # At least one adapter returned null — diverge
            verdict = "DIVERGE"
        elif all(compare_values(non_null[0], v) for v in non_null[1:]):
            verdict = "PASS"
        else:
            verdict = "DIVERGE"

        comparisons.append({"field": field, "values": values, "verdict": verdict})
    return comparisons


def format_value(v) -> str:
    if v is None:
        return "null"
    if isinstance(v, float):
        return f"{v:.9g}"
    return str(v)


def write_fixture_table(f, fixture_name: str, comparisons: list, adapter_names: list):
    f.write(f"\n{'=' * 80}\n")
    f.write(f"FIXTURE: {fixture_name}\n")
    f.write(f"{'=' * 80}\n\n")

    col_field = 42
    col_val = 18
    col_verdict = 8

    header = f"{'FIELD':<{col_field}}"
    for name in adapter_names:
        header += f"  {name[:col_val]:<{col_val}}"
    header += f"  {'VERDICT'}"
    f.write(header + "\n")
    f.write("-" * len(header) + "\n")

    pass_count = diverge_count = missing_count = 0
    for c in comparisons:
        verdict = c["verdict"]
        if verdict == "PASS":
            pass_count += 1
        elif verdict == "DIVERGE":
            diverge_count += 1
        else:
            missing_count += 1

        row = f"{c['field']:<{col_field}}"
        for name in adapter_names:
            v = format_value(c["values"].get(name))
            row += f"  {v[:col_val]:<{col_val}}"
        row += f"  {verdict}"
        f.write(row + "\n")

    f.write(f"\n  pass={pass_count}  diverge={diverge_count}  missing={missing_count}\n")
    return pass_count, diverge_count, missing_count


def write_aggregate(f, totals: dict):
    f.write(f"\n{'=' * 80}\n")
    f.write("AGGREGATE\n")
    f.write(f"{'=' * 80}\n")
    f.write(f"  fixtures:             {totals['fixtures']}\n")
    f.write(f"  total fields tested:  {totals['total']}\n")
    f.write(f"  PASS:                 {totals['pass']}\n")
    f.write(f"  DIVERGE:              {totals['diverge']}\n")
    f.write(f"  MISSING:              {totals['missing']}\n")


def main():
    parser = argparse.ArgumentParser(description="OpenTrackIO differential test harness")
    parser.add_argument(
        "--fixture",
        help="Run a single fixture by name stem (e.g. complete_static_example)",
    )
    parser.add_argument(
        "--generated",
        action="store_true",
        help="Run against all fixtures in fixtures/generated/ (produced by generate_fixtures.py)",
    )
    args = parser.parse_args()

    if args.generated:
        fixture_paths = sorted((FIXTURES_DIR / "generated").glob("*.json"))
        if not fixture_paths:
            print("ERROR: fixtures/generated/ is empty. Run generate_fixtures.py first.", file=sys.stderr)
            sys.exit(1)
    elif args.fixture:
        stem = args.fixture
        if not stem.endswith(".json"):
            stem += ".json"
        fixture_paths = [FIXTURES_DIR / stem]
    else:
        fixture_paths = [FIXTURES_DIR / f for f in FIXTURES]

    adapter_names = [a["name"] for a in ADAPTERS]
    report_path = resolve_report_path()

    totals = {"fixtures": 0, "total": 0, "pass": 0, "diverge": 0, "missing": 0}

    print(f"Writing report to: {report_path}")

    with open(report_path, "w") as report:
        report.write("OpenTrackIO Battery Tester\n")
        report.write(f"Date:              {date.today().isoformat()}\n")
        report.write(f"Adapters:          {', '.join(adapter_names)}\n")
        report.write(f"Float tolerance:   {FLOAT_TOLERANCE}\n")
        report.write(
            "Units:             translation=meters  rotation=degrees  "
            "distances=raw-from-JSON\n"
        )

        for fixture_path in fixture_paths:
            if not fixture_path.exists():
                print(f"WARNING: fixture not found: {fixture_path}", file=sys.stderr)
                continue

            samples = {}
            for adapter in ADAPTERS:
                samples[adapter["name"]] = run_adapter(adapter, fixture_path)

            comparisons = compare_samples(samples)
            p, d, m = write_fixture_table(
                report, fixture_path.stem, comparisons, adapter_names
            )

            totals["fixtures"] += 1
            totals["total"] += len(comparisons)
            totals["pass"] += p
            totals["diverge"] += d
            totals["missing"] += m

        if totals["fixtures"] > 1:
            write_aggregate(report, totals)

    print(
        f"Done. {totals['pass']} pass, {totals['diverge']} diverge, "
        f"{totals['missing']} missing across {totals['fixtures']} fixture(s)."
    )
    print(f"Report: {report_path}")


if __name__ == "__main__":
    main()
