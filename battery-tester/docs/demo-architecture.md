# Demo Architecture — battery-tester

## Runtime Blocks

| Block | File | Role |
|---|---|---|
| Runner | `battery-tester/run.py` | Orchestrates: for each fixture × each adapter, invokes subprocess, collects stdout JSON, diffs, reports |
| Python adapter | `battery-tester/adapters/python_adapter.py` | Imports `opentrackio_lib.py` from camdkit; normalizes output to comparison JSON schema |
| Mo-Sys C++ adapter | `opentrackio-cpp/tools/dump_sample/` | CLI in the rocketmark fork; calls `OpenTrackIOSample::initialise()` directly; emits normalized JSON |
| Fixtures | `battery-tester/fixtures/*.json` | v1.0.1 canonical samples generated from camdkit; never modified at runtime |

## State Boundaries

| State | Location | Mutable? | Persists? |
|---|---|---|---|
| Normalized field dict | In-memory per subprocess call | No | No |
| Comparison result | In-memory per fixture | No | No |
| Float tolerance | Constant in `run.py` (`FLOAT_TOLERANCE = 1e-9`) | No | No |
| Fixture paths | Constant list in `run.py` | No | No |

No persistent state. Everything is derived fresh from each invocation.

## Mutation Points

None. The runner is a pure read → transform → compare → report pipeline. Nothing is written back to disk.

**Authoritative state:** The fixture JSON files are the single source of truth. Each adapter reads them independently. The runner never modifies them.

## External Interfaces

| Interface | Direction | Protocol | Notes |
|---|---|---|---|
| Fixture `.json` files | In | File read | Referenced by path relative to `battery-tester/` |
| Mo-Sys dump_sample binary | Out/In | subprocess stdout | Always emits normalized JSON |

## Invariant-Sensitive Components

**Normalized output schema** — the flat JSON object each adapter emits. Field names and canonical units are the invariant. If either adapter drifts from the schema (different key name, different unit), comparisons become meaningless without detection.

Canonical units (frozen):
- Translation: meters
- Rotation: degrees
- Focus distance: raw from JSON
- Focal length: raw from JSON
- Sample rate: float (numerator / denominator)

**Float tolerance constant** — `FLOAT_TOLERANCE = 1e-9` in `run.py`. Changing this changes all numeric PASS/FAIL verdicts.

## Safe Modification Guide

| If you want to… | Touch | Risk |
|---|---|---|
| Add a fixture | `battery-tester/fixtures/` + `run.py` fixtures list | Low |
| Add a comparison field | Both adapters + `COMPARISON_FIELDS` in `run.py` | High — both must agree on key name and units |
| Change float tolerance | `run.py` constant | High — changes all numeric verdicts |
| Change C++ output format | `dump_sample/main.cpp` + `run.py` JSON parser | Medium |
