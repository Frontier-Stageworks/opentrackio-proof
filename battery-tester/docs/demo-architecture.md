# Demo Architecture — battery-tester

## Critical Structural Note

The CamDKit C++ parser (`ris-osvp-metadata-camdkit/src/test/cpp/opentrackio-parser/`) `#includes <opentrackio-cpp/OpenTrackIOSample.h>` and links against the Mo-Sys library. It is **not an independent parse path** — it is a different API surface layered on top of the same Mo-Sys parse engine. The harness therefore compares:

- One independent Python path (`opentrackio_lib.py`)
- Two API surfaces over one C++ parse engine (`OpenTrackIOSampleParser` wrapper vs. `OpenTrackIOSample` directly)

This is still meaningful: the Python path has real divergences from C++ (wrong key name for focal length, `static.*` wrapper access patterns, unit conversion logic). But the architecture must be honest about what is truly independent.

## Runtime Blocks

| Block | File | Role |
|---|---|---|
| Runner | `battery-tester/run.py` | Orchestrates: for each fixture × each adapter, invokes subprocess, collects stdout JSON, diffs, reports |
| Python adapter | `battery-tester/adapters/python_adapter.py` | Imports `opentrackio_lib.py` from camdkit; normalizes output to comparison JSON schema |
| CamDKit C++ adapter | `ris-osvp-metadata-camdkit/src/test/cpp/opentrackio-parser/src/main.cpp` (+ `--json` flag) | Adds JSON output mode to existing binary; wraps Mo-Sys `OpenTrackIOSample` via `OpenTrackIOSampleParser` |
| Mo-Sys C++ adapter | `opentrackio-cpp/tools/dump_sample/main.cpp` (new in rocketmark fork) | Calls `OpenTrackIOSample::initialise()` directly; emits normalized JSON |
| Fixtures | `ris-osvp-metadata-camdkit/src/test/resources/classic/examples/*.json` | Ground-truth inputs; 4 files; never modified |

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
| Fixture `.json` files | In | File read | Referenced by relative path |
| CamDKit C++ binary | Out/In | subprocess stdout | `--json` flag selects normalized JSON output mode |
| Mo-Sys dump_sample binary | Out/In | subprocess stdout | New binary; always emits normalized JSON |

## Invariant-Sensitive Components

**Normalized output schema** — the flat JSON object each adapter emits. Field names and canonical units are the invariant. If any adapter drifts from the schema (different key name, different unit), comparisons become meaningless without detection.

Canonical units (frozen):
- Translation: meters
- Rotation: degrees
- Focus distance: millimeters
- Focal length: millimeters
- Sample rate: float (numerator / denominator)

**Float tolerance constant** — `FLOAT_TOLERANCE = 1e-9` in `run.py`. Changing this changes all numeric PASS/FAIL verdicts.

## Safe Modification Guide

| If you want to… | Touch | Risk |
|---|---|---|
| Add a fixture | `run.py` fixtures list | Low |
| Add a comparison field | All 3 adapters + normalized schema definition | High — all must agree on key name and units |
| Change float tolerance | `run.py` constant | High — changes all numeric verdicts |
| Change C++ output format | C++ wrapper + `run.py` JSON parser | Medium |
| Add a 4th adapter | New adapter file + `run.py` adapter list | Low — runner is adapter-list-driven |
