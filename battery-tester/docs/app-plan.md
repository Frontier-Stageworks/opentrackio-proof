# CAPS App Plan — battery-tester

## App Shape
A Python CLI script (`run.py`) that invokes three adapter subprocesses per fixture, collects normalized JSON from each, compares field-by-field at a fixed float tolerance, and writes a human-readable report file. Python chosen because the Python adapter imports `opentrackio_lib.py` directly and Python is already present across both camdkit and opentrackio-proof.

## Screens / Routes
CLI only. Two output surfaces written to a dated sequential report file:
- Per-fixture field-comparison table (one per fixture)
- Aggregate summary (when running more than one fixture)

## State Model
In-memory during a single run. Nothing persists between runs.

- `fixtures: list[Path]` — fixture file paths (constant)
- `adapters: list[dict]` — name, binary path, command template (constant)
- `results: list[FixtureResult]` — accumulated as each fixture completes

## Data Model

**NormalizedSample** — one per adapter per fixture
- `source: str` — `"python"` | `"cpp-camdkit"` | `"cpp-mosys"`
- `fields: dict[str, float | int | str | None]` — field name → value (canonical units, raw from JSON)

**FieldComparison** — one per field per fixture
- `field: str`
- `values: dict[str, any]` — source → value
- `verdict: str` — `"PASS"` | `"DIVERGE"` | `"MISSING"`

**FixtureResult**
- `fixture: str`
- `comparisons: list[FieldComparison]`
- `pass_count / diverge_count / missing_count: int`

## Stubbed Integrations

None. All three adapters are real implementations. C++ adapters must be locally built before the demo (see README.md for build steps).

## Implementation Slices

1. Python adapter + runner scaffold + file writer → shows Python fields, `N/A` for unbuilt C++ adapters; report file is created from first run
2. Comparison engine → PASS/DIVERGE/MISSING logic works with 1–3 adapters present; table structure visible
3. CamDKit C++ adapter: add `--json` flag to `main.cpp`, using `OpenTrackIOSample` directly in JSON mode
4. Mo-Sys C++ adapter: `tools/dump_sample/main.cpp` in rocketmark fork, `OPENTRACKIO_BUILD_TOOLS` CMake option
5. Aggregate summary row + all-fixtures run

## Known Cuts

- No CBOR input
- No configurable field list at runtime (comparison fields are hardcoded)
- No graceful C++ build failure recovery (adapter shows MISSING per CAPS-REPORT-003)
- No pairwise-only comparison (always 3-way)
- No colour output
