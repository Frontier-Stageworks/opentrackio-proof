# CAPS Capsule — battery-tester

## Demo Goal
A Python runner ingests 4 canonical OpenTrackIO JSON fixtures, pipes each through all three parser surfaces (Python, CamDKit C++, Mo-Sys C++), collects normalized JSON from each, and prints a field-by-field PASS/FAIL/DIVERGE table — proving equivalence where it holds and exposing divergences where it does not.

## Target User
Protocol engineers or contributors evaluating whether parser implementations agree on the same input.

## Core Demo Flows

1. Run `python run.py --fixture complete_static_example` → see per-field comparison table across all three parsers
2. Observe `lens.pinholeFocalLength` flagged DIVERGE — Python returns `null` (reads wrong key `focalLength`), both C++ surfaces return `24.305` — the first real bug caught by the harness
3. Run `python run.py` against all 4 fixtures → see aggregate summary: N fixtures × M fields, pass/diverge/missing counts

## Non-Goals

- CBOR or UDP input (JSON files only)
- Fields outside the agreed comparison set
- CI integration or machine-readable report file
- Web or GUI output
- Performance benchmarking

## Constraints

- CAP-CONSTRAINT-001: No authentication. No user concept.
- CAP-CONSTRAINT-002: No background jobs, queues, or scheduled tasks.
- CAP-CONSTRAINT-003: No external infrastructure (no Redis, no S3, no message brokers).
- CAP-CONSTRAINT-004: Fixtures are the 4 canonical JSON files shipped with camdkit. No live device, no generated data.
- CAP-CONSTRAINT-005: Single Python process. C++ adapters are subprocesses, not services.
- CAP-CONSTRAINT-006: Maximum 20 smoke specs total.
- CAP-CONSTRAINT-007: No multi-tenancy, permissions systems, or role logic.
- CAP-CONSTRAINT-008: JSON file input only — no CBOR, no UDP streams.
- CAP-CONSTRAINT-009: C++ adapters communicate via stdout JSON only — no IPC, no shared memory, no native Python bindings.
- CAP-CONSTRAINT-010: Float comparison uses a fixed tolerance of `1e-9` — not configurable.

## Data Reality
4 fixture files from `ris-osvp-metadata-camdkit/src/test/resources/classic/examples/`. They ship with camdkit — no generation step needed.

## Success Criteria

1. A user can see which fields agree and which diverge across all three parsers on a single fixture
2. A user can see the `lens.pinholeFocalLength` discrepancy surface as a named DIVERGE result
3. A user can see aggregate pass/diverge/missing counts across all 4 fixtures
