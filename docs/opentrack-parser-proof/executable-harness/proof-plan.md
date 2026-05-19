# Slice 17 — Proof Plan
# executable-differential-harness-packaging

**Status:** Plan (Stop 2)
**Date:** 2026-05-19

---

## Implementation

### Files created

| File | Role |
|---|---|
| `opentrackio_parser/HarnessMain.lean` | Harness source; elaborates under `lake build` |
| `scripts/opentrackio-harness.sh` | Convenience runner wrapping `lake env lean --run` |

### Packaging decision

The harness is packaged as a **Lake-environment Lean runner**, not as a native
`lake exe` binary on this host.

Accepted run command:

```
lake env lean --run opentrackio_parser/HarnessMain.lean
```

Convenience wrapper:

```bash
#!/usr/bin/env bash
set -euo pipefail
lake env lean --run opentrackio_parser/HarnessMain.lean
```

### lakefile.toml

No `[[lean_exe]]` entry. The `[[lean_exe]]` target was removed because the
native-link step fails on this host (see deviation below), and the
`lake env lean --run` path is the accepted delivery form.

### Import chain

`HarnessMain` imports `NormalizationTheorems`, which transitively imports
all of Slices 1–16.

---

## Build results

| Step | Command | Result |
|---|---|---|
| Library build | `lake build` | Exit 0, 3290 jobs |
| Harness run | `lake env lean --run opentrackio_parser/HarnessMain.lean` | **All 10 PASS, exit 0** |

### Run output

```
PASS  protocol decoder
PASS  positive rational decoder
PASS  transform decoder
PASS  camera decoder
PASS  lens decoder
PASS  sample decoder
PASS  roundtrip: empty sample
PASS  roundtrip: sample with id
PASS  normalize: protocol-only json
PASS  normalize: encoded shell

all harness checks passed
```

---

## Deviation: native `lake exe` deferred

`lake exe opentrackio-harness` was attempted and fails at the link step.
The Lean 4.29.0 bundled `ld64.lld` cannot locate `libSystem` on this host
(Darwin 25.3.0, Xcode SDK 26.5, ld 1267). This is a packaging/toolchain
limitation, not a protocol proof failure. No Lean code is incorrect.
`lake env lean --run` is the accepted delivery form per the updated contract.

---

## No deviations from capsule in logic or structure

All 10 checks, all fixtures, all theorem imports, and the `def main : IO UInt32`
signature are exactly as specified in the capsule.

---

## Stop 3 checklist

- [x] `HarnessMain.lean` created, elaborates under `lake build`
- [x] `scripts/opentrackio-harness.sh` created
- [x] `lake build` exits 0, 3290 jobs
- [x] `lake env lean --run opentrackio_parser/HarnessMain.lean` prints all 10 PASS lines, exits 0
- [x] No Slice 1–16 files modified
- [x] No `[[lean_exe]]` target (deferred; native link fails on this host)
