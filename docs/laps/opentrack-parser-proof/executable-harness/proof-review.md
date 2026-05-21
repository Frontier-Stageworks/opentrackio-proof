# Proof Review — executable-differential-harness-packaging (Slice 17)

## Acceptance checks

| Check | Result |
|---|---|
| `HarnessMain.lean` elaborates | ✓ (`lake build` exit 0, 3290 jobs) |
| All 10 checks PASS via `lake env lean --run` | ✓ |
| `scripts/opentrackio-harness.sh` created | ✓ |
| No `sorry`, `admit`, `axiom`, `unsafe`, `partial` | ✓ |
| No Slice 1–16 files modified | ✓ |

## Harness run output

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

## Deviations from capsule

**`lake exe` → `lake env lean --run`:** Native `lake exe opentrackio-harness` was
attempted but fails at the link step. The Lean 4.29.0 bundled `ld64.lld` cannot
locate `libSystem` on this host (Darwin 25.3.0, Xcode SDK 26.5, ld 1267 built
2026-04-22). Lake sets `MACOSX_DEPLOYMENT_TARGET=99.0` internally; the updated
Apple linker on this pre-release macOS rejects this and cannot resolve `-lSystem`
from the Lean toolchain's sysroot. This is a packaging/toolchain limitation, not
a protocol proof failure. All theorems are kernel-verified; the harness logic is
type-checked and correct. `lake env lean --run` is the accepted delivery form
per the updated Slice 17 contract.

**No `[[lean_exe]]` in lakefile.toml:** Removed per updated contract; the
native-link path is deferred.

## Status: COMPLETE
