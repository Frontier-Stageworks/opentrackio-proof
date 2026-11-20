# System Assurance Map

Phase 1 artifact.

## System / segment(s) covered

- **System:** OpenTrackIO protocol interoperability — cross-implementation correctness of camera-tracking metadata exchange (SMPTE RIS OpenTrackIO + companion OpenLensIO lens model).
- **Segment(s) in scope:**
  - `opentrackio-proof` (Lean 4 formal verification layer — proofs, battery-tester differential harness)
  - `ris-osvp-metadata-camdkit` (Python reference implementation)
  - `opentrackio-cpp` (Mo-Sys C++ implementation)
- **LID artifacts consulted:**
  - `ris-osvp-metadata-camdkit/docs/arrows/` — 6 segments, all AUDITED 2026-05-16 @ sha `de5c56e9b2bbecff1b7a89ca6ad0c6ea2cd04ebd`: protocol-envelope, camera-identity, optical-characteristics, spatial-tracking, temporal-synchronization, format-bridge.
  - `opentrackio-proof/docs/proof-map.md`, `docs/opentrackio-proof-summary.md`, `docs/limitations.md`, `docs/specification-questions.md` — not LID artifacts in form, but serve as this repo's own current-state system-understanding record (proof inventory, scope limits, open spec questions).
- **LID artifacts NOT consulted / not available:**
  - `opentrackio-cpp` has no LID map (no `docs/arrows/`, no HLD/LLD/EARS). Genuinely missing, not merely out of scope — flagged below under Open questions rather than remapped here.

## Trust boundaries

| Boundary | What crosses it | Trust level of the far side | Notes |
|---|---|---|---|
| Wire JSON payload → parser | Raw JSON (or CBOR) bytes | Untrusted external input | Three independent decoders sit on the far side: camdkit, opentrackio-cpp, Lean `decodeSample` |
| OpenCV calibration → OpenTrackIO lens conversion | Calibration parameters (`fx, fy, cx, cy`, distortion coefficients) | Trusted producer, unverified upstream math | Conversion correctness is proved in Lean; whether a real producer applies the proved formulas is unverified |
| Converted lens coefficients → consumer undistortion | `lens.distortion[].model` + coefficients | Ambiguous — schema defaults to `"Brown-Conrady D-U"`, proofs establish U→D conjugacy only | SQ-CV-07; a consumer trusting the default direction may apply coefficients backwards |

## Semantic chokepoints

| Chokepoint | What routes through it | Why it's a chokepoint | Existing safeguards |
|---|---|---|---|
| `decodeSample` / `camdkit.from_json` / `dump_sample` | Every field of every sample | All downstream geometric/numeric reasoning depends on correct field extraction | Lean: proved decoder soundness + roundtrip. camdkit/cpp: unit tests only (26 / ~1 file) |
| Principal-point + distortion coefficient conversion (`PrincipalPointConversion.lean`, `DistortionConversion.lean`) | Every OpenCV→OpenTrackIO lens parameter translation | Single shared formula; an error here silently mis-registers every rendered frame | Proved necessary+sufficient in Lean; 40 mutation-test theorems rule out known wrong variants |
| Brown-Conrady undistortion `U` | Every rendered pixel for a distorted lens | Shared by projection-matrix and FOV forms; sign/direction errors are invisible to ordinary unit tests | Proved structurally consistent (`fov_undistort_eq`); direction (SQ-CV-07) and injectivity (SQ-OL-07) open |

## Externally visible outputs

| Output | Consumed by | Consequence if wrong | Currently checked by |
|---|---|---|---|
| 18 battery-tester comparison fields (protocol/tracker/timing/camera/transforms/lens) | Any OpenTrackIO consumer (LED volume, compositor) | Wrong/missing metadata reaches render pipeline | battery-tester 3-way differential (Python/C++/Lean) over 4 canonical + 76 generated fixtures |
| Rendered pixel position (end consequence of lens conversion) | Virtual-production compositing/LED-volume pipeline | Misregistered virtual elements, not a crash — expensive to diagnose | Not directly observed by any current evidence; only the math feeding it is proved |

## High-consequence failure paths

| Failure path | Trigger | Consequence | Blast radius | Currently mitigated by |
|---|---|---|---|---|
| Wrong JSON key read | Schema key renamed/misremembered in an implementation | Field silently null/missing, not an error | All consumers of that field | Differential harness already caught one instance (`lens.pinholeFocalLength` vs `lens.focalLength` in camdkit, confirmed by Lean oracle, fixed via upstream PR#210) |
| Wrong principal-point offset formula | Implementation reimplements SMPTE RIS formula incorrectly | Systematic pixel offset, every frame | Any renderer using OpenCV-derived calibration | Lean proves the one earlier-published buggy variant is inconsistent (`buggy_principal_point_conversion_inconsistent`) |
| SQ-CV-06 tangential scale ambiguity (F vs F²) | Lens with nonzero tangential distortion (`p1≠0 ∨ p2≠0`) converted per the paper's stated formula | Silent divergence between paper-faithful and physically-corrected implementations | Any implementation choosing the "wrong" of two currently-unreconciled conventions | Open question only — no reference-implementation confirmation exists (`opencv_cross_check/` is explicitly not independent confirmation) |
| SQ-CV-07 D-U/U-D direction ambiguity | Consumer applies converted coefficients in the schema's default (D→U) direction | Silent incorrect undistortion, no error raised | Any consumer trusting the undocumented default | Open question — not resolved by paper or proofs |

## Important state machines

- n/a — the protocol as formalized is stateless per-sample; no process/session state machine is defined in any of the three repos or in the specifications consulted. (Candidate territory for the user's stated TLA+ goal — see Open questions.)

## External assumptions

| Assumption | Depended on by | Currently enforced / merely assumed |
|---|---|---|
| OpenTrackIO JSON schema (ris-pub.smpte.org, v1.0.1) is normative and currently published as inspected | All three implementations, Lean model | Assumed; schema text was spot-checked against the live site and against camdkit's tracked `lens.json` (per SQ-CV-07 investigation), not continuously monitored |
| OpenCV pinhole/distortion calibration convention is as OpenCV documents it | Conversion proofs, all conversion-consuming code | Assumed, external to this project |
| nlohmann JSON (C++ dependency) parses per RFC 8259 | `opentrackio-cpp` | Assumed, third-party library, unverified by this project |

## Production / model boundaries

| Model | Covers | Production correspondence status |
|---|---|---|
| Lean parser model (`opentrackio_parser/`) | Parsed `JsonValue` AST → `Sample` | Byte-level JSON parsing explicitly out of scope (`docs/limitations.md`); correspondence to camdkit/opentrackio-cpp established only via battery-tester differential comparison of output fields, not a proved mapping |
| Lean exact-real semantic model (`openlensio_semantics/`) | Brown-Conrady undistortion in exact reals | `ExecutableSemanticOracle.lean` (Float layer) not formally connected — no proved error bound (SQ-OL-04) |
| camdkit / opentrackio-cpp | Full production parsers | Both are "production" relative to the Lean oracle; agreement is evidence of correspondence, not proof |

## Existing tests and verification mechanisms

| Mechanism | Covers | Type |
|---|---|---|
| ~20 completed LAPS proof slices (`opentrackio-proof/docs/laps/*`) | Parser decode/encode/roundtrip/normalization; OpenCV↔OpenLensIO conversion math; OpenLensIO semantic pipeline consistency | Formal proof |
| `battery-tester` 3-way differential harness | 18 fields × 4 canonical fixtures + 76 generated fixtures, Python vs C++ vs Lean | Differential testing |
| `battery-tester/tests/test_properties.py` | Harness's own comparison-verdict logic (PASS/DIVERGE/MISSING, aggregate counts) | Property-based test (Hypothesis) — tests the harness, not the protocol implementations |
| `battery-tester/opencv_cross_check/` | Scaffolding sanity check of this repo's own OpenCV formula transcription, one real calibration | Self-check only — explicitly not independent confirmation (both sides authored here) |
| camdkit `src/test/` | 26 `test_*.py` files | Example/unit tests (per this project's own `correctness-plan.md`, authored locally in the camdkit checkout — not an upstream camdkit/SMPTE planning artifact); no property/metamorphic/differential tests built yet |
| `opentrackio-cpp/tests/test.cpp` | 454 lines, scope not yet characterized in detail | Unit tests |

## Known fragile or historically buggy areas

| Area | History | Why it's still a risk |
|---|---|---|
| camdkit lens key naming | `lens.focalLength` vs normative `lens.pinholeFocalLength` — real bug, caught by battery-tester, independently confirmed by Lean oracle, fixed upstream via PR#210 | Demonstrates the exact class of bug differential testing is meant to catch; no regression guard currently runs in CI for either repo |
| SMPTE RIS paper principal-point formula | Earlier published version omitted the `−w_shader/2` centering term; caught by Lean formalization, now proved inconsistent | Historical, resolved — relevant only as a mutation-test anchor |
| Tangential conversion power of F (SQ-CV-06) | Open question about the paper's own derivation; a corrected alternative is mechanically proved to permit unconditional pixel agreement where the paper's version doesn't | Unresolved; could already be a live cross-implementation divergence for any lens with tangential distortion |
| D-U/U-D direction (SQ-CV-07) | Schema defaults to a direction opposite the one the pipeline theorems prove | Unresolved; silent failure mode, no current evidence either way |

## Higher-level assurance goals

| Goal | Decomposes into (property IDs, once registered) |
|---|---|
| Differential tests, Lean proofs, and TLA+ proofs establish that camdkit and opentrackio-cpp interoperate correctly on the OpenTrackIO protocol (user's stated goal for this effort) | TBD — Phase 2 |
| Close the gap between "parser decodes correctly" and "renderer receives semantically correct pixel output" (`docs/limitations.md § Cross-cutting`) | TBD — Phase 2 |

## Open questions surfaced during mapping

1. **opentrackio-cpp has no LID map.** It is small (~1050 LOC across `OpenTrackIOSample.{h,cpp}`, `OpenTrackIOProperties.{h,cpp}`, `tests/test.cpp`) and is already exercised only as a black box through `dump_sample`'s JSON-in/JSON-out behavior in the battery-tester. Proposed scoping: treat it as an external differential-test subject (its own internals un-mapped), the same way MAPS treats any reference implementation under differential test, rather than stopping to route it through LID. **Needs confirmation** before Phase 2 treats this as settled.
2. **TLA+ has no starting point.** Nothing in any of the three repos currently defines a state machine, session/ordering model, or temporal property — the existing Lean proofs are pure-math (conversion formulas) and structural (parser roundtrip), not state-machine or temporal. The user's stated goal names TLA+ proofs as a deliverable, but there is no existing design artifact describing what protocol-level state/ordering/concurrency behavior TLA+ should model (sample sequencing across a tracking session? PTP sync-state convergence? a producer/consumer handshake?). **Needs the user to name a concrete candidate** before this can become a registered property rather than an unscoped goal.
3. **SQ-CV-06 and SQ-CV-07 are live open specification questions**, already tracked in `opentrackio-proof`'s own docs, that sit directly on the interoperability goal this MAPS package exists to assess. Confirm whether Phase 2 should register these as properties with explicit residual gaps (spec ambiguity, pending maintainer erratum), or track them only as design questions outside the register until the ambiguity resolves.
