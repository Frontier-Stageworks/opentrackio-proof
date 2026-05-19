# Work Queue — OpenTrackIO Parser Verification

Task classification: **Large**  
Total slices: **17** (16 proof slices + 1 packaging slice)  
Current slice: **COMPLETE — all 17 slices done**

---

## Queue

| # | Slug | Layer | Size | Status | Blocker |
|---|---|---|---|---|---|
| 1 | `rational-value-wrappers` | 0 | Small | **COMPLETE** | — |
| 2 | `json-raw-model` | 0 | Small | **COMPLETE** | — |
| 3 | `decode-error-vocabulary` | 0 | Small | **COMPLETE** | — |
| 4A | `version-model` | 1 | Small | **COMPLETE** | — |
| 4B | `version-value-decoder` | 1 | Small | **COMPLETE** | — |
| 4C | `protocol-version-field-decoder` | 1 | Small | **COMPLETE** | — |
| 5 | `rational-decoder-soundness` | 1 | Medium | **COMPLETE** | — |
| 6 | `nonempty-array-decoder` | 1 | Small | **COMPLETE** | — |
| 7 | `timing-enum-decoders` | 1 | Small | **COMPLETE** | — |
| 8A | `transform-model` | 2 | Small | **COMPLETE** | — |
| 8B | `transform-decoder` | 2 | Medium | **COMPLETE** | — |
| 9 | `camera-model-decoder` | 2 | Med–Large | **COMPLETE** | — |
| 10 | `lens-model-decoder` | 2 | Med–Large | **COMPLETE** | — |
| 11 | `sample-model-shell` | 2 | Small–Med | **COMPLETE** | — |
| 11.5 | `integration-smoke` | 2 | Small | **COMPLETE** | — |
| 12A | `compose-decoder-soundness/decodeSampleShell` | 3 | Small | **COMPLETE** | — |
| 12B | `compose-decoder-soundness/composed-soundness` | 3 | Small | **COMPLETE** | — |
| 13 | `error-correctness-required-fields` | 4 | Small | **COMPLETE** | — |
| 14 | `encoder-version` | 5 | Small | **COMPLETE** | — |
| 14.1 | `leaf-object-decoders` | 5 | Small | **COMPLETE** | — |
| 14.2 | `globalstage-decoder` | 5 | Small | **COMPLETE** | — |
| 14.3 | `tracker-decoders` | 5 | Small | **COMPLETE** | — |
| 14.4 | `ptpinfo-decoder` | 5 | Small | **COMPLETE** | — |
| 14.5 | `timecode-decoder` | 5 | Small | **COMPLETE** | — |
| 14.6 | `synchronization-decoder` | 5 | Small | **COMPLETE** | — |
| 14.7 | `timing-decoder` | 5 | Small | **COMPLETE** | — |
| 14.8 | `sample-decoder-complete` | 5 | Small | **COMPLETE** | — |
| 15 | `encode-decode-roundtrip-by-component` | 5 | Med–Large | **IN PROGRESS** | 14.8 + all decoders |
| 15.1 | `leaf-encoders` | 5 | Small | **COMPLETE** | — |
| 15.2 | `transform-encoder` | 5 | Small | **COMPLETE** | — |
| 15.3 | `globalstage-encoder` | 5 | Small | **COMPLETE** | — |
| 15.4 | `tracker-encoder` | 5 | Small | **COMPLETE** | — |
| 15.5 | `ptpinfo-encoder` | 5 | Small | **COMPLETE** | — |
| 15.6A | `numeric-literal-roundtrip` | 5 | Small | **COMPLETE** | — |
| 15.6B | `timecode-encoder-roundtrip` | 5 | Small | **COMPLETE** | — |
| 15.7 | `synchronization-encoder` | 5 | Small | **COMPLETE** | — |
| 15.8 | `timing-encoder` | 5 | Small | **COMPLETE** | — |
| 15.9 | `camera-encoder` | 5 | Small–Med | **COMPLETE** | — |
| 15.10A | `lens-sub-object-encoders` | 5 | Small–Med | **COMPLETE** | — |
| 15.10B | `lens-staticlens-lens-encoders` | 5 | Med | **COMPLETE** | — |
| 15.11 | `sample-encoder` | 5 | Med | **COMPLETE** | — |
| 16A | `wellformed-predicate` | 6 | Small | **COMPLETE** | — |
| 16B | `normalization-theorems` | 6 | Med | **COMPLETE** | — |
| 17 | `executable-differential-harness-packaging` | 6 | Small | **COMPLETE** | — |

---

## Blocker key

| ID | Description | Ambiguity Register |
|---|---|---|
| A1 | JSON numeric representation for rational values | [A1](ambiguity-register.md#a1--json-numeric-representation-for-rational-values) |
| A2 | Duplicate object key semantics | [A2](ambiguity-register.md#a2--duplicate-object-key-semantics) |
| A3 | Unknown-field policy | [A3](ambiguity-register.md#a3--unknown-field-policy) |
| A4 | Optional and default field behavior | [A4](ambiguity-register.md#a4--optional-and-default-field-behavior) |
| A5 | Enum spelling | [A5](ambiguity-register.md#a5--enum-spelling-and-canonicalization) |
| A6 | Lens coefficient array lengths | [A6](ambiguity-register.md#a6--lens-coefficient-array-lengths) |
| A8 | Protocol field names and version policy | [A8](ambiguity-register.md#a8--protocol-field-names-and-version-policy) |
| A9 | Transform rotation (Euler, not quaternion) | [A9](ambiguity-register.md#a9--transform-rotation-representation) |
| A11 | Version arity: 2-tuple vs. 3-tuple | [A11](ambiguity-register.md#a11--version-arity-majorminor-vs-majorminorpatch) |
| A12 | Version JSON shape: array vs. object vs. string | [A12](ambiguity-register.md#a12--version-json-shape-array-vs-object-vs-string) |
| A13 | `ValidVersion` protocol constraints | [A13](ambiguity-register.md#a13--validversion-protocol-constraints) |

---

## Slice history

| # | Slug | Completed | Notes |
|---|---|---|---|
| 1 | `rational-value-wrappers` | 2026-05-17 | `noncomputable` needed for `toReal`; all 11 theorems green; lake build clean |
| 2 | `json-raw-model` | 2026-05-17 | A2 policy recorded; `lookup?` is raw utility only; 2 theorems green; lake build clean |
| 3 | `decode-error-vocabulary` | 2026-05-17 | `duplicateKey` added per A2 resolution; `deriving DecidableEq`; no proofs needed; lake build clean |
| 4A | `version-model` | 2026-05-17 | `Fin 10` for digit bound; `protocolVersion_valid` by omega; lake build clean |
| 4B | `version-value-decoder` | 2026-05-17 | `decodeVersionValue` + soundness; `_h` unused per type-invariant proof; lake build clean |
| 4C | `protocol-version-field-decoder` | 2026-05-17 | `ProtocolInfo` struct + `decodeProtocol`; `_h` unused per same type-invariant reasoning; lake build clean |
| 5 | `rational-decoder-soundness` | 2026-05-17 | `decodePositiveRational`; decision proofs `hn`/`hd` become struct fields; `_h` unused; lake build clean |
| 6 | `nonempty-array-decoder` | 2026-05-17 | `NonemptyArray α` + `decodeNonemptyArray`; `cons_ne_nil` is load-bearing construction; `_h` unused; lake build clean |
| 7 | `timing-enum-decoders` | 2026-05-17 | 4 enums + `toStr` + decoders + soundness; `cases m` before `split at h` to avoid orientation issue; lake build clean |
| 8A | `transform-model` | 2026-05-17 | `NonemptyString` + `Vec3` + `Rotation` + `Transform`; id invariant in type not predicate; no decoder; lake build clean |
| 8B | `transform-decoder` | 2026-05-17 | `decodeIdField` + `decodeTransform`; `if h : s ≠ ""` constructs `NonemptyString`; soundness is `fun ns _ => ns.nonempty`; lake build clean |
| 9 | `camera-model-decoder` | 2026-05-17 | 9A: 3 structs (SensorPhysicalDimensions, SensorResolution, Camera); 9B: `decodeOptionalString` helper + `decodeCamera`; soundness is `fun r _ => positive_rational_toReal_pos r`; lake build clean |
| 10 | `lens-model-decoder` | 2026-05-17 | 10A: 7 structs including FizOptions with `anyPresent` proof field; 10B: 4 private helpers + 5 sub-object decoders + `decodeStaticLens` + `decodeLens`; soundness is `fun fiz _ => fiz.anyPresent`; lake build clean |
| 11 | `sample-model-shell` | 2026-05-17 | 12 structs; `«static»` guillemet escaping; `Bool`/`Option Bool` for JSON booleans; all enum names corrected to Slice 7 names; lake build clean |
| 11.5 | `integration-smoke` | 2026-05-17 | 16-module import chain; 5 `#eval |>.isOk` lines all `true`; `smokeSample : Sample` shell; capsule corrected `decodeProtocol` input and `#eval` tactic; lake build clean |
| 12A | `compose-decoder-soundness/decodeSampleShell` | 2026-05-17 | `decodeRelatedId` + `decodeStaticInfo` private helpers; nested `do` extracted to avoid elaborator type inference failure; lambda return type extracted to private def; lake build clean |
| 12B | `compose-decoder-soundness/composed-soundness` | 2026-05-17 | 5 theorems; all `_h` unused; proofs are direct struct field reads; no bind tracing; lake build clean |
| 13 | `error-correctness-required-fields` | 2026-05-17 | 5 theorems; `simp [decoder, h]` closed all goals including simultaneous-match in T5; no fallback needed; lake build clean |
| 14 | `encoder-version` | 2026-05-17 | 3 encoders + 3 roundtrip theorems; `decide` → `native_decide` for R1 (toString not kernel-reducible); `simp; rfl` for R2 (monadic residual); lake build clean |
| 14.1 | `leaf-object-decoders` | 2026-05-18 | `decodeTimestamp`, `decodeLeaderPriorities`, `decodeSyncOffsets`; pure `let` for all-optional SyncOffsets; no theorems; lake build clean |
| 14.2 | `globalstage-decoder` | 2026-05-18 | `decodeGlobalStage`; 6 required number fields; `do` block; no theorems; lake build clean |
| 14.3 | `tracker-decoders` | 2026-05-18 | `decodeStaticTracker` + `decodeTracker`; private `decodeOptionalString` re-defined locally; `recording` pure `let` via `.bool`; no theorems; lake build clean |
| 14.4 | `ptpinfo-decoder` | 2026-05-18 | `decodePtpInfo`; 6 required fields + 2 optional; `leaderIdentity` uses `if h : s ≠ ""` for `NonemptyString`; enum decoders take full `JsonValue`; no theorems; lake build clean |
| 14.5 | `timecode-decoder` | 2026-05-18 | `decodeTimecode`; 5 required fields + 2 optional; `frameRate` via `decodePositiveRational`; `dropFrame` pure `let` via `.bool`; no theorems; lake build clean |
| 14.6 | `synchronization-decoder` | 2026-05-18 | `decodeSynchronization`; 2 required + 4 optional; `locked` required bool uses `.expectedString` for wrong-type (no `expectedBool` in vocabulary); `ptp` via `decodePtpInfo`; no theorems; lake build clean |
| 14.7 | `timing-decoder` | 2026-05-18 | `decodeTiming`; all 7 fields optional; `sequenceNumber` pure `let`; delegates to `decodeTimestamp`, `decodePositiveRational`, `decodeSynchronization`, `decodeTimecode`; no theorems; lake build clean |
| 14.8 | `sample-decoder-complete` | 2026-05-18 | `decodeSample` completed; `globalStage`/`timing`/`tracker` wired; `StaticInfo.tracker` wired; 5 existing theorems unchanged; all 11 `Sample` fields now active; lake build clean |
| 15.1 | `leaf-encoders` | 2026-05-18 | `encodeTimestamp`, `encodeLeaderPriorities`, `encodeSyncOffsets`; 3 roundtrip theorems; `obtain ⟨t,r,l⟩` needed for SyncOffsets proof (field-based `cases` doesn't substitute); lake build clean |
| 15.2 | `transform-encoder` | 2026-05-18 | `encodeVec3`, `encodeRotation`, `encodeTransform`; 3 roundtrip theorems; `simp; rfl` pattern established for `do`-block bind chains; `dif_pos hns` + `obtain` for `NonemptyString` guard; lake build clean |
| 15.3 | `globalstage-encoder` | 2026-05-18 | `encodeGlobalStage`; 1 roundtrip theorem; `simp; rfl` closed first attempt; no deviations; lake build clean |
| 15.4 | `tracker-encoder` | 2026-05-18 | `encodeStaticTracker` + `encodeTracker`; 2 roundtrip theorems; private `decodeOptionalString` required local re-expose via `decodeOptStr` + `rfl` equation; `simp [*, ...]` discharges dite via context; lake build clean |
| 15.5 | `ptpinfo-encoder` | 2026-05-18 | `encodePtpInfo`; 1 roundtrip theorem; `·` bullets required — `try t <;> t2` silently skips `t2` when `try` catches failure; `none`/`some` lts branches split explicitly; `decodePtpProfile`/`decodePtpLeaderSource` added to simp set; lake build clean |
| 15.6A | `numeric-literal-roundtrip` | 2026-05-18 | Bridge theorem `nat_repr_toNat?_some`; strong induction on `n` for `toDigitsCore_eq` (not fuel); `interval_cases n` for H6 base case; `rw [if_neg ...]` (not simp) keeps `'0'.toNat` unreduced before `rw [digitChar_toNat_inv]`; `isNat_step` removed — pattern mismatch after `List.foldl_cons` beta-reduces lambda; `isNat_foldl_stable` auxiliary proved instead; lake build clean |
| 15.6B | `timecode-encoder-roundtrip` | 2026-05-18 | `encodePositiveRational` + `encodeTimecode`; 2 roundtrip theorems; `r.num.repr` used directly (not `toString`) so `nat_repr_toNat?_some` matches without extra unfolding; residual `do`-bind goals closed by `<;> rfl` (definitional equality); lake build clean |
| 15.7 | `synchronization-encoder` | 2026-05-18 | `encodeSynchronization`; `encodeSyncOffsets` already in `LeafEncoders` (Slice 15.1) — capsule corrected at Stop 2; 64 goals from 4 SyncSource values × 4 optional field splits; nested roundtrip lemmas as simp rules avoid expanding nested encoders; `Except.map` needed for `.map some` reductions; `<;> rfl` closes `do`-bind residuals; lake build clean |
| 15.8 | `timing-encoder` | 2026-05-18 | `encodeTiming`; all 7 fields optional; two-branch `mode` split required (TimingMode literals must be concrete for `decodeTimingMode`); 192 total goals (64 + 128); `set_option maxHeartbeats 400000` (2× default); nested roundtrip lemmas as simp rules; `<;> rfl` closes do-bind residuals; lake build clean |
| 15.9 | `camera-encoder` | 2026-05-19 | `encodeSensorPhysicalDimensions` + `encodeSensorResolution` + `encodeCamera`; 3 roundtrip theorems; 2^12 = 4096 goals; `rcases ns with _ | ⟨v, h⟩` brings NonemptyString proof into context for `dif_pos`; `decodeOptionalString` public so no unfold-theorem needed; `set_option maxHeartbeats 40000000` (200× default); sub-object roundtrip lemmas as simp rules; lake build clean (826s) |
| 15.10A | `lens-sub-object-encoders` | 2026-05-19 | 6 encoders (FizOptions, DistortionOffset, ProjectionOffset, ExposureFalloff, NonemptyStringArray, Distortion) + 6 roundtrip theorems; `decodeDistortion_unfold` by `rfl` for private helper access; `list_mapM_ok` induction — cons residual closed by `rfl` (`Except.bind_ok` does not exist); `decodeNonemptyArray_roundtrip` final `rfl` covers monad laws + proof irrelevance; `encodeNonemptyStringArray_rt` must not co-occur with `encodeNonemptyStringArray` in simp set; no `maxHeartbeats` override needed; lake build clean (8.2s) |
| 15.10B | `lens-staticlens-lens-encoders` | 2026-05-19 | `encodeStaticLens` + `encodeLens`; 2 roundtrip theorems; 3 private local decoder copies + 2 `rfl`-unfold theorems (`decodeStaticLens_unfold`, `decodeLens_unfold`); `list_mapM_ok'` and `decodeNonemptyArray_roundtrip'` reproved locally (private in 15.10A); explicit types required for `list_mapM_ok'` (inference picks wrong `α`); `decodeCustom'` must be absent from `encodeLens_roundtrip` simp set (pre-expansion trap, same as 15.10A); `maxHeartbeats 10000000` for StaticLens (256 goals), `maxHeartbeats 40000000` for Lens (4096 goals); lake build clean (561s) |
| 15.11 | `sample-encoder` | 2026-05-19 | `encodeStaticInfo` (private) + `encodeSample`; 1 public roundtrip theorem; `decodeRelId'` + `decodeStaticInfo'` local copies + `decodeSample_unfold` by `rfl`; `encodeRelatedIds_rt` must use composed-mapM form `rs.mapM (decodeRelId' ∘ .string)` — Mathlib's `List.mapM_map` fuses map+mapM before simp lemma can match; `relatedSampleIds` and `transforms` inlined in encoder (no named helper); `maxHeartbeats 40000000` for 2048 goals; lake build clean (229s) |
| 16A | `wellformed-predicate` | 2026-05-19 | 29 predicates (NoDupKeys via `mutual`, allKeysIn, 26 WellFormed* helpers, WellFormedSampleJson); `private mutual` not valid Lean 4 — `private` goes on each `def` inside the block; allKeysIn receiver order: `(j : JsonValue) (allowed : List String)` for dot notation; NoDupKeys asserted once at root, covers all descendants; no allKeysIn on Sample itself (extension-tolerant per A3); lake build clean (6.4s) |
| 16B | `normalization-theorems` | 2026-05-19 | `sampleNormalize` function + 5 theorems; `normalize` clashes with Mathlib — renamed `sampleNormalize`; bare `simp` triggers `CommMonoidWithZero JsonValue` — all proofs use `simp only`; `sampleNormalize_idempotent` proved by `cases h : decodeSample j` with `rw`+`simp only` in each branch; `WellFormedSampleJson (encodeSample s)` excluded (private predicate access required); lake build clean (15s) |
| 17 | `executable-differential-harness-packaging` | 2026-05-19 | `HarnessMain.lean` + `scripts/opentrackio-harness.sh`; all 10 checks PASS via `lake env lean --run`; native `lake exe` deferred — Lean 4.29.0 bundled `ld64.lld` cannot locate `libSystem` on Darwin 25.3.0 / SDK 26.5; packaging/toolchain limitation, not a proof failure; lake build clean (3290 jobs) |

---

## Rules

1. Only one slice is **IN PROGRESS** at a time.
2. A slice may not open if its listed blockers are unresolved.
3. Mark a slice **COMPLETE** only after proof review passes and artifacts are updated.
4. If a slice expands beyond its contract, stop and create a sub-queue entry.
5. Slice 17 (packaging) does not open until Slice 12 is complete.
