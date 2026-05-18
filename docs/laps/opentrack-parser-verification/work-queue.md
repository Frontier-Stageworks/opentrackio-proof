# Work Queue — OpenTrackIO Parser Verification

Task classification: **Large**  
Total slices: **17** (16 proof slices + 1 packaging slice)  
Current slice: **Slice 9 — camera-model-decoder** (blocked on A4, A8)

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
| 15 | `encode-decode-roundtrip-by-component` | 5 | Med–Large | Queued | Slice 14 + all decoders |
| 16 | `decode-encode-normalization` | 6 | Large | Queued | Slices 14–15; **A2**, **A3** |
| 17 | `executable-differential-harness-packaging` | 6 | TBD | Future | Slice 12+ |

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

---

## Rules

1. Only one slice is **IN PROGRESS** at a time.
2. A slice may not open if its listed blockers are unresolved.
3. Mark a slice **COMPLETE** only after proof review passes and artifacts are updated.
4. If a slice expands beyond its contract, stop and create a sub-queue entry.
5. Slice 17 (packaging) does not open until Slice 12 is complete.
