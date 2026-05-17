# Work Queue — OpenTrackIO Parser Verification

Task classification: **Large**  
Total slices: **17** (16 proof slices + 1 packaging slice)  
Current slice: **Slice 6 — fixed-length-array-decoder** (blocked on A6) / **Slice 7 — enum-field-decoder** (blocked on A5)

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
| 6 | `fixed-length-array-decoder` | 1 | Small–Med | Queued | Slice 2, 3; **A6** |
| 7 | `enum-field-decoder` | 1 | Small | Queued | Slice 2, 3; **A5** |
| 8 | `transform-model-decoder` | 2 | Medium | Queued | Slices 5, 6; **A9** |
| 9 | `camera-model-decoder` | 2 | Med–Large | Queued | Slices 5, 6, 7; **A4**, **A8** |
| 10 | `lens-model-decoder` | 2 | Med–Large | Queued | Slices 5, 6, 7; **A4**, **A6**, **A8** |
| 11 | `sample-model-shell` | 2 | Small–Med | Queued | Slices 9, 10 |
| 12 | `compose-decoder-soundness` | 3 | Medium | Queued | Slices 4–11 |
| 13 | `error-correctness-required-fields` | 4 | Small | Queued | Slice 12 |
| 14 | `encoder-version` | 5 | Small | Queued | Slice 4 |
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
| A6 | Exact array lengths | [A6](ambiguity-register.md#a6--exact-array-lengths-for-lens-coefficient-arrays) |
| A8 | Protocol field names and version policy | [A8](ambiguity-register.md#a8--protocol-field-names-and-version-policy) |
| A9 | Quaternion normalization | [A9](ambiguity-register.md#a9--quaternion-normalization-requirement) |
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

---

## Rules

1. Only one slice is **IN PROGRESS** at a time.
2. A slice may not open if its listed blockers are unresolved.
3. Mark a slice **COMPLETE** only after proof review passes and artifacts are updated.
4. If a slice expands beyond its contract, stop and create a sub-queue entry.
5. Slice 17 (packaging) does not open until Slice 12 is complete.
