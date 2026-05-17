# Proof Plan — OpenTrackIO Parser Verification

## Overview

Large task, 16 + 1 slices. Strategy is strictly bottom-up: no higher-level
decoder may be written until all types it depends on have local soundness
proofs. Composition is the only allowed proof technique at the top level.

---

## Layer map

```
Layer 0 — Primitive types and vocabulary
  Slice 1: rational-value-wrappers        ← CURRENT SLICE
  Slice 2: json-raw-model
  Slice 3: decode-error-vocabulary

Layer 1 — Atomic decoders
  Slice 4: version-decoder-soundness
  Slice 5: rational-decoder-soundness     ← blocked on A1 (numeric repr)
  Slice 6: fixed-length-array-decoder     ← blocked on A6 (array lengths)
  Slice 7: enum-field-decoder             ← blocked on A5 (enum spelling)

Layer 2 — Composite record decoders
  Slice 8: transform-model-decoder        ← blocked on A9 (quaternion norm)
  Slice 9: camera-model-decoder           ← blocked on A4 (optional fields)
  Slice 10: lens-model-decoder            ← blocked on A4, A6
  Slice 11: sample-model-shell            (no decoder yet — model + decomp lemmas)

Layer 3 — Top-level composition
  Slice 12: compose-decoder-soundness     ← blocked on Slices 4–11

Layer 4 — Error correctness
  Slice 13: error-correctness-required-fields

Layer 5 — Encoder and roundtrip
  Slice 14: encoder-version
  Slice 15: encode-decode-roundtrip-by-component

Layer 6 — Normalization and packaging
  Slice 16: decode-encode-normalization   (large; needs work queue)
  Slice 17: executable-differential-harness-packaging  (future)
```

---

## Per-slice proof strategy

### Slice 1 — rational-value-wrappers

Strategy: define three `structure`s with invariant fields (`den_pos`, `num_pos`),
required `toReal` evaluation functions (not optional), then prove ℕ-level
denominator nonzero lemmas via `omega` and ℝ-level nonzero/positivity lemmas via
`exact_mod_cast` and `positivity`. No Mathlib search needed.

Expected tactic budget: `omega` for ℕ arithmetic, `exact_mod_cast` for casts,
`positivity` for `toReal_pos` and `toReal_nonneg`.

### Slice 2 — json-raw-model

Strategy: define `JsonValue` as an inductive. Define `lookup?` as a list scan.
Left-bias may be proposed as the implementation choice, but **A2 must be
formally resolved before protocol-facing lookup semantics are treated as
normative** — document the choice in the ambiguity register and record it as
decided, not silently assumed. Prove two lookup theorems by `simp` on the list
definition. No arithmetic.

### Slice 3 — decode-error-vocabulary

Strategy: define `DecodeError` as an inductive with string-carrying constructors.
No theorems required unless discriminator lemmas are useful later.

### Slice 4 — version-decoder-soundness

**Blocked on A8 for any protocol-facing JSON decoding** (normative field names
are not yet fixed). Two options:

- **Model-only sub-slice** (`version-model`): define `Version` and `ValidVersion`,
  prove decomposition lemmas, no JSON decoding. This can open immediately after
  Slice 3 without resolving A8.
- **Decoder sub-slice** (`version-decoder-soundness`): define `decodeVersion` and
  prove soundness. Opens only after A8 is resolved.

If A8 is not resolved before Slice 4 opens, split into these two sub-slices
and proceed with the model-only sub-slice first.

### Blocked composite slices — split policy

Any slice in Layers 1–2 that is blocked on an unresolved ambiguity may be
split into two sub-slices:

- **Model sub-slice** (`X-model`): defines types and `ValidX`, proves structural
  lemmas. No JSON, no field names, no decoder. Opens as soon as its type
  dependencies are complete.
- **Decoder sub-slice** (`X-decoder-soundness`): defines `decodeX` and proves
  soundness. Opens only after the ambiguity blocking the field names or
  representation is resolved.

When a split occurs, update the work queue to replace the original slice entry
with the two sub-slices and re-evaluate blockers for each.

---

### Slice 5 — rational-decoder-soundness

Strategy: blocked on A1. Once numeric repr is fixed, define one decoder per
rational type. Prove positivity/nonnegativity from constructor invariants.
Medium — numeric parsing can spiral if representation is complex.

### Slice 6 — fixed-length-array-decoder

Strategy: blocked on A6. Once lengths are known, define `decodeVec3` etc.
by length-checking a `List JsonValue`. Prove length invariant.

### Slice 7 — enum-field-decoder

Strategy: blocked on A5. Define enum inductives. Decoder is a match on exact
string literals. Proof by `decide` or `simp`.

### Slice 8 — transform-model-decoder

Strategy: blocked on A9. Define `Transform`, `ValidTransform`. Decoder
composes Vec3 and Quaternion decoders. Soundness by composition lemmas.

### Slice 9 — camera-model-decoder

Strategy: blocked on A4, A8. Define `Camera` with required/optional fields
mirroring spec. Soundness by composition.

### Slice 10 — lens-model-decoder

Strategy: blocked on A4, A6, A8. Define `Lens` with distortion coefficient
arrays. Soundness by composition.

### Slice 11 — sample-model-shell

Strategy: define `Sample` record and `ValidSample`. Prove decomposition
lemmas only (`valid_sample_camera`, etc.). No `decodeSample` yet.

### Slice 12 — compose-decoder-soundness

Strategy: define `decodeSample` using all sub-decoders. Prove T1 by applying
sub-decoder soundness theorems in sequence. Proof is almost a one-liner per
field if sub-decoder soundness is available.

### Slices 13–16

Standard patterns; see the parser plan for details.

---

## Global tactic budget

| Tactic | Allowed for |
|---|---|
| `omega` | ℕ/ℤ arithmetic, array length checks, ordinal comparisons |
| `norm_cast` | coercions between `Nat`, `Int`, `ℝ` |
| `exact_mod_cast` | casting a known fact to a coerced goal (preferred over `norm_cast` when goal is fully determined) |
| `positivity` | nonnegativity and positivity of division/product expressions |
| `simp` | unfolding definitions, list lemmas, basic propositional rewriting |
| `decide` | closed decidable propositions (enum membership, small finite checks) |
| `linarith` / `nlinarith` | real arithmetic; fallback when `positivity` does not close the goal |
| `ring` / `field_simp` | not expected in Slices 1–7 |

No custom tactics. No `native_decide` unless agreed per-slice.

---

## Composition discipline

- Each slice declares its imports explicitly.
- A higher-level slice may import a lower-level slice's file, but must not
  inline the lower slice's proofs.
- If a composition proof requires a lemma not yet proved, stop and add it to
  the lower slice rather than proving it ad hoc at the higher level.

---

## Proof review requirement

Each slice must pass proof review before the next slice opens. Review checks:
- kernel green (no `sorry`)
- no vacuous hypotheses
- theorem statement matches the slice contract
- no excluded scope was touched
- `lake env lean <new-file-path>` exits 0 with no errors or warnings
- `lake build` succeeds if the new file is wired into the package

Every implementation slice records the result of both checks in its slice
artifacts before marking itself complete.
