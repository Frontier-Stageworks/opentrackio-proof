# Slice 16B — Proof Capsule
# normalization-theorems

**Status:** Capsule (Stop 1)
**Date:** 2026-05-19

---

## Goal

Prove normalization theorems using `encodeSample_roundtrip` (Slice 15.11) and
`WellFormedSampleJson` (Slice 16A). The deliverable is a `normalize` function and its
idempotency theorem, plus the framing theorems that connect normalization to the
`WellFormedSampleJson` predicate.

---

## Architecture constraint

`WellFormedSampleJson.lean` (16A) exports only `WellFormedSampleJson`. All per-type
predicates (`WellFormedGlobalStage`, etc.) and `JsonValue.NoDupKeys` are `private`, so
they cannot be named or unfolded from an external file.

Consequence: the theorem `WellFormedSampleJson (encodeSample s)` — encoding always
produces schema-clean JSON — is not provable from a separate file without modifying 16A.
It is excluded from 16B scope. The achievable theorems use `WellFormedSampleJson` only as
an opaque hypothesis, and use `encodeSample_roundtrip` as the primary engine.

---

## Output

| Item | Value |
|---|---|
| File | `opentrackio_parser/NormalizationTheorems.lean` |
| Lake lib | `NormalizationTheorems` |
| Imports | `WellFormedSampleJson`, `SampleEncoder` |
| Public surface | `normalize`, `normalize_idempotent`, `encodedSample_stable`, `wellFormed_normalize_eq_encode`, `normalization_under_wellFormed` |

---

## Definitions

### `normalize`

The canonical normalization function: decode then re-encode; identity on decode failure.

```lean
def normalize (j : JsonValue) : JsonValue :=
  match decodeSample j with
  | .ok s    => encodeSample s
  | .error _ => j
```

---

## Theorems

### `normalize_idempotent` (main theorem)

Re-normalizing an already-normalized value is a no-op.

```lean
theorem normalize_idempotent (j : JsonValue) : normalize (normalize j) = normalize j
```

**Proof sketch:**
```
unfold normalize
rcases h : decodeSample j with | ok s | error e
· -- decodeSample j = .ok s  ⟹  normalize j = encodeSample s
  -- need: normalize (encodeSample s) = encodeSample s
  -- decodeSample (encodeSample s) = .ok s  by encodeSample_roundtrip
  simp [h, encodeSample_roundtrip s]
· -- decodeSample j = .error e  ⟹  normalize j = j
  -- need: normalize j = j  (unfolds to: match .error e with ... = j)
  simp [h]
```

### `encodedSample_stable` (Option C)

For any `s : Sample`, there exists `s'` such that decoding the encoded `s` gives `s'` and
re-encoding `s'` gives the same JSON as encoding `s`. Trivial from roundtrip.

```lean
theorem encodedSample_stable (s : Sample) :
    ∃ s', decodeSample (encodeSample s) = .ok s' ∧ encodeSample s' = encodeSample s :=
  ⟨s, encodeSample_roundtrip s, rfl⟩
```

### `normalize_encodeSample`

Encoding a sample and then normalizing gives the same encoding back. Corollary of
roundtrip.

```lean
theorem normalize_encodeSample (s : Sample) : normalize (encodeSample s) = encodeSample s
```

Proof: `simp [normalize, encodeSample_roundtrip]`.

### `wellFormed_normalize_eq_encode`

For schema-clean JSON that decodes successfully, `normalize` produces the encoded form.

```lean
theorem wellFormed_normalize_eq_encode (j : JsonValue) (s : Sample)
    (_ : WellFormedSampleJson j) (hd : decodeSample j = .ok s) :
    normalize j = encodeSample s
```

Proof: `simp [normalize, hd]`.

### `normalization_under_wellFormed` (Option A)

For schema-clean JSON that decodes to `s`, the normalization decodes back to `s`.

```lean
theorem normalization_under_wellFormed (j : JsonValue) (s : Sample)
    (_ : WellFormedSampleJson j) (hd : decodeSample j = .ok s) :
    decodeSample (normalize j) = .ok s
```

Proof: `simp [normalize, hd, encodeSample_roundtrip]`.

---

## What is NOT proved

**`encodeSample_wellFormed : ∀ s, WellFormedSampleJson (encodeSample s)`** — proving that
encoded samples are schema-clean requires unfolding `WellFormedGlobalStage`,
`WellFormedLens`, `JsonValue.NoDupKeys`, etc., all of which are private to 16A. This
theorem would require either (a) making per-type predicates public in 16A, or (b) adding it
directly to `WellFormedSampleJson.lean`. Excluded from 16B to respect the completed-slice
rule. The `normalize_idempotent` theorem achieves the essential normalization claim without
it.

---

## Stop 2 checklist (preview)

- [ ] `normalize` defined
- [ ] All 5 theorems proved
- [ ] No `sorry`, `admit`, `axiom`, `unsafe`, `partial`
- [ ] `lake build NormalizationTheorems` exits 0, no warnings
