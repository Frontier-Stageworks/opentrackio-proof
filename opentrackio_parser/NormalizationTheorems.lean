/-
  NormalizationTheorems.lean — Slice 16B: normalization-theorems

  Defines the sampleNormalize function and proves its idempotency and connection to
  the WellFormedSampleJson predicate. The roundtrip theorem encodeSample_roundtrip
  (Slice 15.11) is the primary engine for all proofs.

  Note: `normalize` is already defined in Mathlib; this file uses `sampleNormalize`.

  Ref: docs/laps/encode-decode-roundtrip/16B-normalization-theorems/proof-capsule.md
-/

import Mathlib
import WellFormedSampleJson
import SampleEncoder

/-─────────────────────────────────────────────────────────────────────────────
  Normalization function

  Decode then re-encode; identity on decode failure.
─────────────────────────────────────────────────────────────────────────────-/

def sampleNormalize (j : JsonValue) : JsonValue :=
  match decodeSample j with
  | .ok s    => encodeSample s
  | .error _ => j

/-─────────────────────────────────────────────────────────────────────────────
  Theorems
─────────────────────────────────────────────────────────────────────────────-/

-- sampleNormalize is idempotent: applying it twice equals applying it once.
theorem sampleNormalize_idempotent (j : JsonValue) :
    sampleNormalize (sampleNormalize j) = sampleNormalize j := by
  cases h : decodeSample j with
  | ok s =>
    have heq : sampleNormalize j = encodeSample s := by simp only [sampleNormalize, h]
    rw [heq]
    simp only [sampleNormalize, encodeSample_roundtrip]
  | error e =>
    have heq : sampleNormalize j = j := by simp only [sampleNormalize, h]
    simp only [heq]

-- Stability (Option C): encoding a sample produces a canonical representative.
theorem encodedSample_stable (s : Sample) :
    ∃ s', decodeSample (encodeSample s) = .ok s' ∧ encodeSample s' = encodeSample s :=
  ⟨s, encodeSample_roundtrip s, rfl⟩

-- Normalizing an already-encoded sample is a no-op.
theorem sampleNormalize_encodeSample (s : Sample) :
    sampleNormalize (encodeSample s) = encodeSample s := by
  simp only [sampleNormalize, encodeSample_roundtrip]

-- Under WellFormedSampleJson, sampleNormalize produces the encoded form of the decoded sample.
theorem wellFormed_normalize_eq_encode (j : JsonValue) (s : Sample)
    (_ : WellFormedSampleJson j) (hd : decodeSample j = .ok s) :
    sampleNormalize j = encodeSample s := by
  simp only [sampleNormalize, hd]

-- Option A: for schema-clean JSON that decodes to s, normalization also decodes to s.
theorem normalization_under_wellFormed (j : JsonValue) (s : Sample)
    (_ : WellFormedSampleJson j) (hd : decodeSample j = .ok s) :
    decodeSample (sampleNormalize j) = .ok s := by
  simp only [sampleNormalize, hd, encodeSample_roundtrip]
