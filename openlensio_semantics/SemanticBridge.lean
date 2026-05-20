/-
  SemanticBridge.lean — SLICE-OL-02 (extraction) + SLICE-OL-03 (soundness)

  Defines the semantic extraction function and the soundness theorem
  connecting it to ValidLensSemantics.

  Design:
    extractLensSemantics takes already-decoded ℝ values — not raw Strings.
    String-to-ℝ parsing lives in the executable oracle layer (Layer F), not
    in the formal proof layer. This keeps the formal bridge free of
    floating-point parsing concerns and lets SemanticBridge focus on
    semantic validation (F > 0, etc.).

  Proof capsule for semanticExtraction_sound:
    Intent: a successful extraction guarantees ValidLensSemantics.
    Statement is NOT vacuous: the error branch for non-positive F is
    reachable and tested (see note below).
    Hard step: none — follows directly from the if-guard in the definition.
    Load-bearing definitions: extractLensSemantics, ValidLensSemantics.
    Forbidden changes: do not weaken ValidLensSemantics to make the proof
    easier; do not add a sorry.

  AMB-OL-007 note: denominator nonzero is NOT a condition here. It is
  a per-point predicate introduced in SLICE-OL-05.
  AMB-OL-013 note: p1=0, p2=0 when tangential coefficients are absent
  is a caller responsibility, not enforced here.
-/

import LensSemantics

/-─────────────────────────────────────────────────────────────────────────────
  SemanticError

  Reasons the semantic extraction can fail.
  Mirrors the structure of DecodeError but for semantic (not parse) failures.
─────────────────────────────────────────────────────────────────────────────-/

inductive SemanticError where
  | nonPositiveFocalLength : SemanticError
  deriving Repr, DecidableEq

/-─────────────────────────────────────────────────────────────────────────────
  extractLensSemantics

  Validates a set of already-decoded ℝ values and produces a LensSemantics.
  Returns Except.error if the focal length is not positive.

  Parameters correspond directly to the OpenLensIO model (§1.3):
    focalLength  — F in mm
    k1..k6       — radial polynomial coefficients (alternating num/den, §4.1)
    p1, p2       — tangential coefficients (zero if absent, AMB-OL-013)
    dcx, dcy     — ΔC components in mm (§1.5)
    dpx, dpy     — ΔP components in mm (§1.5)
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def extractLensSemantics
    (focalLength : ℝ)
    (k1 k2 k3 k4 k5 k6 : ℝ)
    (p1 p2 : ℝ)
    (dcx dcy : ℝ)
    (dpx dpy : ℝ) :
    Except SemanticError LensSemantics :=
  if _ : 0 < focalLength then
    .ok {
      focalLength := focalLength,
      radial      := ⟨k1, k2, k3, k4, k5, k6⟩,
      tangential  := ⟨p1, p2⟩,
      distCentre  := ⟨dcx, dcy⟩,
      perspOffset := ⟨dpx, dpy⟩
    }
  else
    .error .nonPositiveFocalLength

/-─────────────────────────────────────────────────────────────────────────────
  semanticExtraction_sound

  A successful extraction yields a value satisfying ValidLensSemantics.

  Proof plan:
    Unfold extractLensSemantics and split on the decidable condition
    0 < focalLength.

    Positive branch: the result is .ok { focalLength := focalLength, ... }.
      After injecting the Except.ok equality and rewriting, the goal
      reduces to 0 < focalLength, which is the branch hypothesis hf.

    Negative branch: the result is .error, so the hypothesis
      h : Except.error _ = Except.ok s is a contradiction; simp closes it.

  Non-vacuity note: ValidLensSemantics l = (0 < l.focalLength).
    The error branch is reachable (focalLength = 0 or negative).
    The theorem does not hold for all inputs — only successful ones.
─────────────────────────────────────────────────────────────────────────────-/

theorem semanticExtraction_sound
    (focalLength : ℝ)
    (k1 k2 k3 k4 k5 k6 : ℝ)
    (p1 p2 : ℝ)
    (dcx dcy : ℝ)
    (dpx dpy : ℝ)
    (s : LensSemantics)
    (h : extractLensSemantics focalLength k1 k2 k3 k4 k5 k6 p1 p2 dcx dcy dpx dpy = .ok s) :
    ValidLensSemantics s := by
  unfold extractLensSemantics at h
  split_ifs at h with hf
  · -- Positive branch: h : Except.ok { focalLength := focalLength, ... } = Except.ok s
    -- simp injects: h becomes {focalLength := focalLength, ...} = s
    -- subst then substitutes s with the record literal throughout (including in the goal)
    -- leaving ValidLensSemantics {focalLength := focalLength, ...} = 0 < focalLength = hf
    simp only [Except.ok.injEq] at h
    subst h
    exact hf
