# LAPS Handoff

## Source

- **Property ID:** PROP-003 (Full OpenCV/OpenLensIO pixel-level pipeline equivalence)
- **Evidence ID:** EVID-006 (planned)
- **Evidence-matrix row:** `evidence-matrix.md § PROP-002 / PROP-003 § Evidence records § EVID-006`
- **MAPS session / date:** this session, 2026-10-10

## Exact intended claim

For the y-axis analog of the existing x-pixel theorems: given all of PROP-002's coefficient conversions and `h_shader/h = fy`, the OpenCV and OpenTrackIO full-pipeline **y**-pixel outputs agree for all normalised inputs (sufficiency); and, given `p1 ≠ 0 ∨ p2 ≠ 0`, y-pixel agreement holds **iff** `h_shader/h = fy`. This is the mechanical y-axis mirror of `opencv_openlensio_full_pipeline_pixel_sufficiency` and `opencv_openlensio_full_pipeline_pixel_iff` in `Pipeline/PixelSufficiency.lean` / `Pipeline/PixelIff.lean`, with the tangential roles swapped: the x-theorem's tangential term `2*p1*x'*y' + p2*(r²+2x'²)` becomes `p1*(r²+2y'²) + 2*p2*x'*y'` for y, and `F=(w/w_shader)*fx` becomes `F=(h/h_shader)*fy`.

## Why it matters

The project's own `docs/limitations.md` currently states the y-result "follows by a symmetric argument... argued informally... but not formally proved," and recommends "any reader can verify the y-result by inspection of the x-proof" rather than treating it as established. This MAPS pass explicitly declined to treat that informal argument as a structural discharge (per the discipline in `property-register.md § PROP-003`) — it is recorded as a residual gap, not as covered. Consequence if false: a y-axis-specific implementation error (e.g. a sign or coefficient-role error only visible on the vertical axis) would currently be invisible to every proof or test in this project.

## Relevant LID behavioral segment

None — opentrackio-proof has no LID map of its own (it is the verification layer, not a LID-governed implementation project). Treat `docs/proof-map.md` and `docs/limitations.md` as the orientation documents instead.

## Relevant source files

- `opencv_opentrackio_proofs/Pipeline/PixelSufficiency.lean` (x-theorem to mirror)
- `opencv_opentrackio_proofs/Pipeline/PixelIff.lean` (x-theorem to mirror)
- `opencv_opentrackio_proofs/DistortionConversion.lean` (the shared coefficient-conversion hypotheses both axes depend on)

## Preconditions

- All of PROP-002's coefficient conversions hold (`l1=k1/F²`, …, `q1=p1/F²`, `q2=p2/F²` — using the paper's as-published tangential scaling, same as the x-theorem; this handoff does NOT ask LAPS to adjudicate SQ-CV-06, see Open questions below).
- Nonzero image dimensions (`h ≠ 0`, `h_shader ≠ 0`).
- For the iff direction: `p1 ≠ 0 ∨ p2 ≠ 0`.

## Assumptions

- This handoff inherits PROP-003's existing assumption that the paper's tangential conversion formula is the one being formalized (not the corrected alternative in `DistortionConversionCorrected.lean`) — mirror the as-published x-theorem, not the corrected investigation.
- `denominatorNonzero` remains a free hypothesis, exactly as in the x-theorem — this handoff does not ask LAPS to derive it from coefficient bounds (that is a separate, deferred residual gap, not in scope here).

## Likely specification boundary

Small and well-bounded: this is a mechanical relabeling of an already-proved theorem (swap `p1↔p2` roles in the tangential term, swap `x'↔y'`, swap `w/w_shader/fx` for `h/h_shader/fy`), not new mathematical content. MAPS's assessment is that the specification boundary is exactly the existing x-theorem's boundary, mirrored.

## What should be modeled vs. remain abstract

Same abstraction level as the existing x-theorem — exact reals (`ℝ`), same structure. No new modeling decisions expected.

## Target stage

- [x] Specification / toy model (Stage 1) — this is pure algebra mirroring an existing proved result, not a production-correspondence claim
- [ ] Simplified realistic model (Stage 2)
- [ ] Production port (Stage 3 — requires LAPS port-audit.md)
- [ ] Production-correspondence theorem (differential/refinement claim between a proved model and production)

## What evidence is still required outside the proof

Nothing additional for PROP-003's own scope once this closes — the x+y pair together would still not constitute the joint-2D theorem (that remains a separately deferred gap, not requested here) and would still not resolve SQ-CV-06/SQ-CV-07 (those stay open regardless of this proof's outcome).

## Vacuity / discrimination requirement

**Required check:** mirror the x-theorem's own discrimination result — LAPS should produce y-axis analogs of a representative subset of the 40 `MutationTests.lean` theorems (at minimum: wrong F-power for the y-side tangential coefficients, and a `p1↔p2` coefficient swap) demonstrating that plausible wrong y-axis variants are also provably degenerate or inconsistent, not merely that the one correct statement type-checks.

## Open questions for LAPS

- Confirm whether Lean's existing proof script for `PixelIff.lean` is in fact mechanically mirror-able with a bulk relabeling, or whether the y-axis case analysis differs in a way not anticipated by this handoff (the x-proof's internal structure was not independently re-derived by this MAPS pass — only its public theorem statement was read).
- This handoff deliberately stays silent on SQ-CV-06 (whether the paper's tangential scaling itself is physically correct) — do not fold a "corrected" variant into this proof; if LAPS judges the corrected-formula question relevant while working this ticket, flag it back to MAPS rather than deciding it unilaterally.

---

## Return path

- **LAPS formal-status:** proved — `opencv_openlensio_full_pipeline_pixel_sufficiency_y` and `opencv_openlensio_full_pipeline_pixel_iff_y`, `lake build` (full project) succeeds, 0 `sorry`/`admit`/unauthorized `axiom`.
- **LAPS semantic-status:** accepted — statement matches this handoff's exact intended claim verbatim (confirmed in `docs/laps/y-pixel-equivalence/proof-review.md`); uses the paper's as-published tangential formula only, does not fold in the corrected alternative, per this handoff's explicit instruction.
- **Artifacts updated on return:** `evidence-matrix.md` § EVID-006 (realized); `property-register.md` § PROP-003 (Evidence coverage, Residual gaps); `correctness-assurance.md` § 3.3; `assurance-case.md` PROP-003 trace. All updated — see those files directly.
- **Notes:** Two discrimination open questions this handoff flagged were resolved during the work, not left open: (1) the x-proof script *was* mechanically mirrorable, with two recorded exceptions — a hypothesis-name collision (`h` meaning "sensor height" in the y-file's established naming vs. "pixel-equality hypothesis" in the x-file's convention) and an associativity-driven need to split one combined helper lemma into two single-term lemmas, both resolved and recorded in `docs/laps/y-pixel-equivalence/proof-run-log.md`; (2) the required discrimination check needed a new local extraction lemma (`whole_tangential_field_iff_y`) not present in the original capsule, since the y-term shape has no existing 1D iff lemma to call directly (only the combined 2D `whole_tangential_field_2d_iff`, which only exercises the δx component in its own proof). Joint-2D and pure-radial gaps (deferred, out of this handoff's scope) are untouched.
