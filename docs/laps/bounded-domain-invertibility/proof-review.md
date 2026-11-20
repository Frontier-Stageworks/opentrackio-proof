# Proof Review — bounded-domain-invertibility

## A. Scope

5 new files, ~31 new declarations (definitions + theorems). Exhaustive inventory in
`audit/BOUNDED_DOMAIN_INVERTIBILITY.md` §3. No existing file modified (confirmed via
`git status` — only new untracked files).

## B. Kernel Status

`lake build` (plain, default targets) — 8396 jobs, exit 0 (up from 8391 before this
slice, i.e. exactly the 5 new files, auto-swept by `PipelineEquivalence`'s existing
`Pipeline.+` glob with no `lakefile.toml` change needed). `#print axioms` on all ~31 new
declarations — every one depends only on `propext, Classical.choice, Quot.sound`. Zero
`sorry`/`admit`/custom `axiom`/`native_decide`/`unsafe`/`partial` (grep, zero matches).

## C. Semantic Review

### Does the work match the task's five priorities?

1. **Denominator safety from explicit coefficient bounds**: yes —
   `denom_pos`/`denom_ge` (`RationalRadialBounds.lean`), condition
   `denomMargin θ R = |k4|R²+|k5|R⁴+|k6|R⁶ < 1`, fully explicit and checkable from the
   coefficients and disk radius alone.
2. **Sufficient conditions for injectivity + existence of a unique inverse via Lipschitz
   bounds and contraction mapping**: yes — `RDist_injective_on_disk` (algebraic,
   contraction-based, mirroring `D_eq_implies_eq`) and, more significantly,
   `RDist_exists_unique_preimage` (genuine Banach fixed-point existence/uniqueness, not
   merely injectivity) for the ACTUAL rational+tangential model.
3. **Connected to the existing 2D inverse-conjugacy theorem**: yes —
   `CVmap_inverse_invOn` produces a value of EXACTLY the type
   `opencv_openlensio_inverse_conjugate`'s `hCVInv` parameter expects (confirmed both by
   direct inspection of the two type signatures and by a scratch end-to-end
   type-compatibility check).
4. **Two nontrivial Lean-verified examples, one with both radial and tangential
   distortion, with positive-radius certified regions**: yes —
   `example1_invertible` (pure radial, `k1=k4=1/10`) and `example2_invertible`/
   `example2_CVmap_invertible` (radial+tangential, adds `p1=1/100`), both on the unit
   disk `R=1`, both with `denomMargin`/`LPert` side conditions verified by `norm_num`.
5. **Full build, axiom audit, hidden/unnecessarily-strong-assumption check**: this
   section and `audit/BOUNDED_DOMAIN_INVERTIBILITY.md` §7.

### Is any theorem vacuous or does any hypothesis smuggle the conclusion?

No. The two concrete examples are non-identity (nonzero `k1,k4,p1`), demonstrating the
hypothesis set (`hsafe`, `hcontract`) is satisfiable without assuming the all-zero
degenerate case. `denomMargin`/`LPert` are independent, explicit functions of the
coefficients and `R` — the theorems do not take "the lens is invertible" or an
equivalent restatement as a free hypothesis anywhere; they derive it from coefficient
bounds.

### Hard step identification

The quotient-rule Lipschitz bound for the rational radial factor (`Rfac_lipschitz`,
`RationalRadialBounds.lean`) is the hard step — it is the one piece of genuinely new
real-analysis content this slice contributes beyond what `InverseApproximation.lean`
already had (which has no denominator at all). It was identified in `proof-capsule.md`
before tactic work began and closed in the number of iterations recorded in
`proof-run-log.md` (type-mismatch and missing-unfold fixes, not an algebra-tripwire
spiral — no `field_simp`/`ring` call was attempted more than twice on the same goal).

### A genuine mathematical correction, not a tactic failure

`RDist_inverse_invOn`'s originally-drafted domain (`{z | ‖z‖≤R}` for the left-inverse
side) was **mathematically wrong**, not merely a proof-tactic problem — caught when
`linarith` could not derive that a point's *image* under `RDist` lands in the smaller
buffer region where the Banach-constructed inverse is actually characterized. This is
exactly the kind of "hypothesis found too weak" situation the LAPS protocol calls a
`STATEMENT CHANGE STOP` for. The fix was not to weaken the claim to route around the
difficulty, but to correct the domain to the mathematically accurate set
(`{z | ‖z‖≤R ∧ ‖RDist θ z‖+MPert θ R≤R}`) and propagate that correction through the one
downstream theorem (`CVmap_inverse_invOn`) that depended on it. See
`proof-run-log.md` Entry 4 for the full record.

### Anti-pattern scan

No tactic soup; every nontrivial `have` has a stated role either in-file or in
`proof-run-log.md`. No algebra ping-pong (each `field_simp`/`ring`/quotient-bound `calc`
closes on first or second attempt, per the run log's own failure classifications — the
Algebra Tripwire's two-attempt limit was never reached). No global `[simp]`/`[grind]`
annotations added anywhere. The one `native_decide`-adjacent risk category does not
apply here (no such construct used). Heavy reuse of `InverseApproximation.lean`'s
generic lemmas (`radial_bounded`, `radial_lipschitz`, `normSq_*`, `smul_norm`,
`phi_bounded`, `phi_lipschitz`) is deliberate and documented in each file's header, not
incidental — this is the slice's main "reuse existing proofs" discipline in practice.

## D. Required Action Split

- Mathematical/proof action: none outstanding — all 5 priorities complete and
  kernel-checked.
- Documentation action: `audit/BOUNDED_DOMAIN_INVERTIBILITY.md` (this slice's required
  deliverable).
- Process-evidence action: none outstanding — exact build commands, axiom-print output,
  and forbidden-construct scan commands are all recorded with their literal output in
  `proof-run-log.md` and the audit deliverable.

## E. Final Classification

**Accepted, with explicitly-scoped limitations** (not a full resolution of native
OpenLensIO D→U interoperability or production correctness — never claimed to be, and
explicitly disclaimed in every new file's header and in the audit deliverable). The
domain-correctness issue caught mid-session is exactly the kind of thing this review
process exists to catch, and it was caught and fixed rather than silently weakened or
left as a latent error.

## F. Correction pass (adversarial re-review)

A second adversarial reviewer (the user) correctly identified that `k1=k4` in both
original examples collapses the radial factor `R(u)=(1+k1 u+...)/(1+k4 u+...)` to the
identity (`≡1`), making Example 1 exactly the identity map and Example 2
tangential-only. This was a genuine gap in this review's own first pass (§C above did not
catch it). Fixed in `Pipeline/RationalDistortionExamples.lean`: new coefficients
`k1=1/5, k4=1/20` for both examples, with explicit, machine-checked non-identity proofs
(`example1_not_identity`, `example2_not_identity`, `example2_tangential_active`) rather
than a bare nonzero-coefficient claim. Additionally, in the same pass: the end-to-end
composition into `opencv_openlensio_inverse_conjugate` was upgraded from a scratch,
non-committed type-check to a permanent, fully-resolved theorem
(`example2_full_inverse_conjugate`), and the global `hden`/`hdenOTI` hypotheses were
discharged outright (`hden_shared`, `hdenOTI_shared`, via `positivity`, since the chosen
`k4, l2 > 0` with all other denominator coefficients zero make the denominators
`≥1` for every real input, not just within the certified disk).

Re-verified: `lake build` (plain, default targets) — 8396 jobs, exit 0 (unchanged count —
this pass edited existing file content, added no new files). `#print axioms` on all ~37
declarations in the 5-file slice — all depend only on `propext, Classical.choice,
Quot.sound`. Word-boundary forbidden-construct scan — zero genuine matches. No
established definition or previously-proved theorem statement (from the first pass) was
altered; only `RationalDistortionExamples.lean`'s example instantiations and the audit
document were changed.

**Revised classification: Accepted**, with the identity-map defect in the examples now
corrected and the review process's own miss of it recorded rather than hidden.
