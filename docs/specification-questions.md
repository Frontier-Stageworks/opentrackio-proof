# Specification Questions

Open and resolved ambiguities surfaced during formalization. Formalization forces
every question to be answered before a function can be defined; questions that prose
reading leaves implicit become compile errors here.

Each entry has a status: **open**, **resolved**, or **deferred**.

---

## OpenLensIO v1.0.1

### SQ-OL-01: Denominator nonzero condition
**Status: open**

The radial distortion factor is a rational polynomial `R(r²)` whose denominator can
be zero for pathological coefficient values (e.g., k₂ = −1, r = 1). The specification
is silent on what happens at a zero denominator. The formal model makes this explicit
via the `denominatorNonzero` per-point domain predicate that every call site must
supply. There is no specification guidance on what coefficient constraints or radius
bounds would guarantee nonzero denominators in practice. Implementations that do not
handle this case silently produce undefined or infinite output.

### SQ-OL-02: Overscan asymmetry
**Status: deferred**

Equations 8 and 15 (the overscan equations) drop the ΔC and ΔP offsets
asymmetrically between the two forms — one form includes them and the other does not,
with no explanation. No overscan theorems are attempted in this repository until this
asymmetry is resolved by the specification. Any formalization of overscan must first
decide which form is normative.

### SQ-OL-03: Forward distortion inversion method
**Status: open**

The specification notes that the inverse of the undistortion function U (i.e., the
forward distortion D such that U(D(ε)) = ε) requires iterative numerical methods and
provides no closed form. D is not formalized. This means roundtrip properties
`U(D(ε)) = ε` and `D(U(ε)) = ε` cannot be proved, and an implementation of D cannot
be validated against the formal model.

### SQ-OL-04: Float-to-exact-real bridge
**Status: deferred**

The executable Float layer and the exact-real proof layer have structurally different
function signatures — exact functions carry domain proofs in their types; Float
functions return `Option` on domain failure. No theorem connects their outputs. Bridging
requires IEEE 754 error-bound machinery. Deferred pending a decision on whether
floating-point correctness is in scope.

### SQ-OL-05: ΔP coordinate sign convention
**Status: resolved**

Both Equation 13 and the inline text near Equation 10 write `ε_d = ε'_d + ΔP` in the
same form. The sign convention is load-bearing for the FOV ↔ projection consistency
theorem. Confirmed consistent in the specification; formalized as `deltaP_characterisation`.

### SQ-OL-06: Distortion-center frame for tangential evaluation
**Status: resolved**

Undistortion U is applied to the shifted coordinate `ε_d − ΔC − ΔP`. The tangential
correction inside U uses a radius r computed from this shifted point. An implementation
that computes r from the unshifted coordinate produces subtly wrong output. This is
derivable from the call-site structure in the specification; formalized as
`distortion_center_translation_commutes` and `fov_undistort_eq`.

### SQ-OL-07: Invertibility and continuity of U
**Status: open**

U is not proved injective, surjective, continuous, or invertible. For well-calibrated
lenses these properties are plausible but require analytical machinery (intermediate
value theorem, derivative bounds for monotonicity) not present in the current proof
infrastructure. The specification does not state or prove these properties.

### SQ-OL-08: Angle-of-view at F = 0
**Status: open (benign)**

`angle_of_view_eq` holds for all F including F = 0, where Lean's total real-number
division gives 0/0 = 0. This is technically correct but physically meaningless. All
intended call sites enforce `F > 0`. The specification is silent on degenerate focal
lengths.

---

## OpenCV ↔ OpenLensIO Conversion

### SQ-CV-01: Pure-radial case (p1 = p2 = 0)
**Status: open**

When both tangential coefficients are zero, `ws/w = fx` is not entailed by universal
pixel agreement — the tangential term that would reveal the scale discrepancy is
identically zero and the two pipelines agree regardless of `ws/w`. The iff theorem
requires `p1 ≠ 0 ∨ p2 ≠ 0` to handle this. The behavior of purely-radial pipelines
under mismatched `ws/w` is not separately characterized.

### SQ-CV-02: Denominator nonzero derivability from coefficient bounds
**Status: open**

The conversion proofs take `hden : ∀ x' y', denominator ≠ 0` as a free hypothesis.
Deriving this from physically-meaningful bounds on the coefficients k4, k5, k6 — e.g.,
showing the denominator stays positive over a bounded working radius — is not proved.
Connecting the abstract hypothesis to real calibration data requires this bridge.

### SQ-CV-03: Coefficient naming conflict between OTI and OpenCV
**Status: resolved**

`RadialCoefficients` in `LensSemantics.lean` uses the OTI alternating convention:
k1,k3,k5 = numerator; k2,k4,k6 = denominator. OpenCV uses the sequential convention:
k1,k2,k3 = numerator; k4,k5,k6 = denominator. The conversion library (`DistortionConversion.lean`)
uses raw `ℝ` parameters in the OpenCV convention and assembles a `RadialCoefficients`
value with an explicit field mapping. The two naming conventions must not be conflated.

### SQ-CV-04: Single focal length F vs separate fx, fy
**Status: resolved**

OpenCV uses separate horizontal and vertical focal lengths `fx`, `fy`. OpenLensIO uses
a single `F`. `single_focal_length_compatibility` proves that 2D pixel consistency
forces `(w/ws)·fx = (h/hs)·fy` — the exact condition under which both can be
represented by one F. When this condition fails, no single F makes the full 2D
pipeline equivalent.

### SQ-CV-05: y-component symmetry
**Status: open**

The pipeline iff is proved for the x-pixel coordinate only. The y-component is
expected to be symmetric (p1 ↔ p2 swapped) but is not yet formalized.

---

## OpenTrackIO Parser

### SQ-PA-01: Duplicate JSON key behavior
**Status: open**

`decodeSample` uses `lookup?`, which returns the first match in a JSON object and
silently ignores subsequent keys with the same name. The OpenTrackIO specification
does not state whether duplicate keys are an error, which value is authoritative, or
whether producers are required to avoid them. The formal model handles duplicates only
through the `WellFormedSampleJson` predicate's `NoDupKeys` condition.

### SQ-PA-02: Unknown top-level vs unknown nested fields
**Status: open (by design)**

The OpenTrackIO extension policy allows unknown top-level fields in a `Sample`. The
model permits these silently. Unknown nested fields inside known sub-objects (e.g.,
inside `lens`) are handled through `WellFormedSampleJson` rather than by making all
decoders reject unknown keys. This distinction reflects the specification's stated
policy but is worth revisiting if strict validation is required.

### SQ-PA-03: `WellFormedSampleJson (encodeSample s)` not proved
**Status: open**

`encodeSample_roundtrip` proves that encode → decode returns the original sample.
Whether `encodeSample s` itself satisfies `WellFormedSampleJson` — i.e., whether the
encoder produces schema-clean JSON — is not proved. This is a private-boundary issue:
`WellFormedSampleJson.lean` cannot see the encoder internals in the current module
structure.

### SQ-PA-04: Numeric upper bounds
**Status: deferred**

Frame rates, pixel counts, angle ranges, and similar schema-bounded fields are stored
as `PositiveRational` (positivity enforced) but not range-checked. Formalizing these
bounds would require extending the model types or adding validation predicates.
Deferred pending a decision on how much of the schema-level validation is in scope.
