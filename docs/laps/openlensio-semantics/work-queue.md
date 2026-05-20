---
name: openlensio-semantics-work-queue
description: LAPS work queue and proof roadmap for openlensio_semantics project; all slices, theorem inventory, risk matrix, gates
metadata:
  type: reference
---

# LAPS Work Queue — `openlensio_semantics`

**Source document:** OpenLensIO v1.0.1 PDF  
(`OpenLensIO_v1-0-1.pdf`, title page: "OpenLensIO Lens Model Version 1.0.0", 17 February 2025)  
**Status:** Gates 0–3 complete. Slices OL-00, OL-01–OL-15 DONE. All Stop 4 reviews complete. Campaign complete through Layer F.  
**Phase:** Complete — Layers B, C/D, C/E, F all done. External differential testing blocked (see OL-15 review). Gate 7 (high-risk analysis) deferred.

---

## 1. Executive Summary

`openlensio_semantics` adds **mathematical semantic content** that the parser project deliberately excluded.

`opentrackio_parser` gives us:
- Typed Lean values decoded from JSON: `Lens`, `Camera`, `Sample`, `Distortion`, `DistortionOffset`, `ProjectionOffset`, etc.
- Roundtrip theorems, normalization theorems, encoder soundness
- Raw string fields for numeric values (parsing to rational numbers deferred)
- The `NonemptyArray` invariant on distortion arrays

`opentrackio_parser` gives us **no**:
- Interpretation of the string values as numbers
- Validated semantic domains (focal length positive, etc.)
- Mathematical distortion functions
- Projection models
- FOV characterisations
- Coordinate-space models
- Denominator safety guarantees

`opencv_opentrackio_proofs` gives us:
- Conversion between OpenCV principal-point conventions and OpenTrackIO conventions
- Distortion-coefficient conversion (radial and tangential) between OpenCV and OpenTrackIO parameterisations
- Pixel-coordinate preservation under those conversions
- Uniqueness and necessity theorems for the conversion formulas

`opencv_opentrackio_proofs` gives us **no**:
- The OpenLensIO distortion model itself (it models the OpenCV ↔ OpenTrackIO conversion, not the forward/inverse distortion function)
- Projection or FOV characterisations
- Coordinate-frame definitions for the OpenLensIO model
- ΔP and ΔC semantics

`openlensio_semantics` must build the semantic bridge from decoded typed values into a mathematical model of the OpenLensIO distortion and projection functions, and prove properties of that model.

**What to verify next:**
1. Semantic bridge: parser `Lens` → validated `LensSemantics`
2. Coordinate-space and sensor-metric coordinate types
3. Rational-polynomial (radial R) definition with denominator safety
4. Brown-Conrady undistortion function U(ϵ) in component form
5. Zero-coefficient identity lemmas
6. Projection and FOV model definitions
7. ΔP / ΔC translation lemmas

**What to defer:**
- Overscan containment theorems (informative appendix, hard analysis)
- Global invertibility of U
- Continuity / monotonicity arguments
- Aperture model (paper explicitly under investigation)
- Vignetting model (future work per paper)
- Anamorphic, chromatic aberration (future per paper)
- Floating-point error bounds

**Highest-risk proof areas:**
- `projection_fov_equiv` — depends on AMB-OL-002, AMB-OL-003, AMB-OL-008
- `undistorted_roundtrip_preserves_pixel` — depends on AMB-OL-010 (U invertibility)
- Overscan containment — informative section, requires real analysis
- Denominator safety across full domain — may require domain restriction hypotheses

---

## 2. Phase 0 — Spec Extraction Table

All equations extracted from the PDF. Source version: as read above.

| ID | Section/Eq | Statement or Equation | Variables | Coord Space | Units | Domain Assumptions | Type | Already Proved? | Proof Status |
|----|------------|----------------------|-----------|-------------|-------|-------------------|------|-----------------|--------------|
| OL-SPEC-001 | §1.1 | F = focal length | F | — | mm | F > 0 (inferred) | Normative | No | Open |
| OL-SPEC-002 | §1.1 | w = width of active sensor area | w | Image | mm | w > 0 | Normative | No | Open |
| OL-SPEC-003 | §1.1 | ϵ = [ϵ_x, ϵ_y]^T, screen coords in mm, origin at screen centre, ϵ_x right, ϵ_y down | ϵ_x, ϵ_y | Image (mm) | mm | — | Normative | No | Open |
| OL-SPEC-004 | §1.1 | r = sqrt(ϵ_x² + ϵ_y²) | r, ϵ | Image (mm) | mm | r ≥ 0 | Normative | No | Open |
| OL-SPEC-005 | §1.2 | World frame: right-handed, X_W=Right, Y_W=Forward, Z_W=Up | X_W,Y_W,Z_W | World | metres | — | Normative | No | Open |
| OL-SPEC-006 | §1.2 | Camera frame: X_p=Right, Y_p=Down, Z_p=Forward | X_p,Y_p,Z_p | Camera | metres | — | Normative | No | Open |
| OL-SPEC-007 | §1.2 | Image frame: mm, origin at image centre, ϵ_x right, ϵ_y down | ϵ_x,ϵ_y | Image | mm | — | Normative | No | Open |
| OL-SPEC-008 | §1.4 Eq(1) | [x,y,z]_p = [R\|t]_s [x,y,z,1]_W - [0,0,z_epd]^T | R,t,z_epd | World→Camera | metres | z_p ≠ 0 for projection | Normative | No | Open |
| OL-SPEC-009 | §1.4 Eq(2) | [x,y]_u = (1/z_p)[x,y]_p | z_p | Camera→Image | — | z_p ≠ 0 | Normative | No | Open |
| OL-SPEC-010 | §1.5 | ΔC = [ΔC_x, ΔC_y]^T, distortion-centre offset | ΔC | Image | mm | — | Normative | No | Open |
| OL-SPEC-011 | §1.5 | ΔP = [ΔP_x, ΔP_y]^T, perspective offset | ΔP | Image | mm | — | Normative | No | Open |
| OL-SPEC-012 | §1.5 | ΔP = translation from ϵ_u/ϵ_d shared centre to centre of projection ϵ′_u | ΔP | Image | mm | — | Normative | No | Open |
| OL-SPEC-013 | §1.5 | ΔC = translation from ϵ′_u centre to distortion centre | ΔC | Image | mm | — | Normative | No | Open |
| OL-SPEC-014 | §2 Eq(3) | ϵ_u = F·[x/z_p, y/z_p]^T + ΔP | F,ΔP,z_p | Camera→Image | mm | F>0, z_p≠0 | Normative | Yes | ✅ `projectToImage` def + `projection_matrix_undistort_eq` (OL-10) |
| OL-SPEC-015 | §2 Eq(4) | ϵ_u = U(ϵ_d − ΔC − ΔP) + ΔC + ΔP | U,ϵ_d,ΔC,ΔP | Image | mm | Denominator of R ≠ 0 | Normative | Yes | ✅ `undistortFromDistorted` def + `projection_matrix_undistort_eq` (OL-10) |
| OL-SPEC-016 | §2 Eq(5) | ϵ_d = U⁻¹(ϵ_u − ΔC − ΔP) + ΔC + ΔP | U⁻¹,ϵ_u,ΔC,ΔP | Image | mm | U invertible (see AMB-OL-010) | Normative | No | Assumption-gated |
| OL-SPEC-017 | §2 Eq(6) | r_u/F = tan(α/2), centred at ΔP | r_u,F,α | Image | mm/rad | F>0, r_u≥0 | Normative | Yes | ✅ `angle_of_view_eq` (OL-12); `angleOfView` def |
| OL-SPEC-018 | §2.1 Eq(7) | ϵ_Ω = (1/Ω)·F·[x/z_p,y/z_p]^T + ΔP | Ω,F,ΔP | Image | mm | Ω>0, F>0, z_p≠0 | Normative | No | Open |
| OL-SPEC-019 | §2.1 Eq(8) | ϵ_Ω = (1/Ω)·U(ϵ_d − ΔC − ΔP) | Ω,ϵ_d,ΔC,ΔP | Image | mm | Ω>0; no +ΔC+ΔP (see AMB-OL-003) | Normative | No | Assumption-gated |
| OL-SPEC-020 | §3 Eq(9) | ϵ′_u = F·[x/z_p,y/z_p]^T | F,z_p | Camera→Image | mm | F>0, z_p≠0 | Normative | Yes | ✅ `fovProjectToImage` def (OL-11) |
| OL-SPEC-021 | §3 Eq(10) | ϵ′_u = U(ϵ′_d − ΔC) + ΔC | U,ϵ′_d,ΔC | Image | mm | Denominator ≠ 0 | Normative | Yes | ✅ `fovUndistortFromDistorted` def + `fov_undistort_eq` (OL-11) |
| OL-SPEC-022 | §3 Eq(11) | ϵ′_d = U⁻¹(ϵ′_u − ΔC) + ΔC | U⁻¹ | Image | mm | U invertible (AMB-OL-010) | Normative | No | Assumption-gated |
| OL-SPEC-023 | §3 Eqs(12,13) | ϵ_u = ϵ′_u + ΔP; ϵ_d = ϵ′_d + ΔP | ΔP | Image | mm | see AMB-OL-002 | Normative | Yes | ✅ `distortion_center_translation_commutes` + `fov_undistort_eq` (OL-09, OL-11) |
| OL-SPEC-024 | §3.1 Eq(14) | θ_Ω′ = 2·arctan(w_Ω′/(2F)) | θ,w_Ω′,F | — | rad/mm | F>0, w_Ω′>0 | Normative | Yes | ✅ `fovAngleFromWidth` def (OL-12); no roundtrip theorem (definitional consequence of `angleOfView`) |
| OL-SPEC-025 | §3.1 Eq(15) | ϵ′_Ω′ = (1/Ω′)·(U(ϵ_d−ΔC−ΔP)+ΔC) | Ω′,ϵ_d,ΔC,ΔP | Image | mm | Ω′>0; AMB-OL-009 | Normative | No | Assumption-gated |
| OL-SPEC-026 | §3.1 prose | Projection and FOV forms can generate equivalent renders | — | — | — | Conditions unstated (AMB-OL-008) | Normative claim | No | Assumption-gated |
| OL-SPEC-027 | §4.1 Eq(16) | U(ϵ) component form: U_x = R·ϵ_x + 2p₁ϵ_xϵ_y + p₂(r²+2ϵ_x²) | R,p₁,p₂,ϵ | Image (distortion-centred) | mm | Denominator of R ≠ 0 (AMB-OL-007) | Normative | Yes | ✅ `undistortX` def + `brown_conrady_zero_identity` (OL-07, OL-08) |
| OL-SPEC-028 | §4.1 Eq(16) | U(ϵ) component form: U_y = R·ϵ_y + p₁(r²+2ϵ_y²) + 2p₂ϵ_xϵ_y | R,p₁,p₂,ϵ | Image (distortion-centred) | mm | Denominator of R ≠ 0 | Normative | Yes | ✅ `undistortY` def + `brown_conrady_zero_identity` (OL-07, OL-08) |
| OL-SPEC-029 | §4.1 Eq(17) | R = (1+k₁r²+k₃r⁴+k₅r⁶)/(1+k₂r²+k₄r⁴+k₆r⁶) | k₁…k₆, r | Image | mm^{−2m} per term | Denominator ≠ 0 (AMB-OL-007) | Normative | Yes | ✅ `radialTerm` def + `radial_zero_coefficients_identity` (OL-05, OL-06) |
| OL-SPEC-030 | §4.1 Eq(17) | k₁,k₃,k₅ are numerator coefficients; k₂,k₄,k₆ are denominator coefficients, alternating | — | — | see AMB-OL-005 | — | Normative | No | Open |
| OL-SPEC-031 | §4.2 Eq(18) | ε_shader_x = wshader·ϵ_x/w + wshader/2; ε_shader_y = wshader·ϵ_y/h + wshader/2 | wshader,w,h,ϵ | Image→Shader | px/mm | w>0, h>0, wshader>0 | Normative | Yes | ✅ `pixel_metric_roundtrip`, `image_texture_coordinate_roundtrip` (OL-13) |
| OL-SPEC-032 | §4.3 Eq(19) | c_u = F²·\|S_o−Φ\|/(N·S_o·(Φ−F)) | F,Φ,S_o,N | Undistorted screen | mm | Under investigation | NOT normative | No | Defer |
| OL-SPEC-033 | §4.4 Eq(20) | υ_n(r) = 1 − (α₁r²+α₂r⁴+α₃r⁶) | α₁,α₂,α₃,r | Image | — | — | Normative | No | Defer |
| OL-SPEC-034 | §A.1 Eqs(21-24) | Ideal overscan algorithm | Ω,wΩ,ϵ_u^i | Image | mm | Informative only | Informative | No | Defer (low priority) |

---

## 3. Project Boundary and Dependency Plan

### Proposed Project

**Name:** `openlensio_semantics`  
**Location:** `/Users/markstalzer/github/opentrackio-proof/openlensio_semantics/`  
**Lean package:** New library target in `lakefile.toml`, separate from `opentrackio_parser`

### Imports allowed

From `opentrackio_parser`:
- `LensModel` — `Lens`, `StaticLens`, `Distortion`, `DistortionOffset`, `ProjectionOffset`, `FizOptions`, `ExposureFalloff`
- `SampleModel` — `Sample`
- `CameraModel` — `Camera`
- `TransformModel` — `Transform`
- `RationalValueWrappers` — `PositiveRational`, `NonzeroNat`, etc.
- `NonemptyArrayDecoder` — `NonemptyArray`
- `DecodeError` — for error typing if needed

From `opencv_opentrackio_proofs`:
- May import if a bridge theorem is needed, but only for explicit bridge points
- Must not re-prove coefficient conversion theorems already in `DistortionConversion`
- Must not re-prove pixel equivalence already in `PixelEquivalence`

### Must NOT modify

- Any file in `opentrackio_parser/`
- Any file in `opencv_opentrackio_proofs/`
- `battery-tester/`
- `lakefile.toml` parser/opencv targets

### Dependency arrows

```
opentrackio_parser
  (Lens, Distortion, Sample, Camera, PositiveRational, NonemptyArray, ...)
        |
        ▼
openlensio_semantics
  SemanticBridge          -- parser types → semantic types
  CoordinateSpaceModel    -- image, camera, world frames
  SensorMetric            -- mm-coordinate types
  RadialPolynomial        -- R with denominator safety
  DistortionModel         -- U(ϵ) component form, domain predicates
  ProjectionModel         -- Eq(3), Eq(14), FOV equations
  DeltaSemantics          -- ΔP, ΔC definitions and translation lemmas
  IdentityLemmas          -- zero-coefficient identities
  ProjectionFovEquiv      -- Eqs(12,13), assumption-gated equivalence
  PixelMetricRoundtrip    -- image ↔ shader coordinate conversion
  ExecutableSemanticOracle -- Float approximation, computable
        |
        ▼
  differential semantic tests / battery-tester
```

### Bridge shape (representation plan, no code)

The semantic bridge transforms parser-layer strings into validated semantic types:

```
parser: Lens.distortion          : Option (NonemptyArray Distortion)
parser: Distortion.radial        : NonemptyArray String   -- raw JSON number strings
parser: Distortion.tangential    : Option (NonemptyArray String)
parser: Lens.pinholeFocalLength  : Option String
parser: Lens.distortionOffset    : Option DistortionOffset
parser: Lens.projectionOffset    : Option ProjectionOffset
```

Semantic bridge proposes:

```
SemanticBridge:
  parseRationalCoeff : String → Option ℚ  -- or ParsedCoeff type
  extractLensSemantics : Lens → Except SemanticError LensSemantics
  extractRadialCoeffs  : NonemptyArray String → Except SemanticError RadialCoefficients
  ...
LensSemantics:
  focalLength    : PositiveRational
  radialCoeffs   : RadialCoefficients       -- k₁..k₆ as ℚ values
  tangCoeffs     : TangentialCoefficients   -- p₁, p₂ (default 0)
  distortionCentre : SensorPoint             -- ΔC
  perspectiveOffset : SensorPoint            -- ΔP
  ValidLensSemantics : LensSemantics → Prop
    -- includes: radial denominator nonzero for domain, F > 0, ...
```

---

## 4. Layer Architecture

### Layer A — Parser/data foundation (COMPLETE — do not re-prove)

**Purpose:** Decode bytes/JSON into typed Lean values  
**Inputs:** `JsonValue` AST  
**Outputs:** `Lens`, `Sample`, `Camera`, `Distortion`, `PositiveRational`, `NonemptyArray`, etc.  
**Existing support:** All of `opentrackio_parser/`  
**New Lean objects needed:** None  
**Must NOT prove in this layer:** Mathematical distortion functions, projection models, coordinate frames, semantic validity

### Layer B — Semantic validity

**Purpose:** Establish that typed parser values satisfy OpenLensIO semantic domain requirements  
**Inputs:** Parser-layer Lean types  
**Outputs:** `ValidLensSemantics`, `ValidDistortionCoefficients`, `ValidFocalLength`, `ValidSensorDimensions`  
**Existing support:** Parser carries structural invariants (nonempty arrays, option presence). Semantic invariants (positive focal length, nonzero denominator) are new.  
**New Lean objects needed:** `LensSemantics`, `CameraSemantics`, `ValidLensSemantics`, `RadialCoefficients`, `TangentialCoefficients`, `SemanticBridge`  
**Must NOT prove in this layer:** The distortion function itself; projection equations; coordinate-space models

### Layer C — Mathematical model

**Purpose:** Exact-real or rational mathematical functions for OpenLensIO projection, distortion, and coordinate transforms  
**Inputs:** `LensSemantics`, coordinate-space types, `SensorPoint`  
**Outputs:** `undistortPoint`, `radialTerm`, `distortionFunction`, `projectionMatrixCharacterisation`, `fovCharacterisation`  
**Existing support:** None in current projects  
**New Lean objects needed:** `SensorPoint`, `CameraPoint`, `RadialPolynomial`, `undistortComponent`, `projectionParameters`, `fovParameters`  
**Must NOT prove in this layer:** Equivalence theorems (those are Layer E); denominator safety (Layer D); executable Float versions (Layer F)

### Layer D — Numerical/domain safety

**Purpose:** Prove that the mathematical model is well-defined on its domain  
**Inputs:** Layer B validity predicates, Layer C definitions  
**Outputs:** `radial_denominator_nonzero_under_constraints`, `distortion_finite_on_bounded_domain`, `projection_well_defined`  
**Existing support:** None  
**New Lean objects needed:** Domain predicates, safe-denominator lemmas  
**Must NOT prove in this layer:** Equivalence or preservation theorems

### Layer E — Equivalence/preservation properties

**Purpose:** Projection/FOV equivalence, ΔP/ΔC translation lemmas, coordinate roundtrips, identity properties  
**Inputs:** Layers C and D  
**Outputs:** `projection_fov_equiv`, `deltaP_translation_commutes`, `zero_distortion_identity`, `pixel_metric_roundtrip`  
**Existing support:** `opencv_opentrackio_proofs` covers the OpenCV↔OTio conversion; not the OpenLensIO model itself  
**New Lean objects needed:** Translation lemmas, identity theorems  
**Must NOT prove in this layer:** Parser correctness; floating-point approximation accuracy

### Layer F — Executable validation / differential testing

**Purpose:** Reference model execution; comparison against reference implementations  
**Inputs:** Layer C definitions made computable  
**Outputs:** `executableUndistort`, `executableProjection`, oracle output format, battery-tester adapter  
**Existing support:** `battery-tester/` harness, `HarnessAdapter.lean` in parser  
**New Lean objects needed:** `Float`-based executable counterparts, oracle adapter  
**Must NOT prove in this layer:** Exact-real theorems; conflate Float execution with proved exact semantics

---

## 5. Lean Representation Plan

### Coordinate-space types

**Recommendation:** Use phantom-type tagged records.

```
-- Phantom tags (no code, proposed representation)
SensorCoords     -- millimetre screen coordinates, origin at centre
CameraCoords     -- pinhole camera frame (metres)
WorldCoords      -- world frame (metres)
ShaderCoords     -- normalised shader/texture coordinates
DistortionCentredCoords -- shifted by −(ΔC + ΔP)
```

**Why it matches the paper:** Section 1.2 defines three distinct coordinate frames with different units and origins. Phantom types prevent accidental mixing.  
**Why proof-friendly:** Theorems about coordinate transforms become typed functions between phantom-typed records; mismatched frames fail to typecheck.  
**What would cause proof spirals:** Collapsing all coordinate types into `ℝ × ℝ` with no tagging; every lemma then requires explicit frame hypotheses.

### Exact real numbers vs rational numbers

**Recommendation:** Use `ℚ` for coefficient values decoded from JSON (all coefficients are finite rational approximations); use `ℝ` only for intermediate mathematical functions (arctan in FOV, sqrt for r). Maintain a clear boundary.

**Why it matches the paper:** All parameters are finite floating-point numbers in practice; exact-real machinery is needed only for arctan-based FOV equations and continuity arguments.  
**What would cause proof spirals:** Using `ℝ` everywhere when most theorems are purely algebraic over `ℚ` or `ℤ`.

### Radial polynomial / denominator-safe wrapper

**Recommendation:**

```
structure RadialCoefficients where
  k1 k2 k3 k4 k5 k6 : ℚ

-- Domain predicate (not a subtype to avoid proof-term explosion)
def denominatorNonzero (k : RadialCoefficients) (r : ℝ) : Prop :=
  1 + k.k2 * r^2 + k.k4 * r^4 + k.k6 * r^6 ≠ 0

def radialTerm (k : RadialCoefficients) (r : ℝ)
    (h : denominatorNonzero k r) : ℝ := ...
```

**Why it matches the paper:** Eq (17) with rational coefficients and real r (from mm-valued screen coordinates).  
**Why proof-friendly:** Making the nonzero condition an explicit hypothesis avoids `sorry` in domain safety lemmas.  
**What would cause proof spirals:** Trying to prove the denominator is always nonzero without the hypothesis; encoding the nonzero condition inside a `Subtype` everywhere.

### Distortion coefficients

**Recommendation:** Keep radial (k₁..k₆) and tangential (p₁, p₂) as separate structures. Optional p₁, p₂ default to zero at the semantic bridge.

```
structure TangentialCoefficients where
  p1 p2 : ℚ

def TangentialCoefficients.zero : TangentialCoefficients := ⟨0, 0⟩
```

### Distortion function U

**Recommendation:** Define as a component function pair (non-singular form), NOT the diagonal matrix form:

```
def undistortX (k : RadialCoefficients) (p : TangentialCoefficients)
    (ex ey r : ℝ) (h : denominatorNonzero k r) : ℝ :=
  radialTerm k r h * ex + 2 * p.p1 * ex * ey + p.p2 * (r^2 + 2 * ex^2)

def undistortY (k : RadialCoefficients) (p : TangentialCoefficients)
    (ex ey r : ℝ) (h : denominatorNonzero k r) : ℝ :=
  radialTerm k r h * ey + p.p1 * (r^2 + 2 * ey^2) + 2 * p.p2 * ex * ey
```

**Why it matches the paper:** This is the non-singular expansion of Eq (16)'s diagonal form. AMB-OL-004 documents the choice.  
**Why proof-friendly:** No singularities on coordinate axes; enables `ring` for polynomial identity proofs.

### Projection parameters

**Recommendation:**

```
structure ProjectionParameters where
  focalLength   : PositiveRational   -- F in mm
  perspOffset   : SensorPoint        -- ΔP in mm
  distCentre    : SensorPoint        -- ΔC in mm
  sensorWidth   : PositiveRational   -- w in mm
  sensorHeight  : PositiveRational   -- h in mm
```

### FOV parameters

**Recommendation:**

```
structure FovParameters where
  halfAngle : ℝ  -- or use w and F with arctan definition
  overscan  : Option PositiveRational
```

Alternatively represent the FOV by (w, F) and compute the angle as needed, to stay in the rational domain.

### Semantic extraction

**Recommendation:** Define `extractLensSemantics : Lean.Lens → Except SemanticError LensSemantics` where `LensSemantics` carries both `ProjectionParameters` and `RadialCoefficients`. The bridge theorem:

```
theorem semanticExtraction_sound :
  extractLensSemantics l = Except.ok s →
  ValidLensSemantics s
```

is the entry point for all subsequent theorems.

---

## 6. Dependency Graph

```
opentrackio_parser
  Lens, Distortion, Sample, Camera, PositiveRational, NonemptyArray
        |
        ▼
[SemanticBridge]          (Layer B)
  parseRationalCoeff
  extractLensSemantics
  extractRadialCoeffs
  semanticExtraction_sound
        |
        ▼
[CoordinateSpaceModel]    (Layer C)
  SensorPoint / ImagePoint (ℝ × ℝ tagged with SensorCoords)
  CameraPoint
  sensorNorm (r = ‖ϵ‖)
        |
        ▼
[RadialPolynomial]        (Layer C + D)
  RadialCoefficients
  denominatorNonzero
  radialTerm
  radial_denominator_nonzero_under_constraints   ← Layer D
        |
        ▼
[DistortionModel]         (Layer C + D)
  TangentialCoefficients
  undistortX, undistortY
  undistortPoint
  distortion_finite_on_bounded_domain            ← Layer D
        |
        ▼
[IdentityLemmas]          (Layer E — algebraic)
  radial_zero_coefficients_identity              -- k₁..k₆ = 0 → R = 1
  tangential_zero_coefficients_identity          -- p₁=p₂=0 → U_x=R·ϵ_x
  brown_conrady_zero_identity                    -- all zero → U(ϵ)=ϵ
        |
        ▼
[DeltaSemantics]          (Layer C + E)
  perspectiveOffset, distortionCentre
  deltaP_translation_commutes
  deltaC_shift_definition
  projection_matrix_undistort_eq   (Eq 4)
  fov_undistort_eq                 (Eq 10)
        |
        ▼
[ProjectionModel]         (Layer C + E)
  projectionMatrixCharacterisation (Eq 3, 4)
  fovCharacterisation (Eq 9, 10)
  projection_fov_equiv (Eqs 12,13 — assumption-gated on AMB-OL-002,008)
  angle_of_view_eq (Eq 6)
        |
        ▼
[PixelMetricRoundtrip]    (Layer E)
  shaderCoordinateConversion (Eq 18)
  pixel_metric_roundtrip
  image_texture_coordinate_roundtrip
        |
        ▼
[ExecutableSemanticOracle] (Layer F)
  Float-based executable counterparts
  oracle output format
  battery-tester adapter
```

**Dependency types:**
- `opentrackio_parser` → `SemanticBridge`: **parser/data dependency**
- `SemanticBridge` → `CoordinateSpaceModel`: **semantic validity dependency**
- `CoordinateSpaceModel` → `RadialPolynomial`, `DistortionModel`: **algebraic dependency**
- `DistortionModel` → `ProjectionModel`: **algebraic dependency**
- `ProjectionModel` → `PixelMetricRoundtrip`: **algebraic + coordinate dependency**
- `PixelMetricRoundtrip` → `ExecutableSemanticOracle`: **executable testing dependency**

---

## 7. Slice Breakdown

### SLICE-OL-00 — Project skeleton and imports ✅ DONE

**Layer:** A/B boundary  
**Goal:** Create `openlensio_semantics` Lean project with correct imports, no theorems yet  
**Inputs:** `opentrackio_parser` targets  
**Outputs:** Compiling `lakefile.toml` entry; stub `SemanticBridge.lean` that imports parser models  
**Theorem targets:** None  
**Blockers:** None  
**Proof difficulty:** N/A  
**Expected tactics:** N/A  
**Stop condition:** Project compiles; imports resolve  
**Acceptance criteria:** `lake build openlensio_semantics` succeeds with empty stubs

---

### SLICE-OL-01 — Semantic bridge types ✅ DONE

**Layer:** B  
**Goal:** Define `LensSemantics`, `RadialCoefficients`, `TangentialCoefficients`, `ProjectionParameters`, `ValidLensSemantics`  
**Inputs:** Parser `Lens`, `Distortion`, `DistortionOffset`, `ProjectionOffset`, `PositiveRational`  
**Outputs:** `LensSemantics` structure; `ValidLensSemantics` predicate  
**Theorem targets:** None yet (type definitions only)  
**Blockers:** AMB-OL-013 (default p₁, p₂ = 0 assumption must be documented)  
**Proof difficulty:** Low  
**Expected tactics:** Definitional; `#check` verification  
**Stop condition:** Types compile; `ValidLensSemantics` includes `denominatorNonzero` condition  
**Acceptance criteria:** Definitions reviewed for semantic fidelity against paper §1.3

---

### SLICE-OL-02 — Semantic extraction function ✅ DONE

**Layer:** B  
**Goal:** Define `extractLensSemantics : Lens → Except SemanticError LensSemantics`; parse raw string coefficients to `ℚ`  
**Inputs:** Parser `Lens`, `Distortion`, string-to-rational parser  
**Outputs:** `extractLensSemantics`, `SemanticError`  
**Theorem targets:** None yet  
**Blockers:** String-to-rational parsing must be consistent with `RationalValueWrappers`  
**Proof difficulty:** Low  
**Expected tactics:** Definitional  
**Stop condition:** Function compiles; returns `Except.error` for malformed inputs  
**Acceptance criteria:** Tested against representative inputs; no runtime panics on axis cases

---

### SLICE-OL-03 — Semantic extraction soundness ✅ DONE (Stop 4 complete)

**Layer:** B  
**Goal:** `semanticExtraction_sound : extractLensSemantics l = Except.ok s → ValidLensSemantics s`  
**Inputs:** SLICE-OL-01, SLICE-OL-02  
**Outputs:** Checked soundness theorem  
**Theorem targets:** `semanticExtraction_sound`  
**Blockers:** None (structure follows from definition)  
**Proof difficulty:** Low–Medium (requires unfolding extraction + validity predicate)  
**Expected tactics:** `simp [extractLensSemantics, ValidLensSemantics]`, `omega`/`linarith` for arithmetic conditions, `cases` for Option branches  
**Stop condition:** Theorem compiles without `sorry`; semantic review passes  
**Acceptance criteria:** Statement audit confirms `ValidLensSemantics` is not vacuous; includes denominator nonzero check

---

### SLICE-OL-04 — Coordinate space types ✅ DONE

**Layer:** C  
**Goal:** Define `SensorPoint`, image/camera/world coordinate types; define `sensorRadius`  
**Inputs:** Standard Lean types  
**Outputs:** `SensorPoint`, `sensorRadius`, `SensorPoint.zero`  
**Theorem targets:** `sensorRadius_nonneg : ∀ p, sensorRadius p ≥ 0`  
**Blockers:** None  
**Proof difficulty:** Low  
**Expected tactics:** `simp [sensorRadius]`, `positivity` or `nlinarith`  
**Stop condition:** Types compile; `sensorRadius_nonneg` proved  
**Acceptance criteria:** Phantom-type tags prevent coordinate-frame confusion

---

### SLICE-OL-05 — Radial polynomial definition and denominator safety ✅ DONE (Stop 4 complete)

**Layer:** C + D  
**Goal:** Define `radialTerm`; prove `radial_denominator_nonzero_under_constraints`  
**Inputs:** `RadialCoefficients`, `sensorRadius` (Eq 17)  
**Outputs:** `radialTerm`, domain predicate `denominatorNonzero`, safety lemma  
**Theorem targets:**
- `radialTerm_eq : radialTerm k r h = (1 + k1*r² + k3*r⁴ + k5*r⁶) / (1 + k2*r² + k4*r⁴ + k6*r⁶)`
- `radial_denominator_nonzero_under_constraints`

**Blockers:** AMB-OL-007 (denominator nonzero: producer vs consumer obligation). Resolution: treat as precondition.  
**Proof difficulty:** Low for definition; Medium for explicit domain conditions  
**Expected tactics:** `ring`, `field_simp [h]`, `linarith` for specific coefficient conditions  
**Stop condition:** `radialTerm` defined; denominator nonzero stated explicitly as hypothesis  
**Acceptance criteria:** Statement audit confirms nonzero condition is not vacuous; AMB-OL-007 documented in proof capsule

---

### SLICE-OL-06 — Zero-coefficient radial identity ✅ DONE (Stop 4 complete)

**Layer:** E (algebraic)  
**Goal:** `radial_zero_coefficients_identity : k1=0 → k2=0 → k3=0 → k4=0 → k5=0 → k6=0 → radialTerm k r h = 1`  
**Inputs:** SLICE-OL-05  
**Outputs:** Proved identity  
**Theorem targets:** `radial_zero_coefficients_identity`  
**Blockers:** None  
**Proof difficulty:** Low  
**Expected tactics:** `simp [radialTerm]`, `ring`, `norm_num`  
**Stop condition:** Theorem compiles  
**Acceptance criteria:** No `sorry`; `ring` or `field_simp` closes the goal

---

### SLICE-OL-07 — Brown-Conrady distortion function definition ✅ DONE (Stop 4 complete)

**Layer:** C  
**Goal:** Define `undistortX`, `undistortY`, `undistortPoint` in component (non-singular) form  
**Inputs:** SLICE-OL-05 (radialTerm), SLICE-OL-04 (SensorPoint), Eqs (16), (17)  
**Outputs:** `undistortX`, `undistortY`, `undistortPoint`  
**Theorem targets:** None yet (definitions only in this slice)  
**Blockers:** AMB-OL-004 documented (component form choice)  
**Proof difficulty:** N/A  
**Expected tactics:** Definitional  
**Stop condition:** Definitions compile  
**Acceptance criteria:** Comments note component form chosen over diagonal form; paper reference §4.1 Eq(16)

---

### SLICE-OL-08 — Zero-distortion identity theorem ✅ DONE (Stop 4 complete)

**Layer:** E  
**Goal:** When all k and p coefficients are zero, U(ϵ) = ϵ  
**Inputs:** SLICE-OL-06, SLICE-OL-07  
**Outputs:** `brown_conrady_zero_identity`  
**Theorem targets:**
- `tangential_zero_coefficients_identity : p1=0 → p2=0 → undistortX k p e = radialTerm k r h * e.x`
- `brown_conrady_zero_identity : allZeroCoeffs k p → undistortPoint k p ϵ h = ϵ`

**Blockers:** None  
**Proof difficulty:** Low  
**Expected tactics:** `simp [undistortX, undistortY]`, `ring`  
**Stop condition:** Both theorems proved  
**Acceptance criteria:** Statement directly references paper claim that zero coefficients give identity; paper ref §4.1

---

### SLICE-OL-09 — ΔP and ΔC definitions and translation lemmas ✅ DONE (Stop 4 complete)

**Layer:** C + E  
**Goal:** Define the ΔP and ΔC offset operations; prove translation properties  
**Inputs:** `SensorPoint`, `ProjectionParameters`, §1.5, §2 Eqs(4,5), §3 Eqs(10,12,13)  
**Outputs:** `applyDeltaP`, `applyDeltaC`, translation lemmas  
**Theorem targets:**
- `deltaP_characterisation : ϵ_u = ϵ'_u + ΔP` (Eq 12, with AMB-OL-002 assumption documented)
- `deltaC_characterisation : ϵ_d = ϵ'_d + ΔP` (Eq 13)
- `distortion_center_translation_commutes`

**Blockers:** AMB-OL-002 — must use Eq (13) sign, not inline text. State explicitly.  
**Proof difficulty:** Low (algebraic, no real analysis)  
**Expected tactics:** `ring`, `simp [applyDeltaP]`  
**Stop condition:** Theorems proved; AMB-OL-002 documented in proof capsule  
**Acceptance criteria:** Proof capsule explicitly states which paper location is authoritative for the sign

---

### SLICE-OL-10 — Projection matrix characterisation (Eq 3, 4) ✅ DONE

**Layer:** C  
**Goal:** Define projection from camera frame to image; define undistort equation (Eq 4)  
**Inputs:** SLICE-OL-07, SLICE-OL-09, Eqs (3), (4)  
**Outputs:** `projectionMatrixCharacterisation`, `undistortProjection`  
**Theorem targets:** `projection_matrix_undistort_eq` (consistency of Eq 3 with Eq 4)  
**Blockers:** AMB-OL-003 (Eq 8 ambiguity — this slice is Eq 4 only, no overscan)  
**Proof difficulty:** Medium  
**Expected tactics:** `ring`, `simp [projectionMatrixCharacterisation]`, `field_simp [hF]`  
**Stop condition:** Eq (4) stated as a theorem; Eq (3) as a definition  
**Acceptance criteria:** F>0 precondition explicit; denominator nonzero carried from SLICE-OL-05

---

### SLICE-OL-11 — FOV characterisation (Eqs 9, 10) ✅ DONE

**Layer:** C  
**Goal:** Define FOV characterisation; relate to projection matrix characterisation via Eqs (12, 13)  
**Inputs:** SLICE-OL-09, SLICE-OL-10, Eqs (9), (10), (12), (13)  
**Outputs:** `fovCharacterisation`, `fovUndistort`  
**Theorem targets:**
- `fov_projection_translation : ϵ_u = ϵ'_u + ΔP` (from definitions, not new axiom)
- `fov_undistort_eq` (consistency of Eq 10 with Eq 4 via translation)

**Blockers:** AMB-OL-002 (sign of ϵ'_d) — document assumption  
**Proof difficulty:** Medium  
**Expected tactics:** `ring`, `simp`, substitution  
**Stop condition:** Both characterisations defined; translation theorems proved  
**Acceptance criteria:** AMB-OL-002 documented; translation relationship proved algebraically, not axiomatically

---

### SLICE-OL-12 — Angle-of-view / FOV equivalence (Eq 6, 14) ✅ DONE

**Layer:** C + E  
**Goal:** State Eq (6) tan formula; define FOV angle from sensor width (Eq 14)  
**Inputs:** SLICE-OL-10, SLICE-OL-11, Eqs (6), (14)  
**Outputs:** `angleOfView`, `fovAngle`  
**Theorem targets:** `angle_of_view_eq : r_u / F = tan(α/2)` (with appropriate hypotheses)  
**Blockers:** Requires `Real.tan` from Mathlib  
**Proof difficulty:** Medium (real analysis)  
**Expected tactics:** `simp [Real.tan_eq_sin_div_cos]`, Mathlib trig lemmas  
**Stop condition:** Definition compiles; equation stated with F>0 precondition  
**Acceptance criteria:** No `sorry`; preconditions match paper (centred at ΔP per §2 Eq 6)

---

### SLICE-OL-13 — Pixel/shader coordinate conversion ✅ DONE (Stop 4 complete)

**Layer:** E  
**Goal:** Define image-to-shader coordinate conversion (Eq 18); prove roundtrip  
**Inputs:** SLICE-OL-04, Eq (18)  
**Outputs:** `toShaderCoords`, `fromShaderCoords`, `pixel_metric_roundtrip`  
**Theorem targets:**
- `pixel_metric_roundtrip : fromShaderCoords (toShaderCoords p) = p`
- `image_texture_coordinate_roundtrip`

**Blockers:** w>0, h>0, wshader>0 as preconditions  
**Proof difficulty:** Low  
**Expected tactics:** `ring`, `field_simp [hw, hh]`  
**Stop condition:** Roundtrip proved  
**Acceptance criteria:** Units documented: mm → normalised shader coordinates; inverse requires w,h,wshader > 0  
**Result:** `lake build ShaderCoords` ✅ clean. `pixel_metric_roundtrip`: `field_simp` alone closes. `image_texture_coordinate_roundtrip`: `field_simp <;> ring`. Lean `ring` redundancy in first theorem caught and removed.

---

### SLICE-OL-14 — Executable semantic oracle ✅ DONE (Stop 4 complete)

**Layer:** F  
**Goal:** Float-based executable counterparts for undistort and projection; oracle output  
**Inputs:** Slices OL-07 through OL-11 (exact definitions)  
**Outputs:** `ExecutableSemanticOracle.lean` — 10 Float definitions  
**Theorem targets:** None (testing only)  
**Blockers:** Must clearly label as Float approximation, not proved exact semantics  
**Proof difficulty:** N/A  
**Expected tactics:** N/A  
**Stop condition:** Oracle runs against test fixtures; output format compatible with battery-tester  
**Acceptance criteria:** Executable boundary documented; no exact-semantic theorems claimed for Float output  
**Result:** `lake build ExecutableSemanticOracle` ✅ clean. All 4 `#eval` outputs manually verified. Structure grouped-field syntax bug caught and fixed (Lean 4 requires one field per line in `structure where`).

---

### SLICE-OL-15 — Differential semantic testing ✅ DONE (Stop 4 complete)

**Layer:** F  
**Goal:** Compare oracle output against Mo-Sys C++ and CamDKit for canonical fixtures  
**Inputs:** SLICE-OL-14, battery-tester harness  
**Outputs:** `battery-tester/semantic_oracle/` — Python reference oracle, 7 fixtures, comparison runner  
**Theorem targets:** None (testing only)  
**Blockers:** External undistort math not available in `opentrackio-cpp` or `ris-osvp-metadata-camdkit` — descoped to Python reference oracle  
**Proof difficulty:** N/A  
**Stop condition:** Fixtures pass within tolerance; domain failures classified separately  
**Acceptance criteria:** Mismatch cases documented; singularity/invalid-domain test cases included  
**Result:** `python3 run.py` → 7/7 PASS. Python 3.9 union-type annotation bug caught and fixed. External blocker documented in capsule and review.

---

### SLICE-OL-DEFER-01 — Projection/FOV equivalence under overscan

**Layer:** E  
**Goal:** Prove that projection and FOV characterisations generate equivalent renders under overscan  
**Blockers:** AMB-OL-003, AMB-OL-008, AMB-OL-009 — all unresolved  
**Proof difficulty:** High  
**Status:** DEFERRED — do not open until ambiguities resolved

---

### SLICE-OL-DEFER-02 — Overscan containment theorem

**Layer:** E  
**Goal:** Prove that the overscanned virtual camera contains all undistorted pixels (Eqs 21–24)  
**Blockers:** Based on informative appendix (AMB-OL-012); requires real analysis (maximum over a set of points)  
**Proof difficulty:** High  
**Status:** DEFERRED

---

### SLICE-OL-DEFER-03 — Global invertibility of U

**Layer:** E/D  
**Goal:** U is injective on some bounded domain  
**Blockers:** AMB-OL-010; requires monotonicity or contraction argument  
**Proof difficulty:** High  
**Status:** DEFERRED

---

## 8. Theorem Inventory

| Theorem | Informal Statement | Lean Shape | Paper Ref | Assumptions | Difficulty | Tactics | Real Analysis? | Test First? |
|---------|-------------------|------------|-----------|-------------|------------|---------|---------------|-------------|
| `semanticExtraction_sound` | Successful extraction yields valid semantics | `extract l = ok s → ValidLensSemantics s` | §1.3 | None | Low | cases, simp | No | Yes |
| `radial_zero_coefficients_identity` | Zero k coefficients → R = 1 | `allZero k → radialTerm k r h = 1` | §4.1 Eq(17) | denominatorNonzero | Low | ring, norm_num | No | No |
| `tangential_zero_coefficients_identity` | Zero p coefficients → tangential terms vanish | `p=0 → undistortX k 0 ϵ = R·ϵ_x` | §4.1 Eq(16) | denominatorNonzero | Low | ring | No | No |
| `brown_conrady_zero_identity` | All-zero coefficients → U(ϵ) = ϵ | `allZero k p → undistortPoint k p ϵ h = ϵ` | §4.1 | denominatorNonzero | Low | simp, ring | No | No |
| `sensorRadius_nonneg` | Screen radius is nonneg | `∀ ϵ, sensorRadius ϵ ≥ 0` | §1.1 | None | Low | positivity | No | No |
| `radial_denominator_nonzero_under_constraints` | Under validity predicate, denominator ≠ 0 | `ValidDistortionCoeffs k → ∀ r ∈ domain, denom k r ≠ 0` | §4.1 Eq(17) | ValidDistortionCoeffs | Medium | linarith, nlinarith | No | Yes |
| `pixel_metric_roundtrip` | mm → shader → mm roundtrip | `fromShader (toShader p) = p` | §4.2 Eq(18) | w,h,wshader > 0 | Low | field_simp | **Yes** | No |
| `deltaP_characterisation` | ϵ_u and ϵ'_u differ by ΔP | `projMatChar.ϵ_u = fovChar.ϵ_u + ΔP` | §3 Eqs(12,13) | AMB-OL-002 assumption | Low | ring | No | No |
| `distortion_center_translation_commutes` | Shifting ΔC commutes with U application | Statement TBD | §1.5 | denominatorNonzero | Medium | ring | No | No |
| `projection_matrix_undistort_eq` | Eq (4) is internally consistent | `U(ϵ_d − ΔC − ΔP) + ΔC + ΔP = ϵ_u` | §2 Eq(4) | denominatorNonzero | Medium | simp, ring | No | No |
| `fov_undistort_eq` | Eq (10) is consistent with Eq (4) via translation | see §3 | §3 Eq(10) | AMB-OL-002 | Medium | ring | No | No |
| `angle_of_view_eq` | r_u/F = tan(α/2) | `Real.tan (angleOfView F r_u / 2) = r_u / F` | §2 Eq(6) | F>0 (junk-value semantics; callers enforce) | Medium | simp [Real.tan_arctan] | **Yes** | No |
| `image_texture_coordinate_roundtrip` | shader → mm → shader roundtrip | `toShader (fromShader q) = q` | §4.2 Eq(18) | w,h,wshader > 0 | Low | field_simp, ring | **Yes** | No |
| `decode_to_semantic_validity` | Parser decode + semantic bridge → valid semantics | `decode json = ok l → extract l = ok s → ValidLensSemantics s` | §1.3 + bridge | None | Medium | cases, simp | No | Yes |
| `projection_fov_equiv` | Projection and FOV forms agree modulo ΔP | TBD | §3 Eqs(12,13) | AMB-OL-002, AMB-OL-008 | High | TBD | No | Yes |
| `radial_denominator_nonzero_zero_k` | All-zero k → denominator = 1 ≠ 0 | `allZero k → denom k r = 1` | §4.1 | None | Low | norm_num, ring | No | No |
| `deltaP_preserves_distortion` | Adding ΔP to undistorted coord matches shifted model | TBD | §1.5 | AMB-OL-002 | Medium | ring | No | No |
| `deltaC_preserves_distortion` | Shifting ΔC consistently applies throughout U | TBD | §1.5 | denominatorNonzero | Medium | ring | No | No |

**Deferred theorems (do not open in first campaign):**
- `overscan_contains_distorted_image` — informative appendix, real analysis
- `undistorted_roundtrip_preserves_pixel` — requires U invertibility (AMB-OL-010)
- `deltaP_preserves_projection_under_reparameterization` — blocked by AMB-OL-003
- Global monotonicity, continuity, compactness arguments

---

## 9. Proof-Risk Matrix

### Low Risk

| Item | Why easy |
|------|----------|
| `sensorRadius_nonneg` | `positivity` closes it; Pythagorean structure |
| `radial_zero_coefficients_identity` | Pure polynomial; `ring` or `norm_num` after `simp` |
| `tangential_zero_coefficients_identity` | Pure polynomial; `ring` |
| `brown_conrady_zero_identity` | Composition of previous two; `simp` + `ring` |
| `pixel_metric_roundtrip` | Linear algebra; `field_simp` + `ring` with w,h,wshader > 0 |
| `deltaP_characterisation` | Algebraic definition; `ring` |
| `semanticExtraction_sound` | Structural; follows from extraction definition |
| `radial_denominator_nonzero_zero_k` | `norm_num` directly |

### Medium Risk

| Item | Why medium | What assumptions help |
|------|------------|----------------------|
| `radial_denominator_nonzero_under_constraints` | Polynomial nonzero over a domain; needs explicit domain restriction | Bounded domain hypothesis; specific sign constraints on k |
| `projection_matrix_undistort_eq` | Composition of definitions; needs F>0 and denominator safety tracked | ValidLensSemantics carries these |
| `distortion_center_translation_commutes` | Translation and polynomial composition; needs careful bookkeeping | Clean ΔC-shifted coordinate type |
| `angle_of_view_eq` | Requires Mathlib `Real.tan`; connection between r_u and α needs care | Restrict to α ∈ (0, π) |
| `fov_undistort_eq` | Depends on AMB-OL-002 resolution | Use Eq (13) sign as assumption |
| `projection_fov_equiv` | Translation composition; assumption-gated on AMB-OL-008 | Explicit preconditions from paper analysis |

### High Risk — separate analysis required

| Item | Why hard | What would make tractable | Worth formalising now? |
|------|----------|--------------------------|----------------------|
| `overscan_contains_distorted_image` | Based on informative appendix; requires supremum over a set of undistorted points; needs compactness or finite-domain argument | Finite discrete approximation; replace continuous max with finite max | No — defer |
| `undistorted_roundtrip_preserves_pixel` | Requires U invertibility; paper says U⁻¹ is numerical (AMB-OL-010); global injectivity of the Brown-Conrady map is not obvious | Strict local injectivity via Jacobian positivity; restrict to small r | Not yet — needs AMB-OL-010 resolved |
| Global invertibility of U | Brown-Conrady is not globally invertible for all k values; only for "mild" distortion | Explicit coefficient range hypothesis; contraction mapping argument | Not in first campaign |
| Continuity / monotonicity of U | Needs `ContinuousOn` machinery; rational polynomial is continuous on denominator-safe domain | Mathlib `Polynomial.continuous_eval` | Not in first campaign |
| FOV/projection equivalence with overscan | AMB-OL-003, AMB-OL-009, AMB-OL-008 all unresolved | Resolve ambiguities first; then algebraic | Not until ambiguities resolved |
| Aperture circle-of-confusion bound | Paper says under investigation; formula validity unknown | Normative confirmation | No |
| Floating-point error bounds | Requires IEEE 754 reasoning and error propagation analysis | Not a Lean 4 strength currently | No |
| Full rendering equivalence across renderers | Out of scope for formal methods | N/A | No |

---

## 10. Differential Testing Strategy

### Separation from proof strategy

Proofs are over **exact mathematical semantics** (ℚ and ℝ, no rounding).
Production implementations use **floating point**.
These are different. The differential testing strategy bridges them.

### Pure functional reference model in Lean

- Define Float-valued counterparts in `ExecutableSemanticOracle.lean`
- Map exact `ℚ` coefficients to `Float`
- Run `undistortPoint_float` for test inputs
- Output JSON compatible with battery-tester format
- Clearly label file: "executable Float approximation — not a proved theorem"

### Comparison targets

1. **Mo-Sys OpenTrackIO C++** — primary reference; compare undistort output point-by-point
2. **CamDKit Python** — secondary reference; compare for canonical fixtures
3. **CamDKit C++** — secondary reference
4. **Future Rust/Python implementations** — add as they become available

### Property-test generation from theorem preconditions

For each proved theorem with explicit preconditions:
- Generate test cases from precondition domain
- Include boundary cases (r=0, ϵ_x=0, ϵ_y=0)
- Include all-zero coefficient cases (should give ϵ_u ≈ ϵ_d)
- Include denominator-safe regions (k coefficients within ValidDistortionCoeffs)
- Include near-singularity cases for the denominator

### Generated coefficient domains

- All-zero coefficients: identity case
- Small radial: |kᵢ| < 0.01 for each i
- Typical VFX: k₁ ∈ [−0.5, 0.5], others small
- Denominator-zero boundary: k₂ set to create near-zero denominator at specific r

### Singularity/invalid-domain test cases

- Denominator = 0 at specific r: must be classified as domain failure, not a wrong answer
- Very large r: large distortion; may cause implementation divergence
- ϵ_x = 0 or ϵ_y = 0: diagonal form singularity; component form must still work
- ΔC = ΔP = 0: degenerate but valid

### Tolerance policy

- Normal cases: tolerance ≤ 1e-6 mm (sub-pixel at typical sensor resolutions)
- Large distortion cases: tolerance ≤ 1e-4 mm
- Domain failures: categorise separately; do not treat as failures needing tolerance

### Oracle output format

Extend `battery-tester` JSON output with `semantic_oracle` key:
```json
{
  "input": { "lens": {...}, "point": [ex, ey] },
  "undistorted": [ux, uy],
  "radial_r": r_val,
  "radial_R": R_val,
  "domain_valid": true
}
```

### Parser vs semantic testing

Parser differential testing (existing): verifies JSON decode/encode roundtrip
Semantic differential testing (new): verifies numeric evaluation of distortion model
These are related but **separate**. Do not conflate.

---

## 11. Executable Reference Model Strategy

### Which definitions should be computable

- `radialTerm_float : RadialCoefficients → Float → Float`
- `undistortX_float undistortY_float`
- `undistortPoint_float`
- `shaderToSensor_float sensorToShader_float`
- `projectionMatrixCharacterisation_float`

### Which proofs are noncomputable

- All theorems using `ℝ` (require `Classical.choice` for division; noncomputable)
- `radialTerm` over `ℝ` is noncomputable unless restricted to `ℚ`
- Consider defining polynomial over `ℚ` for computable version; convert to `ℝ` for analysis

### Parallel Float approximations

Maintain two files:
- `DistortionModel.lean` — exact semantic definitions over `ℚ`/`ℝ`; noncomputable; proved
- `ExecutableSemanticOracle.lean` — Float approximations; `#eval`-able; not proved

Never claim Float output is proved unless a formal bridge theorem exists.

### Exposure to battery-tester

Create `OpenLensIOSemanticHarness.lean` parallel to `HarnessAdapter.lean`:
- Reads JSON input (lens parameters + test points)
- Evaluates `undistortPoint_float`
- Writes JSON output
- References which proved theorems the definitions are based on

---

## 12. LAPS Proof-Flow Gates

### Gate 0 — Source extraction complete
**Required artifacts:** Spec extraction table (Section 2 above)  
**Pass criteria:** All normative equations extracted with paper references; ambiguities registered  
**Stop condition:** Any unextracted equation used in a theorem  
**Status:** COMPLETE (this document)

---

### Gate 1 — Existing-proof boundary review
**Required artifacts:** Explicit list of what `opencv_opentrackio_proofs` and `opentrackio_parser` already cover; statement that no new slice duplicates those proofs  
**Pass criteria:**
- SLICE-OL-03 does not re-prove JSON key name correctness
- SLICE-OL-05 does not re-prove OpenCV↔OTio distortion coefficient conversion
- SLICE-OL-13 does not re-prove pixel-coordinate preservation from `PixelEquivalence.lean`
- Actual field names and types in `LensModel.lean`, `SampleModel.lean`, `CameraModel.lean`, `TransformModel.lean`, `RationalValueWrappers.lean` are read directly from source before SLICE-OL-01 types are designed — no type names or field names assumed from memory
- Actual theorem names in `opencv_opentrackio_proofs/DistortionConversion.lean`, `PixelEquivalence.lean`, and `PrincipalPointConversion.lean` are listed before any semantic theorem is named — to avoid duplicating a theorem that already exists under a different name  
**Stop condition:** SLICE-OL-01 opened before this audit is complete  
**Status:** PENDING — requires explicit review against `opencv_opentrackio_proofs/PixelEquivalence.lean` and `DistortionConversion.lean`

---

### Gate 2 — Ambiguities triaged
**Required artifacts:** `ambiguity-register.md` with all HIGH-impact ambiguities resolved or explicitly assumption-gated  
**Pass criteria:** AMB-OL-002, AMB-OL-003, AMB-OL-007, AMB-OL-010 each have a documented handling decision  
**Stop condition:** Any proof slice opens while depending on an unresolved HIGH-impact ambiguity  
**Status:** PENDING — AMB-OL-002 handled by assumption; AMB-OL-003, AMB-OL-007, AMB-OL-010 assumption-gated but not fully resolved

---

### Gate 3 — Representation review
**Required artifacts:** Lean representation choices documented (Section 5 above); approved types before first `def`  
**Pass criteria:** Phantom coordinate types chosen; exact vs Float separation documented; non-singular component form chosen for U  
**Stop condition:** Implementation before this review  
**Status:** PENDING — requires explicit approval of Section 5 choices

---

### Gate 4 — Domain-safety review
**Required artifacts:** `ValidLensSemantics` predicate defined; denominator nonzero condition in predicate; denominator safety lemma in SLICE-OL-05  
**Pass criteria:** No equivalence theorem opens until SLICE-OL-05 is complete and AMB-OL-007 is assumption-gated  
**Stop condition:** `projection_fov_equiv` or any undistort theorem opened without domain-safety lemmas  
**Status:** PENDING

---

### Gate 5 — Algebraic lemma review
**Required artifacts:** All identity lemmas (SLICE-OL-06, SLICE-OL-08) and translation lemmas (SLICE-OL-09) complete  
**Pass criteria:** Zero-distortion identity proved; ΔP/ΔC translation theorems proved  
**Stop condition:** `projection_matrix_undistort_eq` or `fov_undistort_eq` opened without identity lemmas  
**Status:** PENDING

---

### Gate 6 — Executable model review
**Required artifacts:** `ExecutableSemanticOracle.lean` boundary documented; exact vs Float separation explicit  
**Pass criteria:** No exact-semantic theorem claimed for Float output; oracle runs against at least 3 test fixtures  
**Stop condition:** Float output presented as a proof  
**Status:** PENDING

---

### Gate 7 — High-risk analysis review
**Required artifacts:** Explicit written analysis for each high-risk item; approval before opening  
**Pass criteria:** `overscan_contains_distorted_image`, global invertibility, and continuity theorems reviewed and either deferred or explicitly approved  
**Stop condition:** Any high-risk theorem opened without written analysis  
**Status:** PENDING — all high-risk items currently deferred

---

## 13. Suggested Implementation Order

1. **Gate 0: Spec extraction** — this document (complete)
2. **Gate 1: Existing-proof boundary audit** — read actual field names and types from `LensModel.lean`, `SampleModel.lean`, `CameraModel.lean`, `RationalValueWrappers.lean`; list actual theorem names from `DistortionConversion.lean`, `PixelEquivalence.lean`, `PrincipalPointConversion.lean`; confirm no duplication before SLICE-OL-01
3. **SLICE-OL-00**: Project skeleton
4. **Gate 2: Ambiguity triage** — document AMB-OL-007 handling; confirm AMB-OL-002 sign
5. **Gate 3: Representation review** — approve types in Section 5
6. **SLICE-OL-01**: Semantic bridge types
7. **SLICE-OL-02**: Semantic extraction function
8. **SLICE-OL-03**: Semantic extraction soundness
9. **SLICE-OL-04**: Coordinate space types
10. **Gate 4: Domain-safety review**
11. **SLICE-OL-05**: Radial polynomial + denominator safety
12. **SLICE-OL-06**: Zero-coefficient radial identity
13. **SLICE-OL-07**: U(ϵ) component form definition
14. **SLICE-OL-08**: Zero-distortion identity
15. **Gate 5: Algebraic lemma review**
16. **SLICE-OL-09**: ΔP/ΔC translation lemmas
17. **SLICE-OL-10**: Projection matrix characterisation
18. **SLICE-OL-11**: FOV characterisation
19. **SLICE-OL-12**: Angle-of-view / FOV equation
20. **SLICE-OL-13**: Pixel/shader coordinate roundtrip ✅
21. **Gate 6: Executable model review** ✅
22. **SLICE-OL-14**: Executable semantic oracle ✅
23. **SLICE-OL-15**: Differential semantic testing ✅ (descoped — see OL-15 review)
24. **Gate 7: High-risk analysis review** — DEFERRED

---

## 14. Defer-for-Now List

| Item | Reason | Prerequisite | What would unblock |
|------|--------|--------------|-------------------|
| `overscan_contains_distorted_image` | Informative appendix (AMB-OL-012); requires real analysis (sup over point set); paper gives approximate algorithm, not a tight specification | All identity and projection lemmas | Normative clarification from paper authors; or an explicit formal domain restriction |
| Global invertibility of U | Not stated in paper; requires strict local injectivity or contraction argument | SLICE-OL-07 | Resolution of AMB-OL-010; coefficient-range hypotheses that force injectivity |
| `undistorted_roundtrip_preserves_pixel` | Requires U invertibility (blocked) | Global invertibility | AMB-OL-010 resolved |
| `projection_fov_equiv` under overscan | AMB-OL-003, AMB-OL-008, AMB-OL-009 all unresolved | Unambiguous overscan equations | Paper clarification or reference implementation confirmation |
| Continuity / monotonicity of U | Not required for current proof campaign; needs `ContinuousOn` machinery | SLICE-OL-07 | Decision to add real-analysis goals to scope |
| Aperture model (Eq 19) | Paper explicitly says "under investigation" | N/A | Paper update with normative status |
| Vignetting model (Eq 20) | No formal properties stated; future work per paper §B.4 | N/A | Normative specification with property claims |
| Anamorphic distortion (§B.2) | Explicitly marked as future work | N/A | Future paper version |
| Chromatic aberration (§B.3) | Explicitly marked as future work | N/A | Future paper version |
| Entrance pupil off-axis offset (§B.1) | Explicitly marked as future work | N/A | Future paper version |
| Floating-point error bounds | Requires IEEE 754 reasoning; not Lean 4's strength | SLICE-OL-14 | Lean 4 IEEE 754 support or separate tool |
| Full rendering equivalence across renderers | Out of scope for formal methods | N/A | Not a proof target |
| Production C++ implementation correctness | Out of scope; would require extracting C++ semantics | N/A | Not a proof target |

---

## 15. Final Checklist

- [x] PDF was read (full text extracted via `pdftotext`)
- [x] Paper references used for all equation-dependent claims (section, equation number cited)
- [x] No unsupported equations invented (no Brown-Conrady knowledge assumed beyond what the paper states)
- [x] Existing parser proofs not duplicated (Layer A boundary explicit; parser types imported, not re-proved)
- [x] Existing OpenCV↔OpenTrackIO conversion proofs not duplicated (noted in §3 boundary; Gate 1 check required)
- [x] New `openlensio_semantics` boundary defined (§3 + dependency graph)
- [x] Ambiguities listed (15 entries in ambiguity-register.md; HIGH-impact ones flagged)
- [x] High-risk proofs separated (§9 risk matrix + §14 defer list)
- [x] LAPS stop gates defined (7 gates in §12 with required artifacts and pass criteria)
- [x] Executable/differential strategy separated from proof strategy (§10 + §11)
