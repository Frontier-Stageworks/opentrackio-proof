# Proof Review — sample-encoder (Slice 15.11)

## Acceptance checks

| Check | Result |
|---|---|
| `lake build SampleEncoder` | exit 0, no warnings, 229s |
| `encodeSample_roundtrip` public, no `sorry` | ✓ |
| All helpers private, no `sorry` | ✓ |

## Deviations from plan

One deviation, documented in proof-plan.md:

**`encodeRelatedIds_rt` composed-mapM form:** The capsule predicted the lemma would be
stated as `(rs.map JsonValue.string).mapM decodeRelId' = .ok rs`. Simp applied
`List.mapM_map` (Mathlib) to fuse the map and mapM into a single mapM with composed
function, making the original form unmatchable. The lemma was restated as
`rs.mapM (decodeRelId' ∘ JsonValue.string) = .ok rs` and proved by induction with
`simp only [List.mapM_cons, Function.comp, decodeRelId', ih]; rfl`.

This is a new instance of the pre-expansion trap: Mathlib rewrites a sub-expression
into a form the simp rule no longer matches. The fix is always to match the post-simp
form, not the natural algebraic form.

## Key proof notes

**`decodeSample_unfold` by `rfl`:** Replaces two private helpers (`decodeRelatedId`,
`decodeStaticInfo`) with definitionally equal local copies. The `do`-block body is
transcribed exactly — `rfl` holds because the local copies have identical bodies.

**`encodeStaticInfo` absent from `encodeSample_roundtrip` simp set:** Only
`encodeStaticInfo_rt` is added. If `encodeStaticInfo` were in the simp set, simp would
expand the encoded `static` value before `encodeStaticInfo_rt` could match
`decodeStaticInfo' (encodeStaticInfo si)`. Consistent with the pre-expansion discipline
established in 15.10A and 15.10B.

**`encodeTransformArr_rt` with free `ctx`:** Stated as `∀ ctx ta, decodeNonemptyArray
decodeTransform ctx (.array ...) = .ok ta`. Simp unifies `ctx = "transforms"` when
matching the goal — identical to `encodeDistortionArray_rt` in 15.10B.

**`encodeStaticInfo_rt` at default heartbeats:** 16 goals, no override needed.
Sub-encoder roundtrip lemmas (`encodeCamera_roundtrip`, `encodeStaticLens_roundtrip`,
`encodeStaticTracker_roundtrip`, `encodePositiveRational_roundtrip`) used as simp rules —
cheap rewrite step regardless of the cost to prove them in their home files.

**`encodeSample_roundtrip` at 40M heartbeats:** 2048 goals (2^11). Completed in 229s
total build time.

## Status: COMPLETE
