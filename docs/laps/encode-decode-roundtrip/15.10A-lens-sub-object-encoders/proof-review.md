# Proof Review — lens-sub-object-encoders (Slice 15.10A)

## Acceptance checks

| Check | Result |
|---|---|
| `lake build LensSubEncoders` | exit 0, no warnings, 8.2s |
| All 6 roundtrip theorems public, no `sorry` | ✓ |
| Infrastructure lemmas private, no `sorry` | ✓ |
| No `set_option maxHeartbeats` override required | ✓ |

## Deviations from plan

None. File matches the verified proof plan exactly.

## Key proof notes

**`decodeDistortion_unfold` pattern:** `decodeDistortion` calls a private `decodeNumberString`
that simp cannot unfold. A local `decodeNumStr` with identical body is defined; the unfold
theorem `decodeDistortion = fun j => ... decodeNumStr ...` holds by `rfl` (definitional
equality). `rw [decodeDistortion_unfold]` before simp makes the goal transparent.

**`list_mapM_ok` cons residual:** After `simp [List.mapM_cons, hrt hd, ih]` the remaining
goal is a do-bind expansion of `Except.bind (.ok hd) (fun x => .ok (x :: tl))`. This is
definitionally true — `Except.bind_ok` does not exist as a named lemma in Lean 4; closed
by `rfl`.

**`decodeNonemptyArray_roundtrip` final `rfl`:** Covers two things at once — monad laws
(`Except.bind (.ok x) f = f x` is definitional) and proof irrelevance (Lean 4's kernel
treats all proofs of the same `Prop` as definitionally equal, so the reconstructed
`NonemptyArray.mk` proof field unifies with the original).

**`encodeNonemptyStringArray_rt` simp-ordering constraint:** The roundtrip lemma's LHS is
`decodeNonemptyArray decodeNumStr ctx (encodeNonemptyStringArray arr)`. If `encodeNonemptyStringArray`
also appears in the simp set, simp expands it before the lemma can match, making the lemma
unused. The fix: omit `encodeNonemptyStringArray` from the `encodeDistortion_roundtrip` simp
call; include only `encodeNonemptyStringArray_rt`.

**`encodeFizOptions_roundtrip` `none/none/none` case:** The `FizOptions` invariant
`hap : ¬(focus = none ∧ iris = none ∧ zoom = none)` is a false hypothesis when all three
are `none`. `simp_all` closes this goal after the main `simp`.

## Status: COMPLETE
