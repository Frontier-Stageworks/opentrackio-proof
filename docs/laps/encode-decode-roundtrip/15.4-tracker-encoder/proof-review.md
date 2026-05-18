# Proof Review — tracker-encoder (Slice 15.4)

## Acceptance criteria

| Criterion | Result |
|---|---|
| `lake env lean opentrackio_parser/TrackerEncoder.lean` — exit 0, no warnings | PASS |
| `lake build TrackerEncoder` — exit 0 | PASS |
| No `sorry` or forbidden constructs | PASS |
| Both roundtrip theorems green | PASS |

## Review

**Encoders**: `encodeStaticTracker` and `encodeTracker` use `Option.map ... |>.toList`
to omit absent fields. `NonemptyString` fields encoded as `.string ns.val`.

**Key deviation — private `decodeOptionalString`**: `simp` cannot unfold a `private`
definition from another module. Fix: define a local `private def decodeOptStr` with the
same body. Since both have identical bodies, `decodeStaticTracker_unfold : ... := rfl`
and `decodeTracker_unfold : ... := rfl` hold by definitional equality. `rw [... _unfold]`
rewrites the goal to use `decodeOptStr`, which `simp` can then unfold.

**Pattern recorded**: any future encoder roundtrip proof for a decoder that uses a
`private` helper must re-expose that helper locally and rewrite via a `rfl` equation.

**Proof**: `rcases ns with _ | ⟨v, h⟩` exposes `h : v ≠ ""`. `simp [decodeOptStr, *, ...]`
uses `*` to discharge the `dite` condition — `dif_pos` is redundant and was removed.
`<;> rfl` closes residual `Except.bind` chains.

## Verdict

ACCEPTED. One new pattern established for private-helper decoders.
