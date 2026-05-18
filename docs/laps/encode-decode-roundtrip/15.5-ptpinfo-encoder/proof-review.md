# Proof Review — ptpinfo-encoder (Slice 15.5)

## Acceptance criteria

| Criterion | Result |
|---|---|
| `lake env lean opentrackio_parser/PtpInfoEncoder.lean` — exit 0, no warnings | PASS |
| `lake build PtpInfoEncoder` — exit 0 | PASS |
| No `sorry` or forbidden constructs | PASS |
| Roundtrip theorem green | PASS |

## Review

**Encoder**: `encodePtpInfo` emits six required fields as a list literal plus two optional
fields via `.map ... |>.toList`. `profile` encoded as `.string p.profile.toStr`;
`leaderIdentity` encoded as `.string p.leaderIdentity.val`; `leaderPriorities` via
`encodeLeaderPriorities`; numeric fields (`domain`, `leaderAccuracy`, `meanPathDelay`) as
`.number`; optional `leaderTimeSource` as `.string s.toStr`; optional `vlan` as `.number`.

**Key deviation — `try` with `<;>` parses incorrectly**: First attempt used
`rcases lts with _ | lts <;> try cases lts <;> cases vl`. In Lean 4, `try` consumes
the rest of the `<;>` chain (`try (cases lts <;> cases vl)`), so in the `none` branch
`try` catches the `cases lts` failure and silently skips `cases vl` — leaving `vl` and
`prof` abstract and the `simp` unable to close the goal.

**Fix**: Split `lts` branches explicitly with `·` bullets. The `none` branch needs only
`cases vl <;> cases prof` and `simp` without `PtpLeaderSource.toStr`/`decodePtpLeaderSource`.
The `some lts` branch adds `cases lts` before `cases vl <;> cases prof` and includes the
`PtpLeaderSource` simp lemmas.

**Pattern recorded**: `try t <;> t2` is dangerous — `try` may silently consume `<;> t2`.
Use `·` bullet sub-proofs when one branch needs `cases` on a value the other branch lacks.

**Proof**:
```lean
  rcases lts with _ | lts
  · cases vl <;> cases prof <;>
    simp [encodePtpInfo, decodePtpInfo, JsonValue.lookup?,
          PtpProfile.toStr, encodeLeaderPriorities, decodeLeaderPriorities, lidh] <;> rfl
  · cases lts <;> cases vl <;> cases prof <;>
    simp [encodePtpInfo, decodePtpInfo, JsonValue.lookup?,
          PtpProfile.toStr, PtpLeaderSource.toStr,
          decodePtpProfile, decodePtpLeaderSource,
          encodeLeaderPriorities, decodeLeaderPriorities, lidh] <;> rfl
```

## Verdict

ACCEPTED. One new pattern established: use `·` bullets instead of `try t <;>` when
branches require different case splits.
