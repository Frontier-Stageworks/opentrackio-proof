# Proof Review — ptpinfo-decoder (Slice 14.4)

## Acceptance criteria

| Criterion | Result |
|---|---|
| `lake env lean opentrackio_parser/PtpInfoDecoder.lean` — exit 0, no warnings | PASS |
| `lake build PtpInfoDecoder` — exit 0 | PASS |
| No `sorry` or forbidden constructs | PASS |

## Review

**Structure**: `decodePtpInfo` follows the standard `do`-block pattern established in Slices 14.2 and 14.3. Six required fields use `←` with `.error` on `none`; two optional fields use pure `let` (or `←` with `.ok none`).

**Required fields**:
- `profile`: delegated to `decodePtpProfile` (Slice 7 enum decoder)
- `domain`: raw `.number` string
- `leaderIdentity`: `.string s` with `if h : s ≠ "" then .ok ⟨s, h⟩` — same construction as `decodeIdField` in TransformDecoder
- `leaderPriorities`: delegated to `decodeLeaderPriorities` (Slice 14.1)
- `leaderAccuracy`: raw `.number` string
- `meanPathDelay`: raw `.number` string

**Optional fields**:
- `leaderTimeSource`: `←` with `.ok none` / `.map some` — cannot fail silently
- `vlan`: pure `let` — genuinely infallible

**No theorems**: consistent with capsule spec. The only invariant (`leaderIdentity.val ≠ ""`) is in `NonemptyString` and proved at construction.

**Imports**: `LeafDecoders` for `decodeLeaderPriorities`; `TimingEnumDecoders` for `decodePtpProfile` and `decodePtpLeaderSource`; `SampleModel` for `PtpInfo`/`PtpProfile`/`PtpLeaderSource`/`LeaderPriorities`.

## Verdict

ACCEPTED. No issues found.
