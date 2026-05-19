# Proof Review — timing-enum-decoders (Slice 7)

## Kernel status

`lake env lean opentrackio_parser/TimingEnumDecoders.lean` — exit 0, no warnings.  
`lake build TimingEnumDecoders` — exit 0 (3.2s, 3288 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No non-timing enum types (no coordinate system, projection, or distortion model).
- No changes to Slices 1–6.

## Statement audit

| Name | Intended | Captured |
|---|---|---|
| `TimingMode` / `SyncSource` / `PtpProfile` / `PtpLeaderSource` | inductive enum types | Yes |
| `X.toStr` | maps each variant to its normative string | Yes |
| `decodeX` | exact string match → `.ok variant`; unknown string → `invalidEnum`; non-string → `expectedString` | Yes |
| `decodeX_sound` | `decodeX j = .ok x → j = .string x.toStr` | Yes |

## Semantic review

**Decoder correctness:** Each decoder accepts only the exact normative strings from
A5. No aliases, no case folding. Unknown strings produce `invalidEnum context s`
(not silently ignored), non-string inputs produce `expectedString`.

**Soundness statement:** `j = .string x.toStr` is non-vacuous — it asserts that
the decoder only accepts the exact normative encoding of the variant it returns.
This is strictly stronger than `True` and captures the exact-match semantics.

**Proof shape:** `cases m` enumerates the output variant first, then
`simp only [X.toStr]` reduces the goal to `j = .string "literal"`, then
`simp only [decodeX] at h; split at h` enumerates the input branches.
For the matching branch, `simp_all` closes by `rfl` after `j` is substituted.
For non-matching branches, `simp_all` closes by contradiction from `h`.

**Why `cases m` first:** An earlier attempt used `split at h` alone, which
produced `h : Constructor = variable` in the `.ok` branches. `simp_all` could
not orient that equality for substitution. `cases m` first eliminates `m`
to a concrete constructor, so `split at h` produces only contradictions or
`h : .ok C = .ok C` (trivially closed), with no orientation problem.

## Hard step identification

No hard step. The proof is mechanical case analysis. The `cases m` → `split at h`
ordering is the key structural decision.

## Anti-pattern scan

- No bare `simp` (only `simp only [X.toStr]` and `simp_all`).
- No `omega`, `norm_num`, or arithmetic solvers.
- No global annotations added.
- `simp_all` is appropriate here: it closes both the trivial `rfl` goals and the
  contradiction goals uniformly, and both uses are inspectable from the proof shape.

## Contract compliance

1. ✅ All four enum types and `toStr` functions compile.
2. ✅ All four decoders compile.
3. ✅ All four soundness theorems compile without `sorry`.
4. ✅ `lake env lean` exit 0, no warnings.
5. ✅ `lake build TimingEnumDecoders` exit 0.
6. ✅ No non-timing enums or excluded scope introduced.
