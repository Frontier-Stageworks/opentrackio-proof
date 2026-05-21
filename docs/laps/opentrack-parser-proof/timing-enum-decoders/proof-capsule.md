# Proof Capsule — timing-enum-decoders (Slice 7)

## Parent

Slice 7 of `opentrack-parser-verification`.

## Task classification

**Small** — four inductive types, four `toStr` functions, four decoders, four
soundness theorems. Proof structure is identical for all four.

## Intent

Define the four closed-enum types from the OpenTrackIO timing sub-tree, a
`toStr` function for each (mapping variant back to normative string), a decoder
for each, and a soundness theorem proving that a successfully decoded variant
corresponds exactly to the input string.

## Resolved ambiguities used

- A5: exact normative strings for all four enum fields; no case folding; unknown
  values rejected. Coordinate system, projection type, and `distortion.model`
  are NOT enums and are NOT included here.

## Enums and normative strings (frozen)

```
TimingMode       : "internal" | "external"
SyncSource       : "genlock"  | "videoIn" | "ptp" | "ntp"
PtpProfile       : "IEEE Std 1588-2019" | "IEEE Std 802.1AS-2020" | "SMPTE ST2059-2:2021"
PtpLeaderSource  : "GNSS" | "Atomic clock" | "NTP"
```

## Formal statements (frozen)

For each enum `X` with `toStr : X → String`:

```lean
def decodeX (j : JsonValue) : Except DecodeError X

theorem decodeX_sound (j : JsonValue) (x : X)
    (h : decodeX j = .ok x) : j = .string x.toStr
```

The soundness statement `j = .string x.toStr` is non-vacuous: it asserts that
the decoder only accepts the exact normative string for the variant it returns.
This is strictly stronger than `True` and connects the decoder to the encoding.

## Proof note

Each soundness proof: `unfold decodeX at h; split at h <;> simp_all [X.toStr]`.

`split at h` case-splits the outer `match j` in `h`. For branches where the
decoder returns `.ok x`, the branch hypothesis ties `j` to the exact matched
string; `simp_all` closes by simplifying `j = .string x.toStr` to `rfl`.
For branches where the decoder returns `.error _`, `simp_all` closes by
contradiction (`Except.ok ≠ Except.error`).

## Forbidden

- No `sorry`.
- No non-timing enums (coordinate system, projection, distortion model are not here).
- No changes to Slices 1–6.
