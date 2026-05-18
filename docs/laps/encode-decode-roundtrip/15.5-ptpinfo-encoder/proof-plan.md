# Proof Plan — ptpinfo-encoder (Slice 15.5)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/PtpInfoEncoder.lean` | `PtpInfoEncoder` |

Appended after `TrackerEncoder` in `lakefile.toml`.

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "PtpInfoEncoder"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  PtpInfoEncoder.lean — Slice 15.5: ptpinfo-encoder

  Encoder for PtpInfo with roundtrip theorem.
  All decoder functions are public — no private-helper re-exposure needed.

  Ref: docs/laps/encode-decode-roundtrip/15.5-ptpinfo-encoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import SampleModel
import TimingEnumDecoders
import LeafDecoders
import LeafEncoders
import PtpInfoDecoder
```

---

## Step 3 — Encoder

```lean
def encodePtpInfo (p : PtpInfo) : JsonValue :=
  .object ([("profile",          .string p.profile.toStr),
            ("domain",           .number p.domain),
            ("leaderIdentity",   .string p.leaderIdentity.val),
            ("leaderPriorities", encodeLeaderPriorities p.leaderPriorities),
            ("leaderAccuracy",   .number p.leaderAccuracy),
            ("meanPathDelay",    .number p.meanPathDelay)] ++
           (p.leaderTimeSource.map fun s => ("leaderTimeSource", .string s.toStr)).toList ++
           (p.vlan.map           fun s => ("vlan",              .number s)).toList)
```

---

## Step 4 — Roundtrip theorem

```lean
theorem encodePtpInfo_roundtrip (p : PtpInfo) :
    decodePtpInfo (encodePtpInfo p) = .ok p := by
  obtain ⟨prof, dom, lid, lpri, lacc, mpd, lts, vl⟩ := p
  obtain ⟨lidv, lidh⟩ := lid
  cases lts <;> cases vl <;> cases prof <;>
  simp [encodePtpInfo, decodePtpInfo, JsonValue.lookup?,
        PtpProfile.toStr, PtpLeaderSource.toStr,
        encodeLeaderPriorities, decodeLeaderPriorities, lidh] <;> rfl
```

### Notes

- `obtain ⟨lidv, lidh⟩ := lid` exposes `lidh : lidv ≠ ""` so `simp` can reduce the `dite` in `decodePtpInfo`.
- `cases prof` is needed because `decodePtpInfo` matches on `j.lookup? "profile"` which produces `.string prof.toStr`, and `decodePtpProfile` pattern-matches on the string literal — `simp [PtpProfile.toStr]` must unfold the concrete string to match.
- `cases lts` and `cases vl` handle the two optional fields.
- `encodeLeaderPriorities_roundtrip` is not invoked directly — `simp [encodeLeaderPriorities, decodeLeaderPriorities, ...]` unfolds both inline.
- `<;> rfl` closes residual `Except.bind` chains.

---

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/PtpInfoEncoder.lean` — exit 0, no warnings.
2. `lake build PtpInfoEncoder` — exit 0.
3. No `sorry` or forbidden constructs.
4. Roundtrip theorem green.
