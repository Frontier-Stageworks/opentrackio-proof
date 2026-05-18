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

def encodePtpInfo (p : PtpInfo) : JsonValue :=
  .object ([("profile",          .string p.profile.toStr),
            ("domain",           .number p.domain),
            ("leaderIdentity",   .string p.leaderIdentity.val),
            ("leaderPriorities", encodeLeaderPriorities p.leaderPriorities),
            ("leaderAccuracy",   .number p.leaderAccuracy),
            ("meanPathDelay",    .number p.meanPathDelay)] ++
           (p.leaderTimeSource.map fun s => ("leaderTimeSource", .string s.toStr)).toList ++
           (p.vlan.map           fun s => ("vlan",              .number s)).toList)

theorem encodePtpInfo_roundtrip (p : PtpInfo) :
    decodePtpInfo (encodePtpInfo p) = .ok p := by
  obtain ⟨prof, dom, lid, lpri, lacc, mpd, lts, vl⟩ := p
  obtain ⟨lidv, lidh⟩ := lid
  rcases lts with _ | lts
  · cases vl <;> cases prof <;>
    simp [encodePtpInfo, decodePtpInfo, JsonValue.lookup?,
          PtpProfile.toStr, encodeLeaderPriorities, decodeLeaderPriorities, lidh] <;> rfl
  · cases lts <;> cases vl <;> cases prof <;>
    simp [encodePtpInfo, decodePtpInfo, JsonValue.lookup?,
          PtpProfile.toStr, PtpLeaderSource.toStr,
          decodePtpProfile, decodePtpLeaderSource,
          encodeLeaderPriorities, decodeLeaderPriorities, lidh] <;> rfl
