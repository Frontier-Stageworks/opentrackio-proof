/-
  TimingEnumDecoders.lean — Slice 7: timing-enum-decoders

  Defines the four closed-enum types from the OpenTrackIO timing sub-tree,
  their normative string encodings, decoders, and soundness theorems.

  A5: exact string values; no case folding; unknown values rejected.
  Enums: timing.mode, timing.synchronization.source,
         timing.synchronization.ptp.profile,
         timing.synchronization.ptp.leaderTimeSource
  Ref: docs/laps/timing-enum-decoders/proof-capsule.md
-/

import Mathlib.Tactic
import DecodeError
import JsonRawModel

/-─────────────────────────────────────────────────────────────────────────────
  TimingMode — timing.mode
─────────────────────────────────────────────────────────────────────────────-/

inductive TimingMode where
  | internal
  | external
  deriving Repr, DecidableEq

def TimingMode.toStr : TimingMode → String
  | .internal => "internal"
  | .external => "external"

def decodeTimingMode (j : JsonValue) : Except DecodeError TimingMode :=
  match j with
  | .string "internal" => .ok .internal
  | .string "external" => .ok .external
  | .string s          => .error (.invalidEnum "timingMode" s)
  | _                  => .error .expectedString

theorem decodeTimingMode_sound (j : JsonValue) (m : TimingMode)
    (h : decodeTimingMode j = .ok m) : j = .string m.toStr := by
  cases m <;> simp only [TimingMode.toStr] <;>
    simp only [decodeTimingMode] at h <;> split at h <;> simp_all

/-─────────────────────────────────────────────────────────────────────────────
  SyncSource — timing.synchronization.source
─────────────────────────────────────────────────────────────────────────────-/

inductive SyncSource where
  | genlock
  | videoIn
  | ptp
  | ntp
  deriving Repr, DecidableEq

def SyncSource.toStr : SyncSource → String
  | .genlock  => "genlock"
  | .videoIn  => "videoIn"
  | .ptp      => "ptp"
  | .ntp      => "ntp"

def decodeSyncSource (j : JsonValue) : Except DecodeError SyncSource :=
  match j with
  | .string "genlock"  => .ok .genlock
  | .string "videoIn"  => .ok .videoIn
  | .string "ptp"      => .ok .ptp
  | .string "ntp"      => .ok .ntp
  | .string s          => .error (.invalidEnum "syncSource" s)
  | _                  => .error .expectedString

theorem decodeSyncSource_sound (j : JsonValue) (s : SyncSource)
    (h : decodeSyncSource j = .ok s) : j = .string s.toStr := by
  cases s <;> simp only [SyncSource.toStr] <;>
    simp only [decodeSyncSource] at h <;> split at h <;> simp_all

/-─────────────────────────────────────────────────────────────────────────────
  PtpProfile — timing.synchronization.ptp.profile
─────────────────────────────────────────────────────────────────────────────-/

inductive PtpProfile where
  | ieee1588_2019
  | ieee802_1as_2020
  | smpte_st2059_2
  deriving Repr, DecidableEq

def PtpProfile.toStr : PtpProfile → String
  | .ieee1588_2019    => "IEEE Std 1588-2019"
  | .ieee802_1as_2020 => "IEEE Std 802.1AS-2020"
  | .smpte_st2059_2   => "SMPTE ST2059-2:2021"

def decodePtpProfile (j : JsonValue) : Except DecodeError PtpProfile :=
  match j with
  | .string "IEEE Std 1588-2019"    => .ok .ieee1588_2019
  | .string "IEEE Std 802.1AS-2020" => .ok .ieee802_1as_2020
  | .string "SMPTE ST2059-2:2021"   => .ok .smpte_st2059_2
  | .string s                        => .error (.invalidEnum "ptpProfile" s)
  | _                                => .error .expectedString

theorem decodePtpProfile_sound (j : JsonValue) (p : PtpProfile)
    (h : decodePtpProfile j = .ok p) : j = .string p.toStr := by
  cases p <;> simp only [PtpProfile.toStr] <;>
    simp only [decodePtpProfile] at h <;> split at h <;> simp_all

/-─────────────────────────────────────────────────────────────────────────────
  PtpLeaderSource — timing.synchronization.ptp.leaderTimeSource
─────────────────────────────────────────────────────────────────────────────-/

inductive PtpLeaderSource where
  | gnss
  | atomicClock
  | ntp
  deriving Repr, DecidableEq

def PtpLeaderSource.toStr : PtpLeaderSource → String
  | .gnss        => "GNSS"
  | .atomicClock => "Atomic clock"
  | .ntp         => "NTP"

def decodePtpLeaderSource (j : JsonValue) : Except DecodeError PtpLeaderSource :=
  match j with
  | .string "GNSS"         => .ok .gnss
  | .string "Atomic clock" => .ok .atomicClock
  | .string "NTP"          => .ok .ntp
  | .string s              => .error (.invalidEnum "ptpLeaderTimeSource" s)
  | _                      => .error .expectedString

theorem decodePtpLeaderSource_sound (j : JsonValue) (l : PtpLeaderSource)
    (h : decodePtpLeaderSource j = .ok l) : j = .string l.toStr := by
  cases l <;> simp only [PtpLeaderSource.toStr] <;>
    simp only [decodePtpLeaderSource] at h <;> split at h <;> simp_all
