# Proof Plan — timing-enum-decoders (Slice 7)

## Types and `toStr` functions

```lean
inductive TimingMode      | internal | external
inductive SyncSource      | genlock  | videoIn | ptp | ntp
inductive PtpProfile      | ieee1588_2019 | ieee802_1as_2020 | smpte_st2059_2
inductive PtpLeaderSource | gnss | atomicClock | ntp

def TimingMode.toStr      : TimingMode → String
  | .internal        => "internal"
  | .external        => "external"

def SyncSource.toStr      : SyncSource → String
  | .genlock         => "genlock"
  | .videoIn         => "videoIn"
  | .ptp             => "ptp"
  | .ntp             => "ntp"

def PtpProfile.toStr      : PtpProfile → String
  | .ieee1588_2019   => "IEEE Std 1588-2019"
  | .ieee802_1as_2020 => "IEEE Std 802.1AS-2020"
  | .smpte_st2059_2  => "SMPTE ST2059-2:2021"

def PtpLeaderSource.toStr : PtpLeaderSource → String
  | .gnss            => "GNSS"
  | .atomicClock     => "Atomic clock"
  | .ntp             => "NTP"
```

## Decoder pattern (identical for all four)

```lean
def decodeTimingMode (j : JsonValue) : Except DecodeError TimingMode :=
  match j with
  | .string "internal" => .ok .internal
  | .string "external" => .ok .external
  | .string s          => .error (.invalidEnum "timingMode" s)
  | _                  => .error .expectedString
```

Error coverage (identical structure for all):
- Exact match → `.ok variant`
- Unknown string → `invalidEnum context s`
- Non-string input → `expectedString`

## Soundness proof plan (identical for all four)

Goal shape: `j = .string x.toStr` — an equality.  
Opening move: `cases m` to fix the variant, then `split at h` to enumerate `j` branches.

```lean
theorem decodeTimingMode_sound (j : JsonValue) (m : TimingMode)
    (h : decodeTimingMode j = .ok m) : j = .string m.toStr := by
  cases m <;> simp only [TimingMode.toStr] <;>
    simp only [decodeTimingMode] at h <;> split at h <;> simp_all
```

Proof chain per variant (e.g. `m = .internal`):
1. `cases m` → goal becomes `j = .string .internal.toStr`
2. `simp only [TimingMode.toStr]` → goal becomes `j = .string "internal"`
3. `simp only [decodeTimingMode] at h` → `h` unfolds to `(match j ...) = .ok .internal`
4. `split at h` → case-splits on `j`; in each branch `j` is substituted into the goal:
   - `j = .string "internal"`: goal is `"internal" = "internal"`, `h` is trivial → `simp_all` closes by `rfl`
   - `j = .string "external"`: goal is `"external" = "internal"` (false), `h : .ok .external = .ok .internal` → contradiction → `simp_all` closes
   - other `j` shapes: `h : .error _ = .ok _` → contradiction → `simp_all` closes

Key insight: `cases m` first prevents the `subst`-orientation problem that arises when
`split at h` produces `h : Constructor = variable` (wrong direction for `simp` rewriting).
After `cases m`, `m` is a concrete constructor and `simp_all` only needs to close
equalities and contradictions, both of which it handles.

Hard step: none. The proof is mechanical case analysis.
Automation budget: `simp only [X.toStr]` and `simp_all` — no bare `simp`, no `omega`.
