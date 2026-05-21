# Proof Plan — rational-decoder (Slice 5)

## `decodePositiveRational`

Pattern: `.object _` → simultaneous lookup of `"num"` and `"denom"` → both
`.number` strings → `s.toNat?` → decision proofs `0 < n` and `0 < d`.

```lean
def decodePositiveRational (j : JsonValue) : Except DecodeError PositiveRational :=
  match j with
  | .object _ =>
    match j.lookup? "num", j.lookup? "denom" with
    | none, _         => .error (.missingField "num")
    | _, none         => .error (.missingField "denom")
    | some nj, some dj =>
      match nj, dj with
      | .number ns, .number ds =>
        match ns.toNat?, ds.toNat? with
        | some n, some d =>
          if hn : 0 < n then
            if hd : 0 < d then .ok { num := n, den := d, num_pos := hn, den_pos := hd }
            else .error (.invalidRational "denom")
          else .error (.invalidRational "num")
        | none, _ => .error (.invalidRational "num")
        | _, none => .error (.invalidRational "denom")
      | .number _, _ => .error .expectedNumber
      | _, _         => .error .expectedNumber
  | _ => .error .expectedObject
```

Error coverage:
- Non-object input → `expectedObject`
- `"num"` absent → `missingField "num"`
- `"denom"` absent (with `"num"` present) → `missingField "denom"`
- `"num"` not a JSON number → `expectedNumber`
- `"denom"` not a JSON number (with `"num"` a number) → `expectedNumber`
- `"num"` string not a Nat → `invalidRational "num"`
- `"denom"` string not a Nat → `invalidRational "denom"`
- `"num"` parses as 0 → `invalidRational "num"`
- `"denom"` parses as 0 → `invalidRational "denom"`
- Both positive Nats → `.ok r` with `r.num = n`, `r.den = d`

## `decodePositiveRational_sound`

```lean
theorem decodePositiveRational_sound
    (j : JsonValue) (r : PositiveRational)
    (_h : decodePositiveRational j = .ok r) :
    0 < r.toReal :=
  positive_rational_toReal_pos r
```

Hard step: none. `positive_rational_toReal_pos` is already proved in Slice 1.
The decision proofs `hn` and `hd` in the decoder ensure the struct fields
`num_pos` and `den_pos` are populated, which is all `positive_rational_toReal_pos`
requires.

Automation budget: none needed for the theorem.
