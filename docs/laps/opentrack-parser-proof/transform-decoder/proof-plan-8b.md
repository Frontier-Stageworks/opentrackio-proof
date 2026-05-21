# Proof Plan — transform-decoder (Slice 8B)

## `decodeNumberField`

Accepts `.number s`; rejects anything else with `invalidRational ctx`.

```lean
def decodeNumberField (ctx : String) (j : JsonValue) : Except DecodeError String :=
  match j with
  | .number s => .ok s
  | _         => .error (.invalidRational ctx)
```

## `decodeVec3`

Explicit `match` on each `lookup?`. No `Option.getD`.

```lean
def decodeVec3 (j : JsonValue) : Except DecodeError Vec3 :=
  match j with
  | .object _ =>
    match j.lookup? "x" with
    | none    => .error (.missingField "x")
    | some xj =>
    match j.lookup? "y" with
    | none    => .error (.missingField "y")
    | some yj =>
    match j.lookup? "z" with
    | none    => .error (.missingField "z")
    | some zj => do
        let x ← decodeNumberField "x" xj
        let y ← decodeNumberField "y" yj
        let z ← decodeNumberField "z" zj
        return { x, y, z }
  | _ => .error .expectedObject
```

## `decodeRotation`

Same structure as `decodeVec3`, fields `"pan"`, `"tilt"`, `"roll"`.

## `decodeTransform`

Required fields use explicit `match` on `lookup?` before the `do` block.
Optional `scale` and `id` handled inside `do` with nested `match`.
The `id` branch uses a decision proof to construct `NonemptyString`.

```lean
def decodeTransform (j : JsonValue) : Except DecodeError Transform :=
  match j with
  | .object _ =>
    match j.lookup? "translation" with
    | none    => .error (.missingField "translation")
    | some tj =>
    match j.lookup? "rotation" with
    | none    => .error (.missingField "rotation")
    | some rj => do
        let translation ← decodeVec3 tj
        let rotation    ← decodeRotation rj
        let scale ← match j.lookup? "scale" with
                    | none    => pure none
                    | some sj => (decodeVec3 sj).map some
        let id ← match j.lookup? "id" with
                 | none    => pure none
                 | some ij =>
                   match ij with
                   | .string s =>
                     if h : s ≠ "" then pure (some ⟨s, h⟩)
                     else .error (.missingField "id")
                   | _ => .error .expectedString
        return { translation, rotation, scale, id }
  | _ => .error .expectedObject
```

Load-bearing step: `if h : s ≠ "" then pure (some ⟨s, h⟩)` — the decision
proof `h` becomes the `nonempty` field of `NonemptyString`.

## `decodeTransform_sound`

Goal shape: `∀ ns, t.id = some ns → ns.val ≠ ""`
Opening move: `fun ns _ => ns.nonempty` (term-mode proof)

```lean
theorem decodeTransform_sound
    (j : JsonValue) (t : Transform)
    (_h : decodeTransform j = .ok t) :
    ∀ ns, t.id = some ns → ns.val ≠ "" :=
  fun ns _ => ns.nonempty
```

Hard step: none. `NonemptyString.nonempty` is the struct field.
Automation budget: none — pure term proof.

## Stop rule

If the term proof `fun ns _ => ns.nonempty` does not type-check, stop
immediately. Do not attempt tactic alternatives until the type-check error
is understood. The only expected failure is a universe or implicit argument
issue, which should be diagnosable from the error message alone.
