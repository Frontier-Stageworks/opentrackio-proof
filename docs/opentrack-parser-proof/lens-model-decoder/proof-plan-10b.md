# Proof Plan — lens-decoder (Slice 10B)

## Files and lakefile entries

| File | Library name |
|---|---|
| `opentrackio_parser/LensModel.lean` | `LensModel` |
| `opentrackio_parser/LensDecoder.lean` | `LensDecoder` |

Two new `[[lean_lib]]` entries added to `lakefile.toml`.

---

## 10A — LensModel.lean

**Imports:** `NonemptyArrayDecoder`, `TransformModel`

(`NonemptyArrayDecoder` provides `NonemptyArray`; `TransformModel` provides `NonemptyString`.)

### Step 1. `FizOptions`

```lean
structure FizOptions where
  focus      : Option String
  iris       : Option String
  zoom       : Option String
  anyPresent : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none
```

Load-bearing invariant field. No separate `ValidFizOptions` predicate.

### Step 2. `DistortionOffset`

```lean
structure DistortionOffset where
  x : String
  y : String
```

### Step 3. `ProjectionOffset`

```lean
structure ProjectionOffset where
  x : String
  y : String
```

### Step 4. `ExposureFalloff`

```lean
structure ExposureFalloff where
  a1 : String
  a2 : Option String
  a3 : Option String
```

### Step 5. `Distortion`

```lean
structure Distortion where
  radial     : NonemptyArray String
  tangential : Option (NonemptyArray String)
  overscan   : Option String
  model      : String   -- absent in JSON → "Brown-Conrady D-U"
```

`model` is `String` not `Option String` — the JSON-absent case is handled at
decode time by substituting the default; the type does not represent absence.

### Step 6. `StaticLens`

```lean
structure StaticLens where
  distortionOverscanMax   : Option String
  undistortionOverscanMax : Option String
  make                    : Option NonemptyString
  model                   : Option NonemptyString
  serialNumber            : Option NonemptyString
  firmwareVersion         : Option NonemptyString
  nominalFocalLength      : Option String
  calibrationHistory      : Option (List NonemptyString)
```

### Step 7. `Lens`

```lean
structure Lens where
  custom              : Option (List String)
  distortion          : Option (NonemptyArray Distortion)
  distortionOffset    : Option DistortionOffset
  encoders            : Option FizOptions
  entrancePupilOffset : Option String
  exposureFalloff     : Option ExposureFalloff
  fStop               : Option String
  focusDistance       : Option String
  pinholeFocalLength  : Option String
  projectionOffset    : Option ProjectionOffset
  rawEncoders         : Option FizOptions
  tStop               : Option String
```

Build `LensModel` before proceeding to 10B.

---

## 10B — LensDecoder.lean

**Imports:** `Mathlib.Tactic`, `DecodeError`, `JsonRawModel`, `LensModel`,
`NonemptyArrayDecoder`

### Private helpers

**`decodeNumberString`** — element decoder for nonempty numeric arrays:

```lean
private def decodeNumberString (j : JsonValue) : Except DecodeError String :=
  match j with
  | .number s => .ok s
  | _         => .error .expectedNumber
```

**`decodeOptionalString`** — shared helper for `Option NonemptyString` fields
(same logic as Slice 9B; redefined locally):

```lean
private def decodeOptionalString (key : String) (jv : Option JsonValue) :
    Except DecodeError (Option NonemptyString) :=
  match jv with
  | none             => .ok none
  | some (.string s) =>
    if h : s ≠ "" then .ok (some ⟨s, h⟩)
    else .error (.missingField key)
  | some _           => .error .expectedString
```

**`decodeCustom`** — decodes `lens.custom` (array of JSON numbers):

```lean
private def decodeCustom (j : JsonValue) : Except DecodeError (List String) :=
  match j with
  | .array elems => elems.mapM (fun ej => match ej with
      | .number s => .ok s
      | _         => .error .expectedNumber)
  | _ => .error .expectedArray
```

**`decodeCalibrationHistory`** — decodes array of nonempty strings:

```lean
private def decodeCalibrationHistory (j : JsonValue) :
    Except DecodeError (List NonemptyString) :=
  match j with
  | .array elems => elems.mapM (fun ej => match ej with
      | .string s => if h : s ≠ "" then .ok ⟨s, h⟩
                     else .error (.missingField "calibrationHistory element")
      | _         => .error .expectedString)
  | _ => .error .expectedArray
```

### Sub-object decoders

**`decodeFizOptions`** — load-bearing step is `if h : focus ≠ none ∨ ...`:

```lean
def decodeFizOptions (j : JsonValue) : Except DecodeError FizOptions :=
  match j with
  | .object _ =>
    let focus := match j.lookup? "focus" with
                 | some (.number s) => some s
                 | _                => none
    let iris  := match j.lookup? "iris" with
                 | some (.number s) => some s
                 | _                => none
    let zoom  := match j.lookup? "zoom" with
                 | some (.number s) => some s
                 | _                => none
    if h : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none then
      .ok { focus, iris, zoom, anyPresent := h }
    else
      .error (.missingField "focus/iris/zoom")
  | _ => .error .expectedObject
```

`h : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none` is decidable because
`DecidableEq (Option String)` is available. `h` becomes the `anyPresent`
struct field directly — no later proof recovery needed.

**`decodeDistortionOffset`:**

```lean
def decodeDistortionOffset (j : JsonValue) : Except DecodeError DistortionOffset :=
  match j with
  | .object _ =>
    match j.lookup? "x" with
    | none    => .error (.missingField "x")
    | some xj =>
    match j.lookup? "y" with
    | none    => .error (.missingField "y")
    | some yj =>
      match xj, yj with
      | .number xs, .number ys => .ok { x := xs, y := ys }
      | .number _,  _          => .error .expectedNumber
      | _,          _          => .error .expectedNumber
  | _ => .error .expectedObject
```

**`decodeProjectionOffset`:** Same structure as `decodeDistortionOffset` with
fields `"x"` and `"y"`.

**`decodeExposureFalloff`:** `"a1"` required; `"a2"` and `"a3"` optional via
plain `let` (no `←`) inside the `do` block:

```lean
def decodeExposureFalloff (j : JsonValue) : Except DecodeError ExposureFalloff :=
  match j with
  | .object _ =>
    match j.lookup? "a1" with
    | none     => .error (.missingField "a1")
    | some a1j =>
      match a1j with
      | .number a1s =>
        let a2 := match j.lookup? "a2" with
                  | some (.number s) => some s
                  | _                => none
        let a3 := match j.lookup? "a3" with
                  | some (.number s) => some s
                  | _                => none
        .ok { a1 := a1s, a2, a3 }
      | _ => .error .expectedNumber
  | _ => .error .expectedObject
```

**`decodeDistortion`:** `"radial"` required; `"tangential"` optional nonempty
array; `"overscan"` optional plain-let; `"model"` defaults to
`"Brown-Conrady D-U"` when absent or non-string:

```lean
def decodeDistortion (j : JsonValue) : Except DecodeError Distortion :=
  match j with
  | .object _ =>
    match j.lookup? "radial" with
    | none    => .error (.missingField "radial")
    | some rj => do
        let radial     ← decodeNonemptyArray decodeNumberString "radial" rj
        let tangential ← match j.lookup? "tangential" with
                         | none    => .ok none
                         | some tj =>
                           (decodeNonemptyArray decodeNumberString "tangential" tj).map some
        let overscan := match j.lookup? "overscan" with
                        | some (.number s) => some s
                        | _                => none
        let model ← match j.lookup? "model" with
                    | none             => .ok "Brown-Conrady D-U"
                    | some (.string s) => .ok s
                    | some _           => .error .expectedString
        return { radial, tangential, overscan, model }
  | _ => .error .expectedObject
```

`model` uses `←` (monadic bind) because a present-but-non-string value is an
error, not a silent fallback.

### Top-level decoders

**`decodeStaticLens`:** All 8 fields optional; `do` block with inline `match`.
Scalar number fields use plain `let`; `NonemptyString` fields use
`decodeOptionalString`; `calibrationHistory` delegates to
`decodeCalibrationHistory`.

**`decodeLens`:** All 12 fields optional; `do` block with inline `match`.
Sub-object fields delegate to their respective decoders via `.map some`.
Scalar number fields use plain `let`. `distortion` uses
`decodeNonemptyArray decodeDistortion "distortion"`.

### Soundness theorem

```lean
theorem decodeLens_sound
    (j : JsonValue) (l : Lens)
    (_h : decodeLens j = .ok l) :
    ∀ fiz, l.encoders = some fiz →
      fiz.focus ≠ none ∨ fiz.iris ≠ none ∨ fiz.zoom ≠ none :=
  fun fiz _ => fiz.anyPresent
```

Hard step: none. `fiz.anyPresent` is the struct field.
Automation budget: none — pure term proof.

## Stop rule

If `if h : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none` does not elaborate
(missing `Decidable` instance), stop immediately and diagnose before attempting
any alternative. Do not use `open Classical` or `decide`.

If `decodeLens` fails to elaborate, identify which field binding is the problem
before attempting any fix.
