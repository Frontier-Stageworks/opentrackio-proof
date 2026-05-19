# Proof Capsule — lens-sub-object-encoders (Slice 15.10A)

## Scope

New proof infrastructure plus five sub-object encoders and their roundtrip theorems.
All definitions live in a single new file `LensSubEncoders.lean`.

| Artifact | Status |
|---|---|
| `list_mapM_ok` (private lemma) | NEW |
| `decodeNonemptyArray_roundtrip` (private lemma) | NEW |
| `encodeFizOptions` | NEW |
| `encodeDistortionOffset` | NEW |
| `encodeProjectionOffset` | NEW |
| `encodeExposureFalloff` | NEW |
| `encodeNonemptyStringArray` | NEW |
| `encodeDistortion` | NEW |
| `encodeFizOptions_roundtrip` | NEW |
| `encodeDistortionOffset_roundtrip` | NEW |
| `encodeProjectionOffset_roundtrip` | NEW |
| `encodeExposureFalloff_roundtrip` | NEW |
| `encodeNonemptyStringArray_roundtrip` | NEW |
| `encodeDistortion_roundtrip` | NEW |

File: `opentrackio_parser/LensSubEncoders.lean`
Library name: `LensSubEncoders`
Lakefile entry: after `CameraEncoder`

---

## Dependencies

| Import | Provides |
|---|---|
| `Mathlib` | tactics, `List.mapM` lemmas |
| `LensDecoder` | all public decoders; `NonemptyArray`; `FizOptions`, `DistortionOffset`, `ProjectionOffset`, `ExposureFalloff`, `Distortion` |
| `TimecodeEncoder` | `encodePositiveRational`, `encodePositiveRational_roundtrip` |

`LensDecoder` transitively imports `NonemptyArrayDecoder`, making `decodeNonemptyArray`
and `NonemptyArray` (with field `values : List α`, `nonempty : values ≠ []`) available.

---

## Frozen formal statements

### Infrastructure lemmas (private)

```lean
private theorem list_mapM_ok
    {α : Type} (enc : α → JsonValue) (dec : JsonValue → Except DecodeError α)
    (hrt : ∀ a, dec (enc a) = .ok a) :
    ∀ xs : List α, xs.mapM (fun a => dec (enc a)) = .ok xs

private theorem decodeNonemptyArray_roundtrip
    {α : Type} (enc : α → JsonValue) (dec : JsonValue → Except DecodeError α)
    (hrt : ∀ a, dec (enc a) = .ok a) (ctx : String) (arr : NonemptyArray α) :
    decodeNonemptyArray dec ctx (.array (arr.values.map enc)) = .ok arr
```

### Sub-object encoders and roundtrips

```lean
def encodeFizOptions (fiz : FizOptions) : JsonValue :=
  .object (
    (fiz.focus.map fun s => ("focus", .number s)).toList ++
    (fiz.iris.map  fun s => ("iris",  .number s)).toList ++
    (fiz.zoom.map  fun s => ("zoom",  .number s)).toList)

theorem encodeFizOptions_roundtrip (fiz : FizOptions) :
    decodeFizOptions (encodeFizOptions fiz) = .ok fiz

def encodeDistortionOffset (d : DistortionOffset) : JsonValue :=
  .object [("x", .number d.x), ("y", .number d.y)]

theorem encodeDistortionOffset_roundtrip (d : DistortionOffset) :
    decodeDistortionOffset (encodeDistortionOffset d) = .ok d

def encodeProjectionOffset (p : ProjectionOffset) : JsonValue :=
  .object [("x", .number p.x), ("y", .number p.y)]

theorem encodeProjectionOffset_roundtrip (p : ProjectionOffset) :
    decodeProjectionOffset (encodeProjectionOffset p) = .ok p

def encodeExposureFalloff (ef : ExposureFalloff) : JsonValue :=
  .object (
    [("a1", .number ef.a1)] ++
    (ef.a2.map fun s => ("a2", .number s)).toList ++
    (ef.a3.map fun s => ("a3", .number s)).toList)

theorem encodeExposureFalloff_roundtrip (ef : ExposureFalloff) :
    decodeExposureFalloff (encodeExposureFalloff ef) = .ok ef

def encodeNonemptyStringArray (arr : NonemptyArray String) : JsonValue :=
  .array (arr.values.map .number)

theorem encodeNonemptyStringArray_roundtrip (arr : NonemptyArray String) :
    decodeNonemptyArray (fun j => match j with
      | .number s => .ok s | _ => .error .expectedNumber) "radial"
        (encodeNonemptyStringArray arr) = .ok arr

def encodeDistortion (d : Distortion) : JsonValue :=
  .object (
    [("radial", encodeNonemptyStringArray d.radial),
     ("model",  .string d.model)] ++
    (d.tangential.map fun arr => ("tangential", encodeNonemptyStringArray arr)).toList ++
    (d.overscan.map   fun s   => ("overscan",   .number s)).toList)

theorem encodeDistortion_roundtrip (d : Distortion) :
    decodeDistortion (encodeDistortion d) = .ok d
```

---

## Key proof notes

### `list_mapM_ok`

Proved by induction on `xs`:
- Base (`[]`): `[].mapM f = .ok []` by `rfl`.
- Step (`hd :: tl`): `simp [List.mapM_cons, hrt hd]` + IH closes the goal.

### `decodeNonemptyArray_roundtrip`

`decodeNonemptyArray` matches `| .array (hd :: tl) =>`. Since `arr.values ≠ []`,
destructure with `rcases List.exists_cons_of_ne_nil arr.nonempty with ⟨hd, tl, rfl⟩`.
After substitution:
```
.array ((hd :: tl).map enc) = .array (enc hd :: tl.map enc)
```
`decodeNonemptyArray dec ctx (.array (enc hd :: tl.map enc))` matches the `hd :: tl` arm:
- `let v ← dec (enc hd)` = `.ok hd` by `hrt`
- `let vs ← (tl.map enc).mapM dec` = `tl.mapM (dec ∘ enc)` = `.ok tl` by `list_mapM_ok`
- Returns `{ values := hd :: tl, nonempty := List.cons_ne_nil hd tl }`

The `nonempty` field equality (`List.cons_ne_nil hd tl = arr.nonempty`) closes by proof
irrelevance. `simp [decodeNonemptyArray, hrt, list_mapM_ok, List.mapM_map]` with `<;> rfl`
should close, or an explicit `rfl`-based `ext`-style close.

### `encodeFizOptions_roundtrip`

`FizOptions` has `focus iris zoom : Option String` and `anyPresent : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none`. Strategy:
1. `obtain ⟨fo, ir, zo, hap⟩ := fiz`
2. `rcases fo with _ | fo <;> rcases ir with _ | ir <;> rcases zo with _ | zo`
   — 8 goals; the `none/none/none` case is unreachable since `hap` rules it out
3. `simp [encodeFizOptions, decodeFizOptions, JsonValue.lookup?, *]` closes each reachable goal via `dif_pos`

The `none/none/none` case: `hap : none ≠ none ∨ ...` — simp with `*` sees a contradiction and closes.

### `encodeDistortion_roundtrip`

`decodeDistortion` calls `decodeNonemptyArray decodeNumberString "radial" rj`.
`decodeNumberString` is private in `LensDecoder.lean`. Strategy: use
`encodeNonemptyStringArray_roundtrip` as a simp lemma, which matches the exact
`decodeNonemptyArray (fun j => ...) "radial" (encodeNonemptyStringArray d.radial)` term.
The statement of `encodeNonemptyStringArray_roundtrip` uses the inline lambda matching
`decodeNumberString`'s body, so simp can unify them.

`d.tangential` and `d.overscan` are optional; `rcases` each (4 goals).
`d.model` is always present — the encoder writes `("model", .string d.model)` and the
decoder's `some (.string s) => .ok s` arm fires.

---

## Out of scope

- `StaticLens` and `Lens` encoders — those are Slice 15.10B.
- No changes to any completed slice or to `LensDecoder.lean`.

---

## Stop rule

This capsule is complete. Do NOT proceed to the proof plan until the user signs off.
