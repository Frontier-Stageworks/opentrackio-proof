/-
  ShaderCoords.lean — SLICE-OL-13

  Defines the image-to-shader coordinate conversion from OpenLensIO §4.2 Eq (18)
  and proves two roundtrip theorems:

    pixel_metric_roundtrip:
      fromShaderCoords w h wshader (toShaderCoords w h wshader p) = p

    image_texture_coordinate_roundtrip:
      toShaderCoords w h wshader (fromShaderCoords w h wshader q) = q

  Eq (18): ε_shader_x = wshader * ϵ_x / w + wshader / 2
           ε_shader_y = wshader * ϵ_y / h + wshader / 2

  Preconditions w > 0, h > 0, wshader > 0 are all needed to discharge
  division-by-zero side conditions in field_simp. Physical use enforces
  these via ValidSensorDimensions and ValidLensSemantics.
-/

import AngleOfView

/-─────────────────────────────────────────────────────────────────────────────
  toShaderCoords — Eq (18), forward direction: mm → shader pixel coordinates
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def toShaderCoords (w h wshader : ℝ) (p : SensorPoint) : SensorPoint :=
  ⟨wshader * p.x / w + wshader / 2, wshader * p.y / h + wshader / 2⟩

/-─────────────────────────────────────────────────────────────────────────────
  fromShaderCoords — Eq (18), inverse direction: shader pixel coordinates → mm
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def fromShaderCoords (w h wshader : ℝ) (q : SensorPoint) : SensorPoint :=
  ⟨w * (q.x - wshader / 2) / wshader, h * (q.y - wshader / 2) / wshader⟩

/-─────────────────────────────────────────────────────────────────────────────
  pixel_metric_roundtrip

  §4.2 Eq (18): converting mm → shader → mm returns the original point.
  All three positivity hypotheses are load-bearing:
    hw  : w ≠ 0 for x-component of fromShaderCoords
    hh  : h ≠ 0 for y-component of fromShaderCoords
    hs  : wshader ≠ 0 for both components of toShaderCoords
─────────────────────────────────────────────────────────────────────────────-/

theorem pixel_metric_roundtrip
    (w h wshader : ℝ) (hw : 0 < w) (hh : 0 < h) (hs : 0 < wshader)
    (p : SensorPoint) :
    fromShaderCoords w h wshader (toShaderCoords w h wshader p) = p := by
  ext <;> simp [fromShaderCoords, toShaderCoords] <;>
  field_simp [hw.ne', hh.ne', hs.ne']

/-─────────────────────────────────────────────────────────────────────────────
  image_texture_coordinate_roundtrip

  §4.2 Eq (18): converting shader → mm → shader returns the original point.
─────────────────────────────────────────────────────────────────────────────-/

theorem image_texture_coordinate_roundtrip
    (w h wshader : ℝ) (hw : 0 < w) (hh : 0 < h) (hs : 0 < wshader)
    (q : SensorPoint) :
    toShaderCoords w h wshader (fromShaderCoords w h wshader q) = q := by
  ext <;> simp [toShaderCoords, fromShaderCoords] <;>
  field_simp [hw.ne', hh.ne', hs.ne'] <;> ring
