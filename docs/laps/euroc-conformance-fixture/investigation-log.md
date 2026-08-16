# Investigation Log

Chronological record of what was searched/fetched, and outcome. Distinguishes primary (P), near-primary (NP), secondary (S), and failed/inconclusive (F) per source.

| # | Action | Source | Result | Tier |
|---|---|---|---|---|
| 1 | `git clone` | `github.com/ethz-asl/kalibr.git` | success, commit `1f60227...` | P (repo itself) |
| 2 | WebSearch | "EuRoC MAV dataset cam0 sensor.yaml intrinsics distortion_coefficients radtan" | returned pointers to downstream repos, not the original file | S |
| 3 | WebSearch | ETH ASL VI-Sensor MT9V034/MT9M034/Nikolic | returned `visensor_node` wiki + both datasheets | NP + P |
| 4 | WebFetch | `projects.asl.ethz.ch/datasets/doku.php?id=kmavvisualinertialdatasets` | stub redirect page only | F |
| 5 | WebFetch | `github.com/ethz-asl/visensor_node/wiki/Setting-Sensor-Parameters` | confirmed "Aptina MT9V034" for VI-Sensor CAM0–3 | NP |
| 6 | WebFetch | `onsemi.com/pdf/datasheet/mt9v034-d.pdf` | HTTP 403 (direct) | F |
| 7 | WebFetch | `ethz-asl.github.io/datasets/` | redirected to `projects.asl.ethz.ch/datasets/` | — |
| 8 | Bash curl | `onsemi.com/pdf/datasheet/mt9v034-d.pdf` w/ browser UA | HTTP 403 | F |
| 9 | WebFetch | `projects.asl.ethz.ch/datasets/` | index/listing page only, points to ETH Research Collection DOI, no inline calibration | S (index only) |
| 10 | WebFetch | `uctronics.com/download/Image_Sensor/MT9V034_DS.pdf` | HTTP 403 | F |
| 11 | WebSearch | "asl-datasets EuRoC calibration cam0 sensor.yaml download" | pointed to `maplab_rovio/cfg/euroc_cam0.yaml` and legacy `robotics.ethz.ch/~asl-datasets/...` host | S |
| 12 | WebSearch | "MT9V034 752 480 active imager size mm pixel size 6.0" | search-engine summary of onsemi/mouser datasheet: 4.51mm×2.88mm, 6.0µm, 752×480 | P (summarized, not yet full-text) |
| 13 | Bash | `find . -iname "*radtan*"` in kalibr clone | located `RadialTangentialDistortion.{hpp,cpp}` | P |
| 14 | WebFetch | `github.com/ethz-asl/kalibr/wiki/Calibrating-the-VI-Sensor` | no hardware/resolution detail, points to skybotix.com | NP (inconclusive) |
| 15 | Read | `RadialTangentialDistortion.hpp` (implementation) | full forward (`distort`, closed-form) + inverse (`undistort`, 5-iter Gauss-Newton) traced | P |
| 16 | WebFetch | `mouser.com/ds/2/308/MT9V034-D-606247.pdf` | timeout (60s) | F |
| 17 | WebFetch | `github.com/ethz-asl/maplab_rovio/blob/master/cfg/euroc_cam0.yaml` | full EuRoC cam0 calibration values + a "MT9M034" comment (the flagged contradiction) | S |
| 18 | Bash | `find . -iname "*PinholeCamera*"` in kalibr | located `PinholeCameraGeometry.cpp` | P |
| 19 | WebFetch | `onsemi.com/download/data-sheet/pdf/mt9v034-d.pdf` | HTTP 403 | F |
| 20 | Read | `PinholeCameraGeometry.cpp` | confirms a second, independent implementation of the same forward/inverse split | P |
| 21 | git clone + grep | `ethz-asl/visensor_node.git` (driver ROS wrapper) | no static resolution/windowing config found in this repo (set at runtime via serial registers, not present here) | NP (inconclusive on windowing specifically) |
| 22 | WebSearch | Nikolic ICRA 2014 VI-Sensor paper full text | no open-access PDF link found (IEEE Xplore only) | F |
| 23 | WebFetch | Semantic Scholar paper page | returned no content | F |
| 24 | Bash | `git clone ethz-asl/libvisensor.git` | failed (`timeout` command unavailable on this system, then a syntax error; not retried given the reasonable-search stop condition) | F |
| 25 | WebFetch | `onsemi.com/download/data-sheet/pdf/mt9v034-d.pdf`, retried | returned the PDF binary (saved locally), but text extraction from the fetch tool's markdown conversion failed | F (via WebFetch) |
| 26 | Read (PDF pages) | the locally-saved MT9V034 datasheet PDF, pages 1–3 | **full-text confirmed**: Active Imager Size 4.51mm(H)×2.88mm(V), Active Pixels 752H×480V, Pixel Size 6.0×6.0µm, Full Resolution 752×480, "default mode outputs a wide-VGA-size image," Window Size "User Programmable to any **Smaller** Format," Binning 2×2/4×4 | **P — direct primary-source full text, this is the strongest citation in the investigation** |
| 27 | Bash | `git clone ethz-asl/libvisensor.git` (fixed syntax) | still failed (clone did not complete/repo not found under that exact path in the time available) | F |
| 28 | Read | local `InverseApproximation.lean` lines 1–60 | confirmed `Coeffs`/`radial`/`Φ` structure for §5 compatibility check | — (internal) |
| 29 | Bash grep | `docs/specification-questions.md` for focal-length/fx/fy entries | found SQ-CV-04 already resolved and directly on-point | — (internal) |
| 30 | Read | `PrincipalPointConversion.lean` full file | confirmed `single_focal_length_compatibility` and the `w`/`w_shader` physical/pixel semantics | — (internal) |
| 31 | Bash grep + Read | `docs/opentrackio-proof-summary.md` §2.1/§3.1 | confirmed `w` = physical mm, `w_shader` = raster px, resolving the Fx/Fy mapping | — (internal) |
| 32 | Read | `opencv_opentrackio_proofs/Pipeline/OpenCVModel.lean` (`distortXCV`/`distortYCV`) | confirmed rational-radial form degenerates to EuRoC's polynomial radtan under `k4=k5=k6=0` | — (internal) |
| 33 | WebSearch | "MT9M034 active pixel array resolution pixel size micrometers datasheet" | 1280×960, 3.75µm, rolling shutter (summary only, not full-text) | S (summarized) |
| 34 | Bash (background) | direct download probe of legacy ASL dataset hosts (`robotics.ethz.ch/~asl-datasets/...`, an S3 mirror) | both failed (DNS/connection failure; 404) — confirms the "permanently moved" note from step 4 | F |

## Stop points taken (per the task's documented-search stop condition)

- Nikolic et al. ICRA 2014 full text: stopped after 2 failed access attempts (steps 22–23). Recorded as AMB-EUROC-002.
- `libvisensor` (low-level driver, would be the best remaining source for an explicit windowing/register statement): stopped after 2 failed clone attempts (steps 24, 27) — environment/tooling issue (`timeout` not available; repo path/availability not confirmed), not a deliberate decision to avoid the source. Recorded as a residual gap in `sensor-acquisition-audit.md` Part 2.
- MT9M034 datasheet: not full-text fetched (only WebSearch summary, step 33) — sufficient for the contrast argument in `sensor-acquisition-audit.md`; a full-text fetch was not pursued further since the sensor-identity question was already resolved via the stronger MT9V034 evidence chain, and MT9M034's role here is only as the rejected alternative.
- Original ASL `sensor.yaml`/calibration archive: stopped after 4 failed access routes (steps 4, 7, 9, 34). Recorded as AMB-EUROC-001's provenance caveat in `provenance.md`.
