# Provenance — EuRoC Conformance Fixture Investigation

## Repository clones

| Repo | URL | Commit | Clone date | License |
|---|---|---|---|---|
| kalibr | https://github.com/ethz-asl/kalibr.git | `1f60227442d25e36365ef5f72cd80b9666d73467` (2024-03-08, "Merge pull request #673 from AndyZe/write_svg") | 2026-08-16 | BSD-style, `Copyright (c) 2014, Paul Furgale, Jérôme Maye and Jörn Rehder, Autonomous Systems Lab, ETH Zurich, Switzerland; Copyright (c) 2014, Thomas Schneider, Skybotix AG, Switzerland. All rights reserved.` (see `LICENSE`) |
| visensor_node | https://github.com/ethz-asl/visensor_node.git | HEAD at shallow-clone time, 2026-08-16 (depth 1, exact SHA not separately recorded) | 2026-08-16 | not inspected (repo consulted only for its wiki, not its code license) |

Clones live under `/Users/markstalzer/github/scratch-clones/` (outside this repo; not committed, per task scope — no Lean files or repo structure of `opentrackio-proof` touched by the clone itself).

`rovio` was not cloned — not needed; the VI-Sensor hardware question was resolved via `visensor_node`'s own wiki (§below) without requiring `rovio`.

## EuRoC cam0 calibration — value provenance chain

**Could not directly fetch ASL's own original `sensor.yaml` / calibration archive within this session.** Attempted:
- `https://projects.asl.ethz.ch/datasets/doku.php?id=kmavvisualinertialdatasets` — returns only a "resource permanently moved" redirect stub.
- `https://ethz-asl.github.io/datasets/` → redirects to `https://projects.asl.ethz.ch/datasets/` — this is an index page listing datasets by name/year with a link to the ETH Research Collection DOI (`https://doi.org/10.3929/ethz-b-000690084`); it does not itself contain calibration values.
- `https://projects.asl.ethz.ch/datasets/euroc-mav/` — confirms the dataset provides "Camera intrinsics" and "Camera–IMU extrinsics" and mentions "Stereo images (WVGA monochrome, 2×20 FPS)" but does not inline the numeric calibration.
- A direct attempt to fetch the original calibration/sequence archive from `robotics.ethz.ch/~asl-datasets/...` did not complete within a reasonable time and was not pursued further (large file, not essential — see below).

**What was obtained instead**: the specific EuRoC cam0 numeric calibration (`fx=458.654, fy=457.296, cx=367.215, cy=248.375`, distortion `[-0.28340811, 0.07395907, 0.00019359, 1.76187114e-05, 0.0]`, resolution `752×480`) via `ethz-asl/maplab_rovio`'s `cfg/euroc_cam0.yaml` (an ETH-ASL-org repo, but a downstream *consumer* config, not the original dataset archive). Cross-referenced against WebSearch summaries of independent downstream repos (VINS-Mono issue #206, sptam issue #14, sptam/OpenVINS docs) that all report the identical values.

**Classification: strongly-corroborated secondary, not directly-verified primary.** These exact values (to 8 significant figures) are ubiquitous and mutually consistent across many independent SLAM/VIO codebases that each ingest the ASL-published calibration — that consistency is itself meaningful corroboration (independent transcription errors converging on 8-sig-fig agreement is implausible) — but this task did not manage to read ASL's own original calibration file byte-for-byte. Flagged, not silently treated as primary.

## Camera sensor hardware — source list, in preference order

1. **`ethz-asl/visensor_node` wiki**, "Setting Sensor Parameters" page (`github.com/ethz-asl/visensor_node/wiki/Setting-Sensor-Parameters`) — ASL's own VI-Sensor ROS driver repository. States: *"The Aptina MT9V034 image sensors on the VI Sensor can be configured with a wide range of parameters,"* naming CAM0–CAM3 as all using this sensor. **Near-primary** (ASL's own hardware/driver documentation, not a third party).
2. **ON Semiconductor MT9V034 datasheet** (`MT9V034/D`, Rev. 7, January 2017, `www.onsemi.com/pdf/datasheet/mt9v034-d.pdf`; full text obtained via a mirror at `robu-prod-media.s3...MT9V034-datasheet.pdf` after the direct onsemi.com URL returned HTTP 403 in this sandboxed environment). **Primary** manufacturer datasheet.
3. **ON Semiconductor MT9M034 datasheet** (fetched via WebSearch summary only, not full-text) — used as the contrasting hardware candidate named in the user's stated "known naming confusion."
4. Nikolic et al., "A Synchronized Visual-Inertial Sensor System with FPGA Pre-Processing for Accurate Real-Time SLAM," ICRA 2014 — **not fetched**. No open-access full-text PDF link was found in this session (IEEE Xplore paywalled; Semantic Scholar page returned no usable content; ResearchGate not attempted further). This is a documented search failure, not a silent omission — see `ambiguity-register.md`.
5. **`ethz-asl/maplab_rovio`, `cfg/euroc_cam0.yaml`** — a downstream config file whose header comment says *"VI-Sensor MT9M034 camera."* This directly instantiates the user's stated naming-confusion concern. **Secondary and contradictory** — flagged, not trusted (see `sensor-acquisition-audit.md`).

## Kalibr radtan (RadialTangentialDistortion) implementation — exact locations

- `aslam_cv/aslam_cameras/include/aslam/cameras/implementation/RadialTangentialDistortion.hpp`, lines 4–25 (`distort`, forward map) and lines 67–100 (`undistort`, inverse map).
- `aslam_cv/aslam_cameras/src/PinholeCameraGeometry.cpp`, lines 92–111 (`distortion`, forward map, a second independent implementation of the same formula inside the pinhole-camera class) and lines 145–175 (`undistortGN`, inverse map).

Both are read directly from the cloned repo at commit `1f60227442d25e36365ef5f72cd80b9666d73467`; see `investigation.md` §1 for the traced equations and direction analysis.
