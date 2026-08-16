# Sensor Identity and Acquisition-Mode Audit

## Part 1 — Sensor identity: MT9V034 vs MT9M034

### Evidence for MT9V034

1. **ASL's own driver wiki** (`ethz-asl/visensor_node` wiki, "Setting Sensor Parameters"): explicitly names "Aptina MT9V034 image sensors on the VI Sensor," for all four camera channels (CAM0–CAM3). Near-primary — ASL's own hardware documentation, not a third party.
2. **Resolution match, with no viable alternative construction from MT9M034.** MT9V034's datasheet-stated "Active Pixels" is exactly `752 H × 480 V` (ON Semi `MT9V034/D` Rev. 7, Table 1) — an exact match to EuRoC cam0's `752×480` image resolution. MT9M034's active array is `1280×960` (WebSearch-summarized datasheet figure, not full-text-verified in this session — see gap below). `1280×960 → 752×480` is not a standard binning or windowing operation: 2×2 binning of `1280×960` gives `640×480`, not `752×480`; a windowed *crop* to `752×480` is geometrically possible in principle (752 ≤ 1280, 480 ≤ 960) but would require a bespoke, non-round crop rectangle with no documented justification anywhere found. By contrast, `752×480` is not a crop of MT9V034 at all — it *is* MT9V034's stated full/native array.
3. **Global vs. rolling shutter.** MT9V034 is explicitly a *global-shutter* sensor (datasheet: "Global Shutter Photodiode Pixels; Simultaneous Integration and Readout"). MT9M034 (per WebSearch summary of its datasheet) is a *rolling-shutter* sensor. A rolling-shutter camera is a poor fit for a system whose own title is "a **synchronized** visual-inertial sensor system... for accurate real-time SLAM" (Nikolic et al., ICRA 2014) — rolling-shutter readout skew is a well-known source of visual-inertial calibration error that such a system would specifically avoid. This is circumstantial/engineering-plausibility evidence, not a citation, and is labeled as such.

### Evidence for MT9M034 (the contradiction, documented per task instruction)

- `ethz-asl/maplab_rovio`'s `cfg/euroc_cam0.yaml` header comment reads: *"VI-Sensor MT9M034 camera."* This is exactly the naming confusion flagged in the task prompt. `maplab_rovio` is an ETH-ASL-org repository, but it is a downstream *consumer* of the EuRoC calibration (a VIO front-end config), not the VI-Sensor driver or the dataset's own documentation — its comment is not treated as authoritative over the driver wiki + datasheet + shutter-type argument above.

### Verdict

**MT9V034**, on the strength of (1) ASL's own driver-repo wiki naming it directly, (2) an exact, parameter-free resolution match to MT9V034's stated full active array with no plausible construction from MT9M034's array, and (3) the shutter-type argument. Not from a single ETH/ASL publication naming the part number for the *EuRoC dataset specifically* (the Nikolic et al. ICRA 2014 paper, which would be the strongest possible source, could not be fetched — see `ambiguity-register.md`, AMB-EUROC-002). Classified **strong-but-not-single-source-authoritative**; the `maplab_rovio` comment is recorded as a known, resolved contradiction, not silently discarded.

## Part 2 — Acquisition-mode provenance (the gating question)

**Question**: do EuRoC cam0's 752×480 images correspond to the *full native* MT9V034 array with no crop/windowing/resize/binning/ROI, licensing the physical dimensions `752·6µm = 4.512mm` × `480·6µm = 2.880mm`?

### What the datasheet says (primary, direct citation)

ON Semi `MT9V034/D` Rev. 7, page 1: *"The default mode outputs a wide-VGA-size image at 60 frames per second."* Page 2, Table 1: `Active Pixels: 752 H x 480 V`; `Full Resolution: 752 x 480`; `Frame Rate: 60 fps (at full resolution)`. Page 1, Features: *"Window Size: User Programmable to any **Smaller** Format (QVGA, CIF, QCIF). ... Binning: 2×2 and 4×4 of the Full Resolution."*

### Reasoning

Since `752×480` **is** MT9V034's stated full/native array *and* its documented default output, and the datasheet's own windowing/binning features only ever produce formats *smaller* than `752×480` (QVGA, CIF, QCIF, or 2×2/4×4-binned reductions), there is no documented MT9V034 configuration that outputs exactly `752×480` other than the full, unwindowed array. This is a fairly tight *logical* argument from the datasheet's own stated capability list, not merely "the resolution happens to match."

### Why this is still classified Weak, not Strong

No source found in this session — ASL wiki, datasheet, `visensor_node` source (grepped for `752`/`window`/`resolution`/`WVGA`; none found — the resolution is apparently set at runtime via the two-wire serial register interface, not a static value in this ROS wrapper repo), or the EuRoC dataset's own docs page — contains an **explicit, EuRoC-specific statement** such as "cam0 was configured for full, unwindowed readout." The reasoning above closes off the space of *documented* MT9V034 configurations that could produce `752×480` other than full-array, but it cannot rule out an *undocumented* register configuration, nor could `libvisensor` (the low-level driver) be cloned and inspected in this session (clone attempt failed — see `investigation-log.md`). Per the task's own pre-defined tiers, "752×480 matches the sensor's native array, but no source explicitly confirms full-array capture" is exactly the **Weak** case, even though the supporting argument here is more constrained than a bare coincidence-of-resolution observation.

### Classification: **Weak** — strongly supported but inferred, not authoritative.

`physical_area_status` in `selected-fixture.json` (if §7–9 is authorized) should read `"inferred"`, not `"verified"`.
