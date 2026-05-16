# CAPS Smoke Specs — battery-tester

---

CAPS-ADAPT-001
WHEN python_adapter.py is invoked with a valid fixture path
THE SYSTEM SHALL emit a JSON object where all expected normalized fields
are present and non-null for fields that exist in the fixture
Verification: ✅

CAPS-ADAPT-002
WHEN the Mo-Sys C++ adapter binary is invoked with a valid fixture path
THE SYSTEM SHALL emit a JSON object where all expected normalized fields
are present and non-null for fields that exist in the fixture
Verification: ✅

CAPS-DIFF-001
WHEN both adapters parse complete_static_example.json
THE SYSTEM SHALL report PASS for transforms.Camera.translation.x,
transforms.Camera.translation.y, and transforms.Camera.translation.z
Verification: ✅

CAPS-DIFF-002
WHEN both adapters parse complete_static_example.json
THE SYSTEM SHALL report PASS for transforms.Camera.rotation.pan,
transforms.Camera.rotation.tilt, and transforms.Camera.rotation.roll
Verification: ✅

CAPS-DIFF-003
WHEN both adapters parse complete_static_example.json
THE SYSTEM SHALL report PASS for timing.timecode,
timing.sampleTimestamp.seconds, timing.sampleTimestamp.nanoseconds,
and timing.sampleRate
Verification: ✅

CAPS-DIFF-004
WHEN both adapters parse complete_static_example.json
THE SYSTEM SHALL report PASS for tracker.slate and tracker.serialNumber
Verification: ✅

CAPS-DIFF-005
WHEN both adapters parse complete_static_example.json
THE SYSTEM SHALL report PASS for protocol.name and protocol.version
Verification: ✅

CAPS-DIFF-006
WHEN both adapters parse complete_static_example.json
THE SYSTEM SHALL report DIVERGE for lens.pinholeFocalLength, with the Python
adapter value exposed as null and the C++ adapter value exposed as 24.305
Verification: ✅

CAPS-DIFF-007
WHEN both adapters parse complete_static_example.json
THE SYSTEM SHALL report PASS for lens.focusDistance
Verification: ✅

CAPS-REPORT-001
WHEN the runner completes a fixture
THE SYSTEM SHALL write a per-field table to the report file showing field name,
each adapter's value, and a verdict of PASS, DIVERGE, or MISSING for every field
Verification: ✅

CAPS-REPORT-002
WHEN the runner completes all fixtures
THE SYSTEM SHALL write an aggregate row to the report file showing total fields
tested, PASS count, DIVERGE count, and MISSING count
Verification: ✅

CAPS-REPORT-003
WHEN the C++ adapter binary is not found or fails to produce valid JSON
THE SYSTEM SHALL record MISSING as the verdict for that adapter's fields
and continue running rather than exiting
Verification: ✅

CAPS-REPORT-004
WHEN the runner is invoked on a given calendar day
THE SYSTEM SHALL write the report to a file named battery-tester-YYYY-MM-DD-N.txt
where N is a sequential integer starting at 1 and incrementing by 1 for each
subsequent run on the same day, such that up to 10 runs on the same day produce
distinct filenames battery-tester-YYYY-MM-DD-1.txt through
battery-tester-YYYY-MM-DD-10.txt
Verification: ✅

CAPS-GEN-001
WHEN generate_fixtures.py is run
THE SYSTEM SHALL write at least 50 valid OpenTrackIO v1.0.1 JSON fixture files
to fixtures/generated/, each parseable by both adapters without error
Verification: ✅

CAPS-GEN-002
WHEN generate_fixtures.py is run
THE SYSTEM SHALL produce fixtures that cover boundary values (zero, minimum,
maximum, and at least one mid-range value) for each numeric comparison field,
and at least one fixture where each optional comparison field is absent
Verification: ✅

CAPS-GEN-003
WHEN run.py is invoked with --generated
THE SYSTEM SHALL run both adapters against every file in fixtures/generated/
and include all results in the report aggregate
Verification: ✅

CAPS-PROP-001
WHEN compare_samples() is called with Hypothesis-generated adapter output
covering all verdict cases
THE SYSTEM SHALL produce PASS when both values agree, DIVERGE when values
disagree or one side is null, and MISSING when both sides are null
Verification: ✅

CAPS-PROP-002
WHEN compare_samples() is called across a Hypothesis-generated set of fixture
results
THE SYSTEM SHALL produce aggregate counts where pass + diverge + missing equals
fixtures × fields for every generated combination
Verification: ✅
