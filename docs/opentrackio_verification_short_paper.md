# Proof-Backed Interoperability for OpenTrackIO

## A practical formal verification effort for camera-tracking metadata

Virtual production systems depend on accurate, interoperable exchange of camera metadata. A camera-tracking sample may contain timing information, lens settings, transforms, sensor data, protocol versioning, and identifiers. If two implementations interpret the same JSON sample differently, the result may not be a loud crash. It may be a subtle shift in lens projection, focal length, frame timing, or camera transform. Those are exactly the kinds of bugs that are expensive to diagnose on a stage.

This project applies Lean 4 formal verification to OpenTrackIO, an open protocol for camera-tracking metadata. The goal was not to prove every byte-level detail of JSON parsing. Instead, the goal was to formally model the OpenTrackIO v1.0.1 data model, write verified decoders and encoders over an already-parsed JSON abstract syntax tree, and prove that important structural invariants and roundtrip guarantees hold.

The result is a proof-backed OpenTrackIO model that supports three practical uses:

1. It defines what well-formed OpenTrackIO data means at the semantic level.
2. It proves that encoding and then decoding a modeled sample returns the original sample.
3. It provides an executable Lean oracle that can be used in differential testing against production Python and C++ implementations.

This work is aimed at the engineering boundary where formal methods are most useful: catching protocol ambiguities, key-name drift, missing-field behavior, and cross-language interpretation bugs.

## Why formal verification was useful here

OpenTrackIO is a protocol, not just a library. That means the central risk is not only whether one implementation works in isolation. The larger risk is whether independent implementations agree on what a sample means.

Many protocol bugs are mundane but serious: a field has the wrong key name, a missing required field is silently accepted, a version array has the wrong shape, a denominator is allowed to be zero, or a list that must be nonempty is accepted as empty. These problems often escape ordinary unit tests because each individual implementation may appear internally consistent.

The project therefore focused on conformance properties rather than trying to prove a specific production parser implementation correct. The Lean model acts as a precise reference point: it says what the protocol data model accepts, how it encodes values, and which invariants are guaranteed after decoding.

A concrete example illustrates the value. The differential harness for this repository compares a Python camdkit adapter and a Mo-Sys C++ adapter across 18 OpenTrackIO fields. It exposed a real key-name bug: the Python adapter read `lens.focalLength`, while the normative OpenTrackIO field is `lens.pinholeFocalLength`. The Lean model uses the normative key. When added as a third oracle, it independently confirms which implementation matches the protocol model.

This is the practical payoff of formalization: the proof-backed model does not merely say “some parser works.” It helps identify which interpretation of the protocol is correct when implementations disagree.

## What was modeled

The parser verification project models the OpenTrackIO v1.0.1 sample data model over a formal `JsonValue` abstract syntax tree. That means the Lean code assumes JSON text has already been parsed into a structured representation consisting of nulls, booleans, strings, numbers, arrays, and objects. The project does not attempt to verify a byte-level JSON parser.

Within that boundary, the model includes the major OpenTrackIO sample structures:

- protocol name and version;
- rational values such as frame rates;
- timing enums and PTP-related enums;
- transforms with translation and Euler pan/tilt/roll rotation;
- camera metadata;
- lens metadata, including distortion arrays and encoder groups;
- static sample metadata;
- timing, synchronization, and timecode structures;
- top-level sample fields;
- sample encoders, decoders, normalization, and executable harnesses.

Reusable invariant-carrying types — positive rationals, nonempty arrays, nonempty strings, finite version digits, and lens encoder groups with at least one of focus, iris, or zoom present — are defined first, then composed into camera, lens, timing, transform, and sample models.

## Type-carried invariants

One of the most important design choices was to put many protocol invariants directly into Lean types.

For example, a `PositiveRational` value does not merely contain a numerator and denominator. It also carries proofs that the numerator and denominator are positive. A `NonemptyArray` carries a proof that its list of values is not empty. A `NonemptyString` carries a proof that its string is not `""`. A protocol version digit is represented as `Fin 10`, meaning it is impossible to construct a digit outside the range 0 through 9.

This style can make later proofs look surprisingly short. For instance, once a transform id has type `Option NonemptyString`, proving that a present id is nonempty is immediate: the proof is already stored in the value. That is not a vacuous proof. The real enforcement happened earlier, at the decoder boundary, where the decoder could only construct a `NonemptyString` after checking that the JSON string was nonempty.

This pattern appears throughout the project. The decoder is the gatekeeper. If a value passes through the decoder, its type already records important facts about it. That removes the need for fragile proof scripts that repeatedly inspect the internal logic of large decoders.

## Key theorems

The strongest theorem in the parser work is the sample encode/decode roundtrip:

```lean
theorem encodeSample_roundtrip (s : Sample) :
    decodeSample (encodeSample s) = .ok s
```

In ordinary engineering terms, this says: for any OpenTrackIO sample that can be constructed in the formal model, if we encode it to JSON and then decode it, we get the same sample back.

This theorem is difficult to fake. A constant encoder would fail for populated samples. A decoder that ignored fields would fail to recover the original value. A key-name mismatch, such as encoding `pinholeFocalLength` but decoding `focalLength`, would break the theorem.

The project also proves several composed decoder soundness properties. These show that decoded samples preserve structural invariants such as:

- transform arrays are nonempty when present;
- protocol version digits are valid;
- lens encoder groups have at least one of focus, iris, or zoom;
- static duration and camera frame-rate rationals are positive.

Error-correctness theorems cover specific required-field failures. For example, missing `protocol.name`, missing `protocol.version`, missing transform `translation`, missing transform `rotation`, and missing rational `num` are proved to return the expected missing-field error tags. These are limited but useful rejection guarantees: they show that the decoder does not silently accept those malformed inputs.

Closed-world enum decoders were also proved for timing mode, synchronization source, PTP profile, and PTP leader time source. Unknown enum strings are rejected, and accepted enum strings roundtrip through their renderers.

Finally, normalization theorems establish that sample normalization is idempotent and preserves decoded semantics. The project also defines a `WellFormedSampleJson` predicate to describe schema-clean JSON inputs, including duplicate-key and nested unknown-field constraints.

## Proof Strength

Key invariants are stored in types, not in vague predicates — invalid values often cannot be constructed at all. Decoders were tested on representative inputs, confirming they have successful paths. The roundtrip theorem directly exercises both the real encoder and the real decoder, proving agreement between executable functions rather than a hand-written predicate: a constant encoder fails for populated samples, a decoder that ignores fields fails to recover the original value, and a key-name mismatch breaks the theorem.

Some components, such as the sample model shell and executable harness, are useful infrastructure but not deep semantic proofs. The strongest semantic artifacts are the encode/decode roundtrip theorem, error-correctness theorems, closed enum decoders, and type-carried invariants enforced by decoders.

## Executable harness and differential testing

Formal proofs are most useful when they connect to ordinary engineering workflows. This project includes an executable Lean harness that runs representative checks over the verified components. It is run through Lean’s Lake environment rather than as a native executable, because native `lake exe` linking was deferred due to a local Lean 4.29.0 / Darwin 25.3.0 linker incompatibility.

The repository also includes `battery-tester`, a differential test harness. It runs a Python adapter, a C++ adapter, and optionally the Lean oracle against the same canonical JSON fixtures. It compares 18 fields field-by-field. This bridges the formal model to production implementation behavior.

The Lean adapter is intentionally AST-level. Python still parses fixture JSON bytes, then converts the parsed data into Lean’s `JsonValue` model. This means the Lean oracle does not verify byte-level JSON parsing. It verifies the semantic interpretation of the already-parsed OpenTrackIO data.

That boundary is deliberate. It allows the Lean work to provide value immediately: when Python and C++ disagree, the Lean oracle can show which behavior matches the formal protocol model.

## What is not proved

The project is not a verified JSON parser. It does not prove byte-level parsing correctness. It does not prove every numeric upper bound in the OpenTrackIO schema. Many values are stored as raw strings after being recognized as JSON numbers or integers. Regex-like constraints, such as UUID URNs and PTP leader identities, are not fully verified. Maximum string lengths are also deferred.

Duplicate-key behavior is modeled through well-formedness predicates, but `decodeSample` itself does not reject duplicate keys; raw object lookup takes the first matching key. Unknown top-level fields are allowed by the extension policy, while unknown nested fields are handled through `WellFormedSampleJson` rather than by retrofitting all completed decoders.

Lens distortion mathematical correctness and OpenCV ↔ OpenTrackIO conversion correctness are handled separately in the repository’s conversion theorem project. The parser verification proves data-model, decoder, encoder, roundtrip, and normalization properties, not every downstream mathematical use of the decoded data.

These limitations are important. They define the actual proof boundary and prevent the work from being oversold.

## Conclusion

The OpenTrackIO parser verification work is best understood as proof-backed interoperability infrastructure. It gives the protocol a precise executable model, proves important structural invariants, proves encode/decode roundtrip for the full sample model, and connects that model to differential testing against real implementations.

For engineers who do not use formal methods day to day, the practical result is this: the Lean model acts as a trustworthy reference implementation for the semantic shape of OpenTrackIO samples. It can catch wrong key names, missing required-field behavior, invalid structural states, and encoder/decoder disagreement. It does not replace conventional tests or production parsers, but it strengthens them by providing a formally checked oracle.

That is the main value of the work. It turns protocol assumptions into executable, checked claims, and then uses those claims to improve the reliability of real OpenTrackIO implementations.

