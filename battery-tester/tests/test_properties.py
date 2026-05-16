"""
tests/test_properties.py
Hypothesis property tests for battery-tester's comparison logic.
Tests compare_values() and compare_samples() directly — no subprocess calls.
Run with: python -m pytest tests/test_properties.py -v
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from hypothesis import given, settings
from hypothesis import strategies as st

from run import compare_values, compare_samples, COMPARISON_FIELDS, FLOAT_TOLERANCE


# ── Helpers ───────────────────────────────────────────────────────────────────

def _make_samples(py_val, cpp_val):
    """Build a samples dict where every field has the given value per adapter.
    Pass None for an adapter to simulate that adapter failing entirely."""
    py  = {f: py_val  for f in COMPARISON_FIELDS} if py_val  is not None else None
    cpp = {f: cpp_val for f in COMPARISON_FIELDS} if cpp_val is not None else None
    return {"python": py, "cpp-mosys": cpp}


def _count(comparisons):
    p = sum(1 for c in comparisons if c["verdict"] == "PASS")
    d = sum(1 for c in comparisons if c["verdict"] == "DIVERGE")
    m = sum(1 for c in comparisons if c["verdict"] == "MISSING")
    return p, d, m


# ── compare_values invariants ─────────────────────────────────────────────────

@given(v=st.integers(min_value=-10_000_000, max_value=10_000_000))
def test_identical_integers_compare_equal(v):
    assert compare_values(v, v)


@given(v=st.text(min_size=1, max_size=64))
def test_identical_strings_compare_equal(v):
    assert compare_values(v, v)


@given(
    v=st.floats(allow_nan=False, allow_infinity=False, min_value=-1e6, max_value=1e6),
)
def test_identical_floats_compare_equal(v):
    assert compare_values(v, v)


@given(
    a=st.integers(min_value=-10_000, max_value=10_000),
    b=st.integers(min_value=-10_000, max_value=10_000),
)
def test_different_integers_compare_unequal(a, b):
    if a != b:
        assert not compare_values(a, b)


def test_null_always_fails():
    assert not compare_values(None, 1.0)
    assert not compare_values(1.0, None)
    assert not compare_values(None, None)
    assert not compare_values(None, "x")
    assert not compare_values("x", None)


def test_float_tolerance_boundary():
    # Values separated by more than FLOAT_TOLERANCE must not compare equal
    assert not compare_values(0.0, FLOAT_TOLERANCE * 2)
    assert not compare_values(1.0, 1.0 + FLOAT_TOLERANCE * 100)
    assert not compare_values(-1.0, -1.0 + FLOAT_TOLERANCE * 100)
    # Clearly distant values
    assert not compare_values(0.0, 1.0)
    assert not compare_values(1.0, -1.0)


# ── compare_samples verdict invariants ────────────────────────────────────────

@given(v=st.integers(min_value=-10_000, max_value=10_000))
def test_identical_values_all_pass(v):
    comparisons = compare_samples(_make_samples(v, v))
    p, d, m = _count(comparisons)
    assert p == len(COMPARISON_FIELDS)
    assert d == 0
    assert m == 0


@given(
    a=st.integers(min_value=-10_000, max_value=10_000),
    b=st.integers(min_value=-10_000, max_value=10_000),
)
def test_different_values_all_diverge(a, b):
    if a != b:
        comparisons = compare_samples(_make_samples(a, b))
        p, d, m = _count(comparisons)
        assert p == 0
        assert d == len(COMPARISON_FIELDS)
        assert m == 0


def test_one_null_adapter_all_diverge():
    # Python succeeds, C++ adapter binary not found → all DIVERGE
    comparisons = compare_samples(_make_samples(42, None))
    p, d, m = _count(comparisons)
    assert p == 0
    assert d == len(COMPARISON_FIELDS)
    assert m == 0


def test_both_null_adapters_all_missing():
    comparisons = compare_samples({"python": None, "cpp-mosys": None})
    p, d, m = _count(comparisons)
    assert p == 0
    assert d == 0
    assert m == len(COMPARISON_FIELDS)


# ── Aggregate sum invariant (CAPS-PROP-002) ───────────────────────────────────

@given(
    py_val=st.one_of(
        st.none(),
        st.integers(min_value=-1000, max_value=1000),
    ),
    cpp_val=st.one_of(
        st.none(),
        st.integers(min_value=-1000, max_value=1000),
    ),
)
def test_verdict_counts_always_sum_to_total_fields(py_val, cpp_val):
    comparisons = compare_samples(_make_samples(py_val, cpp_val))
    p, d, m = _count(comparisons)
    assert p + d + m == len(COMPARISON_FIELDS)


@given(
    py_val=st.one_of(
        st.none(),
        st.integers(min_value=-1000, max_value=1000),
    ),
    cpp_val=st.one_of(
        st.none(),
        st.integers(min_value=-1000, max_value=1000),
    ),
)
def test_every_verdict_is_valid(py_val, cpp_val):
    comparisons = compare_samples(_make_samples(py_val, cpp_val))
    for c in comparisons:
        assert c["verdict"] in ("PASS", "DIVERGE", "MISSING")


@given(
    fixture_count=st.integers(min_value=1, max_value=50),
    py_val=st.integers(min_value=-1000, max_value=1000),
)
@settings(max_examples=200)
def test_aggregate_sum_across_multiple_fixtures(fixture_count, py_val):
    # Simulate running multiple fixtures with identical values → all PASS
    total_p = total_d = total_m = 0
    for _ in range(fixture_count):
        comparisons = compare_samples(_make_samples(py_val, py_val))
        p, d, m = _count(comparisons)
        total_p += p
        total_d += d
        total_m += m
    assert total_p + total_d + total_m == fixture_count * len(COMPARISON_FIELDS)
    assert total_p == fixture_count * len(COMPARISON_FIELDS)
