#!/usr/bin/env python3
"""
adapters/lean_adapter.py
Lean proof-backed oracle adapter for battery-tester.

Converts a JSON fixture to a Lean JsonValue literal, writes a temporary runner
that imports HarnessAdapter, and executes:

  lake env lean --run <runner>.lean

from the opentrackio-proof project root. Parses TSV output into a normalized
JSON dict and prints it to stdout.

Boundaries:
- Python parses fixture JSON bytes (json.load).
- Lean operates on the JsonValue AST, not raw JSON bytes.
- Lean does not verify byte-level JSON parsing.
- Numeric literal spelling preservation is not guaranteed (json.load may alter it).
- Native lake exe is not used; lake env lean --run is the execution path.
"""

import json
import subprocess
import sys
import tempfile
from pathlib import Path

_LEAN_ROOT = Path(__file__).resolve().parents[2]   # opentrackio-proof/


# ---------------------------------------------------------------------------
# Python JSON → Lean JsonValue literal
# ---------------------------------------------------------------------------

def _escape_lean_str(s: str) -> str:
    """Escape a Python string for embedding in a Lean string literal."""
    return (
        s.replace("\\", "\\\\")
         .replace('"', '\\"')
         .replace("\n", "\\n")
         .replace("\r", "\\r")
         .replace("\t", "\\t")
    )


def _py_to_lean(v) -> str:
    """Recursively convert a Python JSON value to a Lean JsonValue literal."""
    if v is None:
        return ".null"
    if isinstance(v, bool):
        return ".bool true" if v else ".bool false"
    if isinstance(v, str):
        return f'.string "{_escape_lean_str(v)}"'
    if isinstance(v, int):
        return f'.number "{v}"'
    if isinstance(v, float):
        return f'.number "{repr(v)}"'
    if isinstance(v, list):
        items = ", ".join(_py_to_lean(item) for item in v)
        return f".array [{items}]"
    if isinstance(v, dict):
        pairs = ", ".join(
            f'("{_escape_lean_str(k)}", {_py_to_lean(val)})'
            for k, val in v.items()
        )
        return f".object [{pairs}]"
    return ".null"


# ---------------------------------------------------------------------------
# TSV output → Python dict
# ---------------------------------------------------------------------------

def _parse_tsv(output: str) -> dict:
    """
    Parse HarnessAdapter TSV output (field<TAB>value lines) into a dict.

    Type coercions:
      "null"       → None
      "num/den"    → float (rational)
      "<integer>"  → int
      "<float>"    → float
      otherwise    → str
    """
    result = {}
    for line in output.strip().splitlines():
        if "\t" not in line:
            continue
        field, _, value = line.partition("\t")
        field = field.strip()
        value = value.strip()

        if value == "null":
            result[field] = None
        elif "/" in value:
            # Try rational "num/den"
            try:
                num_s, den_s = value.split("/", 1)
                result[field] = int(num_s) / int(den_s)
            except (ValueError, ZeroDivisionError):
                result[field] = value
        else:
            try:
                result[field] = int(value)
            except ValueError:
                try:
                    result[field] = float(value)
                except ValueError:
                    result[field] = value

    return result


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    if len(sys.argv) < 2:
        print("Usage: lean_adapter.py <fixture.json>", file=sys.stderr)
        sys.exit(1)

    fixture_path = Path(sys.argv[1])
    if not fixture_path.exists():
        print(f"Fixture not found: {fixture_path}", file=sys.stderr)
        sys.exit(1)

    # Load fixture JSON with Python's parser
    try:
        with open(fixture_path) as fh:
            fixture_data = json.load(fh)
    except (json.JSONDecodeError, OSError) as exc:
        print(f"Failed to load fixture: {exc}", file=sys.stderr)
        sys.exit(1)

    lean_literal = _py_to_lean(fixture_data)

    runner_src = (
        "import HarnessAdapter\n\n"
        f"def fixture : JsonValue :=\n  {lean_literal}\n\n"
        "def main : IO Unit :=\n"
        "  IO.println (renderComparisonFields fixture)\n"
    )

    tmp_path = None
    try:
        with tempfile.NamedTemporaryFile(
            suffix=".lean", mode="w", delete=False
        ) as tmp:
            tmp.write(runner_src)
            tmp_path = Path(tmp.name)

        result = subprocess.run(
            ["lake", "env", "lean", "--run", str(tmp_path)],
            capture_output=True,
            text=True,
            timeout=120,
            cwd=_LEAN_ROOT,
        )
    except FileNotFoundError:
        print("lake not found in PATH", file=sys.stderr)
        sys.exit(1)
    except subprocess.TimeoutExpired:
        print("Lean runner timed out", file=sys.stderr)
        sys.exit(1)
    finally:
        if tmp_path is not None:
            try:
                tmp_path.unlink(missing_ok=True)
            except Exception:
                pass

    if result.returncode != 0:
        print(f"Lean runner failed (exit {result.returncode}):\n{result.stderr}",
              file=sys.stderr)
        sys.exit(1)

    out = _parse_tsv(result.stdout)
    print(json.dumps(out))


if __name__ == "__main__":
    main()
