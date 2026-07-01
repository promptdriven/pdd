"""
Example usage of pdd.agentic_reviewer.run_agentic_reviewer

Demonstrates:
  - How to call run_agentic_reviewer with contract effects and artifact paths
  - The structure of the returned findings list
  - Using bounds to limit file traversal
  - The insufficient-evidence sentinel returned when no local evidence is found
  - Classifier failures returning no agentic findings
  - Helper functions: _detect_language, _extract_symbols, _inspect_manifests,
    _build_classifier_input, _extract_last_json, _resolve_local_import

All external dependencies (llm_invoke) are mocked so this example runs
standalone without API keys.
"""
from __future__ import annotations

import json
import os
import sys
import tempfile
import types
from pathlib import Path
from unittest.mock import MagicMock, patch

# Allow import from project root regardless of working directory
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

# ---------------------------------------------------------------------------
# Mock llm_invoke before importing the module so no real LLM call is made
# ---------------------------------------------------------------------------

_MOCK_LLM_RESULT = [
    {
        "action": "write",
        "resource": "filesystem",
        "judgment": "likely_violation",
        "confidence": 0.85,
        "message": "File write detected; contract prohibits filesystem writes.",
    }
]

_mock_llm_invoke = MagicMock(return_value={"result": _MOCK_LLM_RESULT, "cost": 0.0, "model_name": "mock"})

# Patch at the module level before import
import unittest.mock as _mock

with _mock.patch.dict("sys.modules", {"pdd.llm_invoke": types.ModuleType("pdd.llm_invoke")}):
    pass  # pre-seed for patch below

from pdd.agentic_reviewer import (
    run_agentic_reviewer,
    _detect_language,
    _extract_symbols,
    _inspect_manifests,
    _build_classifier_input,
    _extract_last_json,
    _resolve_local_import,
)


def demo_detect_language() -> None:
    """Demonstrate _detect_language() — maps file extension to language string."""
    print("=== _detect_language ===")
    test_cases = [
        ("script.py", "python"),
        ("app.ts", "typescript"),
        ("app.tsx", "typescript"),
        ("index.js", "javascript"),
        ("data.csv", "unknown"),
    ]
    for filename, expected in test_cases:
        result = _detect_language(Path(filename))
        status = "OK" if result == expected else "FAIL"
        print(f"  [{status}] {filename!r} -> {result!r}")
    print()


def demo_extract_symbols() -> None:
    """Demonstrate _extract_symbols() — regex-based symbol extraction."""
    print("=== _extract_symbols ===")
    sample_code = """\
import os
from pathlib import Path
SECRET = os.environ.get("MY_SECRET")
with open("output.txt", "w") as f:
    f.write("hello")
result = requests.get("https://api.example.com/data")
logger.info("done")
"""
    symbols = _extract_symbols(Path("sample.py"), sample_code)
    for sym in symbols:
        print(f"  line {sym['line']:2d} [{sym['kind']:8s}] {sym['symbol']!r}")
    print(f"  Total symbols extracted: {len(symbols)}")
    print()


def demo_inspect_manifests(tmp_dir: Path) -> None:
    """Demonstrate _inspect_manifests() — reads dependency manifest files."""
    print("=== _inspect_manifests ===")

    # Create a requirements.txt
    req_file = tmp_dir / "requirements.txt"
    req_file.write_text("requests==2.31.0\npandas>=1.0\n# comment\n")

    # Create a package.json
    pkg_json = tmp_dir / "package.json"
    pkg_json.write_text(json.dumps({
        "dependencies": {"axios": "^1.0", "express": "^4.18"},
        "devDependencies": {"jest": "^29.0"},
    }))

    result = _inspect_manifests(tmp_dir)
    for manager, deps in result.items():
        print(f"  {manager}: {deps}")
    print()


def demo_build_classifier_input() -> None:
    """Demonstrate _build_classifier_input() — builds LLM classifier payload."""
    print("=== _build_classifier_input ===")
    contract_effects = [{"action": "write", "resource": "filesystem"}]
    observed_evidence = [
        {"file": "app.py", "line": 5, "excerpt": "open('out.txt', 'w')", "kind": "write", "symbol": "open("},
    ]
    result = _build_classifier_input(contract_effects, observed_evidence, "python")
    print(f"  Keys: {list(result.keys())}")
    print(f"  target: {result['target']!r}")
    print(f"  contract_effects count: {len(result['contract_effects'])}")
    print(f"  observed_evidence count: {len(result['observed_evidence'])}")
    print(f"  deterministic_findings: {result['deterministic_findings']}")
    print()


def demo_extract_last_json() -> None:
    """Demonstrate _extract_last_json() — extracts last valid JSON from text."""
    print("=== _extract_last_json ===")

    # Last valid JSON found (iterates forward; dict inside array is encountered last)
    text_with_array = 'Some preamble [{"a": 1}] then [{"b": 2, "c": 3}] trailing'
    result = _extract_last_json(text_with_array)
    print(f"  Last JSON from mixed text: {result}")

    text_with_object = 'Preamble {"key": "value"} more text {"final": true}'
    result2 = _extract_last_json(text_with_object)
    print(f"  Object extraction: {result2}")

    text_no_json = "No JSON here at all."
    result3 = _extract_last_json(text_no_json)
    print(f"  No JSON: {result3}")
    print()


def demo_resolve_local_import(tmp_dir: Path) -> None:
    """Demonstrate _resolve_local_import() — resolves relative import paths."""
    print("=== _resolve_local_import ===")

    # Create a source file and a local module
    src_file = tmp_dir / "app.py"
    src_file.write_text("from ./utils import helper\n")
    utils_file = tmp_dir / "utils.py"
    utils_file.write_text("def helper(): pass\n")

    resolved = _resolve_local_import(src_file, "./utils", tmp_dir)
    print(f"  Resolved './utils' -> {resolved.name if resolved else None}")

    # Test path escape rejection
    escaped = _resolve_local_import(src_file, "../../etc/passwd", tmp_dir)
    print(f"  Escaped path rejected: {escaped is None}")
    print()


def demo_run_agentic_reviewer(tmp_dir: Path) -> None:
    """
    Demonstrate run_agentic_reviewer() — full pipeline with mocked LLM.

    Parameters:
        contract_effects: list of dicts with 'action' and 'resource' keys
        artifact_paths:   list of file paths to inspect
        bounds:           optional dict with max_files, max_follow_depth,
                          max_search_results, max_runtime_seconds

    Returns:
        List[Dict] — each finding has:
          source, severity, confidence, effect (action/resource), message,
          evidence (list of {file, line, excerpt}), agent_steps, judgment
    """
    print("=== run_agentic_reviewer ===")

    # Create a sample Python file with a file write
    target_file = tmp_dir / "service.py"
    target_file.write_text(
        "import os\n"
        "SECRET = os.environ.get('DB_PASSWORD')\n"
        "with open('output.log', 'w') as f:\n"
        "    f.write('started')\n"
    )

    contract_effects = [
        {"action": "write", "resource": "filesystem"},
        {"action": "read", "resource": "env"},
    ]
    bounds = {
        "max_files": 5,
        "max_follow_depth": 1,
        "max_search_results": 20,
        "max_runtime_seconds": 10,
    }

    with patch("pdd.agentic_reviewer.llm_invoke", _mock_llm_invoke):
        findings = run_agentic_reviewer(
            contract_effects=contract_effects,
            artifact_paths=[str(target_file)],
            bounds=bounds,
        )

    print(f"  Number of findings: {len(findings)}")
    for i, finding in enumerate(findings):
        print(f"  Finding {i}:")
        print(f"    source:    {finding.get('source')}")
        print(f"    severity:  {finding.get('severity')}")
        print(f"    judgment:  {finding.get('judgment')}")
        print(f"    confidence:{finding.get('confidence')}")
        print(f"    message:   {finding.get('message')}")
        print(f"    effect:    {finding.get('effect')}")
        print(f"    evidence count: {len(finding.get('evidence', []))}")
        print(f"    agent_steps count: {len(finding.get('agent_steps', []))}")
    print()


def demo_insufficient_evidence_sentinel() -> None:
    """
    Demonstrate that run_agentic_reviewer returns the insufficient-evidence sentinel
    when no symbols are found in target files.
    """
    print("=== Insufficient-evidence sentinel (empty file) ===")

    with tempfile.TemporaryDirectory() as tmp:
        empty_file = Path(tmp) / "empty.py"
        empty_file.write_text("")  # No symbols

        with patch("pdd.agentic_reviewer.llm_invoke", _mock_llm_invoke):
            findings = run_agentic_reviewer(
                contract_effects=[{"action": "write", "resource": "filesystem"}],
                artifact_paths=[str(empty_file)],
            )

    print(f"  Number of findings: {len(findings)}")
    if findings:
        f = findings[0]
        print(f"  judgment:  {f.get('judgment')}")
        print(f"  confidence:{f.get('confidence')}")
        print(f"  source:    {f.get('source')}")
        print(f"  message:   {f.get('message')}")
    print()


def demo_empty_artifact_paths() -> None:
    """Demonstrate that empty artifact_paths returns an empty list (no artifacts inspected)."""
    print("=== Empty artifact_paths ===")
    with patch("pdd.agentic_reviewer.llm_invoke", _mock_llm_invoke):
        findings = run_agentic_reviewer(
            contract_effects=[{"action": "write", "resource": "filesystem"}],
            artifact_paths=[],
        )
    print(f"  findings (expect []): {findings}")
    print()


def main() -> None:
    """Run all demonstrations."""
    print("pdd.agentic_reviewer — Example Usage")
    print("=" * 45)
    print()

    demo_detect_language()
    demo_extract_symbols()
    demo_extract_last_json()
    demo_build_classifier_input()

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        demo_inspect_manifests(tmp_path)
        demo_resolve_local_import(tmp_path)
        demo_run_agentic_reviewer(tmp_path)

    demo_insufficient_evidence_sentinel()
    demo_empty_artifact_paths()

    print("All demonstrations complete.")


if __name__ == "__main__":
    main()
