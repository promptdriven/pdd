#!/usr/bin/env python3
"""Write reports/ab_live.json from environment variables set by live_ab_pipeline.sh."""
from __future__ import annotations

import json
import os
import sys
from pathlib import Path


def _int(name: str, default: int = 0) -> int:
    raw = os.environ.get(name, "")
    if raw == "":
        return default
    return int(raw)


def _opt_int(name: str) -> int | None:
    raw = os.environ.get(name, "")
    if raw == "" or raw == "-1":
        return None
    return int(raw)


def _bool(name: str) -> bool:
    return os.environ.get(name, "0") == "1"


def _derive_verdicts(
    *,
    warn_b: int,
    warn_a: int,
    rule_after: int,
    compile_err: int,
    unchecked_after: int,
    unchecked_before: int | None,
    checked_before: int | None,
    checked_after: int | None,
    rej: int,
    syn_a: bool,
    pyt_a: bool,
    pytest_failed_b: int,
    pytest_failed_a: int,
    golden_b: bool,
    golden_a: bool,
    golden_failed_b: int,
    golden_failed_a: int,
    markers_b: int,
    markers_a: int,
) -> dict:
    """Four separate verdicts — do not collapse prompt/codegen/process layers."""
    spec_instrumented = rule_after > 0 and compile_err == 0

    prompt_improved = (
        warn_a <= warn_b
        and rej == 0
        and spec_instrumented
    )

    contract_linkage_improved = False
    if markers_a < markers_b:
        contract_linkage_improved = True
    elif checked_before is not None and checked_after is not None:
        contract_linkage_improved = checked_after > checked_before
    elif rule_after > 0 and unchecked_after <= rule_after:
        contract_linkage_improved = True

    behavioral_regression = False
    if not syn_a:
        behavioral_regression = True
    elif golden_failed_a > golden_failed_b or (not golden_a and golden_b):
        behavioral_regression = True
    elif pyt_a and pytest_failed_a > pytest_failed_b:
        behavioral_regression = True

    behavioral_exercised = syn_a and (golden_a or pyt_a)
    partial_e2e = not behavioral_exercised

    return {
        "spec_instrumented": spec_instrumented,
        "prompt_improved": prompt_improved,
        "contract_linkage_improved": contract_linkage_improved,
        "behavioral_regression": behavioral_regression,
        "behavioral_exercised": behavioral_exercised,
        "partial_e2e": partial_e2e,
        "behavioral_claim_strength": "single_live_run",
    }


def main() -> int:
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("reports/ab_live.json")

    warn_b = _int("WARN_BEFORE")
    warn_a = _int("WARN_AFTER")
    rule_after = _int("RULE_COUNT_AFTER")
    unchecked_after = _int("UNCHECKED_AFTER")
    unchecked_before = _opt_int("UNCHECKED_BEFORE")
    checked_before = _opt_int("COVERAGE_CHECKED_BEFORE")
    checked_after = _opt_int("COVERAGE_CHECKED_AFTER")
    total_rules_after = _int("COVERAGE_TOTAL_AFTER")
    amb = _int("AMB_COUNT")
    rej = _int("REJ_COUNT")
    compile_err = _int("COMPILE_ERR")
    syn_b = _bool("SYNTAX_BEFORE")
    syn_a = _bool("SYNTAX_AFTER")
    pyt_b = _bool("PYTEST_BEFORE")
    pyt_a = _bool("PYTEST_AFTER")
    golden_b = _bool("GOLDEN_BEFORE")
    golden_a = _bool("GOLDEN_AFTER")
    pytest_passed_b = _int("PYTEST_PASSED_BEFORE")
    pytest_passed_a = _int("PYTEST_PASSED_AFTER")
    pytest_failed_b = _int("PYTEST_FAILED_BEFORE")
    pytest_failed_a = _int("PYTEST_FAILED_AFTER")
    golden_passed_b = _int("GOLDEN_PASSED_BEFORE")
    golden_passed_a = _int("GOLDEN_PASSED_AFTER")
    golden_failed_b = _int("GOLDEN_FAILED_BEFORE")
    golden_failed_a = _int("GOLDEN_FAILED_AFTER")
    markers_b = _int("MARKERS_MISSING_BEFORE")
    markers_a = _int("MARKERS_MISSING_AFTER")

    verdict = _derive_verdicts(
        warn_b=warn_b,
        warn_a=warn_a,
        rule_after=rule_after,
        compile_err=compile_err,
        unchecked_after=unchecked_after,
        unchecked_before=unchecked_before,
        checked_before=checked_before,
        checked_after=checked_after,
        rej=rej,
        syn_a=syn_a,
        pyt_a=pyt_a,
        pytest_failed_b=pytest_failed_b,
        pytest_failed_a=pytest_failed_a,
        golden_b=golden_b,
        golden_a=golden_a,
        golden_failed_b=golden_failed_b,
        golden_failed_a=golden_failed_a,
        markers_b=markers_b,
        markers_a=markers_a,
    )

    payload = {
        "schema": "pdd.ab_report.v1",
        "experiment": "cost_tracker_clarify_sandwich",
        "experiment_question": (
            "Did LLM clarify improve downstream generation/test outcomes "
            "(single pinned live run; not universal codegen proof)?"
        ),
        "controls": {
            "generate_output": os.environ.get("GENERATE_OUTPUT", ""),
            "pdd_version": os.environ.get("PDD_VERSION", ""),
            "model_default": os.environ.get("PDD_MODEL_DEFAULT", ""),
            "preflight_model": os.environ.get("PREFLIGHT_MODEL", ""),
            "golden_test": os.environ.get("GOLDEN_TEST", ""),
        },
        "layers": {
            "prompt": "lint, clarify, compile, coverage on work prompt",
            "codegen_primary": "shared golden tests vs src snapshots",
            "codegen_secondary": "LLM-generated test files + py_compile + pytest",
            "process": "evidence emit/validate, contracts drift",
        },
        "prompt": {
            "pre_clarify_sha256": os.environ.get("SHA_PRE", ""),
            "post_clarify_sha256": os.environ.get("SHA_POST", ""),
        },
        "lint": {"warn_before": warn_b, "warn_after": warn_a},
        "clarify": {
            "ambiguity_count": amb,
            "formalization_rejected_count": rej,
        },
        "contracts": {
            "compile_errors_after": compile_err,
            "rule_count_after": rule_after,
            "unchecked_after": unchecked_after,
            "unchecked_before": unchecked_before,
            "checked_before": checked_before,
            "checked_after": checked_after,
            "total_rules_after": total_rules_after,
            "coverage_measurable": total_rules_after > 0,
        },
        "before": {
            "generate_bytes": _int("GEN_BYTES_BEFORE"),
            "test_bytes": _int("TEST_BYTES_BEFORE"),
            "py_compile_ok": syn_b,
            "golden_pytest": {
                "passed": golden_passed_b,
                "failed": golden_failed_b,
                "exit_ok": golden_b,
            },
            "generated_pytest": {
                "passed": pytest_passed_b,
                "failed": pytest_failed_b,
                "exit_ok": pyt_b,
            },
            "contract_markers_missing": markers_b,
        },
        "after": {
            "generate_bytes": _int("GEN_BYTES_AFTER"),
            "test_bytes": _int("TEST_BYTES_AFTER"),
            "py_compile_ok": syn_a,
            "golden_pytest": {
                "passed": golden_passed_a,
                "failed": golden_failed_a,
                "exit_ok": golden_a,
            },
            "generated_pytest": {
                "passed": pytest_passed_a,
                "failed": pytest_failed_a,
                "exit_ok": pyt_a,
            },
            "contract_markers_missing": markers_a,
        },
        "evidence": {
            "pre": os.environ.get("EVIDENCE_PRE", "reports/evidence_pre_clarify.json"),
            "post": os.environ.get("EVIDENCE_POST", "reports/evidence_post_clarify.json"),
        },
        "drift": {
            "has_drift": os.environ.get("DRIFT_HAS", "false") == "true",
            "finding_count": _int("DRIFT_FINDINGS"),
        },
        "diffs": {
            "prompt_hunks": _int("HUNKS_PROMPT"),
            "src_hunks": _int("HUNKS_SRC"),
            "tests_hunks": _int("HUNKS_TEST"),
        },
        "verdict": verdict,
    }

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"  wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
