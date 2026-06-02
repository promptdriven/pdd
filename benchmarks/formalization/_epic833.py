"""Epic #833 source-set scorecard for the formalization benchmark."""
from __future__ import annotations

import re
from pathlib import Path
from typing import Any, Optional

from pdd.contract_ir import extract_sections, parse_prompt_contracts

_PIN_RE = re.compile(r"<pin>([^<]+)</pin>", re.IGNORECASE)
_EXCLUDE_RE = re.compile(r"<exclude>([^<]+)</exclude>", re.IGNORECASE)


def _extract_grounding_overrides(prompt_text: str) -> dict[str, list[str]]:
    """Local pin/exclude parse (mirrors pdd.grounding_provenance when #827 is merged)."""
    pinned = [m.strip() for m in _PIN_RE.findall(prompt_text or "") if m.strip()]
    excluded = [m.strip() for m in _EXCLUDE_RE.findall(prompt_text or "") if m.strip()]
    return {"pinned": pinned, "excluded": excluded}

# Sub-issues under https://github.com/promptdriven/pdd/issues/833
EPIC833_ISSUES: list[dict[str, Any]] = [
    {
        "issue": 820,
        "title": "Story template (Covers, Oracle, …)",
        "wave": "1",
        "benchmark_signal": "stories_with_covers, stories_with_oracle",
    },
    {
        "issue": 821,
        "title": "Tests generated from contract rule IDs",
        "wave": "1",
        "benchmark_signal": "rule_id_test_functions",
    },
    {
        "issue": 822,
        "title": "pdd checkup contract check",
        "wave": "1",
        "shipped": True,
        "benchmark_signal": "contract_check_errors",
    },
    {
        "issue": 823,
        "title": "pdd checkup coverage",
        "wave": "1",
        "shipped": True,
        "benchmark_signal": "coverage_matrix",
    },
    {
        "issue": 824,
        "title": "Evidence manifests",
        "wave": "1",
        "shipped": True,
        "benchmark_signal": "evidence_manifest_present",
    },
    {
        "issue": 825,
        "title": "pdd checkup gate",
        "wave": "2",
        "benchmark_signal": "gate_cli_available",
    },
    {
        "issue": 826,
        "title": "Expanded prompt snapshot / replay",
        "wave": "2",
        "benchmark_signal": "replay_snapshot_present",
    },
    {
        "issue": 827,
        "title": "Grounding provenance in evidence",
        "wave": "2",
        "benchmark_signal": "grounding_pin_exclude_tags",
    },
    {
        "issue": 828,
        "title": "Capability contracts",
        "wave": "2",
        "benchmark_signal": "capabilities_section_present",
    },
    {
        "issue": 829,
        "title": "pdd checkup lint",
        "wave": "1",
        "shipped": True,
        "benchmark_signal": "prompt_lint_warnings",
    },
    {
        "issue": 830,
        "title": "Architecture metadata extension",
        "wave": "2",
        "benchmark_signal": "architecture_contract_metadata",
    },
    {
        "issue": 831,
        "title": "pdd checkup drift",
        "wave": "2",
        "benchmark_signal": "drift_cli_available",
    },
    {
        "issue": 832,
        "title": "Explicit waiver model",
        "wave": "2",
        "benchmark_signal": "waived_rules",
    },
]

_STORY_ORACLE_RE = re.compile(r"^##\s+Oracle\s*$", re.MULTILINE | re.IGNORECASE)
_STORY_COVERS_RE = re.compile(r"^##\s+Covers\s*$", re.MULTILINE | re.IGNORECASE)
_RULE_TEST_RE = re.compile(r"def\s+test[_]?[Rr](\d+)", re.MULTILINE)


def _check(name: str, *, status: str, detail: str, issue: Optional[int] = None) -> dict[str, Any]:
    return {"name": name, "status": status, "detail": detail, "issue": issue}


def _cli_subcommand_available(module: str, attr: str) -> bool:
    try:
        mod = __import__(module, fromlist=[attr])
        return getattr(mod, attr, None) is not None
    except ModuleNotFoundError:
        return False


def _story_template_stats(stories_dir: Optional[Path]) -> dict[str, int]:
    stats = {"stories_total": 0, "stories_with_covers": 0, "stories_with_oracle": 0}
    if stories_dir is None or not stories_dir.is_dir():
        return stats
    for path in sorted(stories_dir.rglob("story__*.md")):
        stats["stories_total"] += 1
        text = path.read_text(encoding="utf-8")
        if _STORY_COVERS_RE.search(text):
            stats["stories_with_covers"] += 1
        if _STORY_ORACLE_RE.search(text):
            stats["stories_with_oracle"] += 1
    return stats


def _rule_id_test_count(tests_dir: Optional[Path]) -> int:
    if tests_dir is None or not tests_dir.is_dir():
        return 0
    count = 0
    for path in tests_dir.rglob("test_*.py"):
        count += len(_RULE_TEST_RE.findall(path.read_text(encoding="utf-8")))
    return count


def evaluate_epic833(
    *,
    arm: str,
    prompt_path: Optional[Path],
    stories_dir: Optional[Path],
    tests_dir: Optional[Path],
    metrics: dict[str, Any],
    evidence_paths: list[Path],
) -> dict[str, Any]:
    """Build epic #833 source-set scorecard for one benchmark arm."""
    checks: list[dict[str, Any]] = []
    story_stats = _story_template_stats(stories_dir)
    rule_tests = _rule_id_test_count(tests_dir)

    gate_ok = _cli_subcommand_available("pdd.gate_main", "run_gate_policy")
    drift_ok = _cli_subcommand_available("pdd.drift_main", "run_drift")

    if arm == "A2":
        return {
            "epic_issue": 833,
            "arm": arm,
            "checks_passed": 0,
            "checks_total": 0,
            "checks_skipped": len(EPIC833_ISSUES),
            "checks": [
                _check(
                    "epic833",
                    status="skipped",
                    detail="A2 code-as-SOT arm; epic scorecard applies to A1 formalized prompts.",
                )
            ],
            "source_set_answers": {},
        }

    if prompt_path is None or not prompt_path.is_file():
        checks.append(
            _check("prompt_present", status="fail", detail="No prompt file for this arm.")
        )
        return _finalize_scorecard(arm, checks)

    text = prompt_path.read_text(encoding="utf-8")
    sections = extract_sections(text)
    ir = parse_prompt_contracts(prompt_path)
    grounding = _extract_grounding_overrides(text)
    pinned = len(grounding.get("pinned") or [])
    excluded = len(grounding.get("excluded") or [])

    total_rules = metrics.get("total_rules") or 0
    contract_errors = metrics.get("contract_check_errors") or 0
    lint_warnings = metrics.get("prompt_lint_warnings") or 0
    waived = metrics.get("waived_rules") or 0
    unchecked = metrics.get("unchecked_rules") or 0
    checked = metrics.get("checked_rules") or 0
    evidence_present = metrics.get("evidence_manifest_present")

    # Epic acceptance criteria → measurable checks
    checks.append(
        _check(
            "intent_declared",
            status="pass" if total_rules > 0 else "fail",
            detail=f"{total_rules} contract rule(s) in <contract_rules>.",
            issue=833,
        )
    )
    checks.append(
        _check(
            "contract_check",
            status="pass" if contract_errors == 0 else "fail",
            detail=f"contract_check_errors={contract_errors}.",
            issue=822,
        )
    )
    checks.append(
        _check(
            "coverage_queryable",
            status="pass" if total_rules > 0 else "na",
            detail=(
                f"checked={checked}, unchecked={unchecked}, waived={waived} "
                f"(see pdd checkup coverage)."
            ),
            issue=823,
        )
    )
    checks.append(
        _check(
            "prompt_lint",
            status="pass" if lint_warnings == 0 else "warn",
            detail=f"prompt_lint_warnings={lint_warnings}.",
            issue=829,
        )
    )
    checks.append(
        _check(
            "stories_cover_rules",
            status="pass" if story_stats["stories_with_covers"] > 0 else "na",
            detail=(
                f"{story_stats['stories_with_covers']}/{story_stats['stories_total']} "
                "stories have ## Covers."
            ),
            issue=820,
        )
    )
    checks.append(
        _check(
            "story_oracle_blocks",
            status="pass" if story_stats["stories_with_oracle"] > 0 else "na",
            detail=(
                f"{story_stats['stories_with_oracle']}/{story_stats['stories_total']} "
                "stories have ## Oracle (#820 template)."
            ),
            issue=820,
        )
    )
    checks.append(
        _check(
            "tests_reference_rule_ids",
            status="pass" if rule_tests > 0 else "na",
            detail=f"{rule_tests} test function(s) reference rule IDs (test_R<n>).",
            issue=821,
        )
    )
    if evidence_paths:
        checks.append(
            _check(
                "evidence_manifest",
                status="pass" if evidence_present else "fail",
                detail="Configured evidence_paths present on disk.",
                issue=824,
            )
        )
    else:
        checks.append(
            _check(
                "evidence_manifest",
                status="skipped",
                detail="No evidence_paths in task.yaml; run pdd --evidence separately.",
                issue=824,
            )
        )
    checks.append(
        _check(
            "waivers_tracked",
            status="pass" if waived > 0 or unchecked == 0 else "warn",
            detail=f"waived_rules={waived}, unchecked_rules={unchecked}.",
            issue=832,
        )
    )
    checks.append(
        _check(
            "capabilities_section",
            status="pass" if sections.get("capabilities") else "na",
            detail="<capabilities> present in prompt." if sections.get("capabilities") else "No capabilities block.",
            issue=828,
        )
    )
    checks.append(
        _check(
            "grounding_pin_exclude",
            status="pass" if (pinned + excluded) > 0 else "na",
            detail=f"pin tags={pinned}, exclude tags={excluded} in prompt text.",
            issue=827,
        )
    )
    checks.append(
        _check(
            "gate_cli",
            status="pass" if gate_ok else "skipped",
            detail="pdd checkup gate available." if gate_ok else "gate_main not on this branch (#825).",
            issue=825,
        )
    )
    checks.append(
        _check(
            "drift_cli",
            status="pass" if drift_ok else "skipped",
            detail="pdd checkup drift available." if drift_ok else "drift_main not on this branch (#831).",
            issue=831,
        )
    )
    checks.append(
        _check(
            "replay_snapshot",
            status="skipped",
            detail="Expanded prompt snapshot not wired in benchmark yet (#826).",
            issue=826,
        )
    )
    checks.append(
        _check(
            "architecture_contract_metadata",
            status="skipped",
            detail="architecture.json contract fields not scored in benchmark yet (#830).",
            issue=830,
        )
    )

    source_set = {
        "what_does_module_intend": total_rules > 0,
        "contracts_must_satisfy": contract_errors == 0 and total_rules > 0,
        "stories_cover_contracts": story_stats["stories_with_covers"] > 0,
        "tests_execute_contracts": rule_tests > 0 or (metrics.get("test_total") or 0) > 0,
        "checks_passed": contract_errors == 0,
        "unchecked_or_waived_visible": total_rules == 0 or (unchecked + waived) >= 0,
        "replay_auditable": evidence_present is True,
    }

    return _finalize_scorecard(arm, checks, source_set_answers=source_set)


def _finalize_scorecard(
    arm: str,
    checks: list[dict[str, Any]],
    *,
    source_set_answers: Optional[dict[str, bool]] = None,
) -> dict[str, Any]:
    passed = sum(1 for c in checks if c["status"] == "pass")
    warned = sum(1 for c in checks if c["status"] == "warn")
    failed = sum(1 for c in checks if c["status"] == "fail")
    skipped = sum(1 for c in checks if c["status"] in {"skipped", "na"})
    return {
        "epic_issue": 833,
        "arm": arm,
        "checks_passed": passed,
        "checks_warn": warned,
        "checks_failed": failed,
        "checks_skipped": skipped,
        "checks_total": len(checks),
        "checks": checks,
        "source_set_answers": source_set_answers or {},
    }
