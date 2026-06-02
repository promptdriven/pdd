"""v1 summary report and TEF scoring for the formalization benchmark."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Optional

# Traceability + Enforceability + Fidelity (documented in BASELINE.md)
TEF_WEIGHTS = {
    "rule_coverage": 0.30,
    "story_coverage": 0.15,
    "test_pass": 0.25,
    "evidence": 0.10,
    "lint_clean": 0.10,
    "formalization": 0.10,
}
TEF_PENALTY_UNCHECKED = 0.15
TEF_PENALTY_CONTRACT_ERRORS = 0.20


def _metric(run: Optional[dict[str, Any]], key: str) -> Optional[float]:
    if run is None:
        return None
    value = run.get("metrics", {}).get(key)
    if value is None:
        return None
    return float(value)


def compute_tef(run: dict[str, Any]) -> Optional[float]:
    """Compute TEF for one arm run. Returns None when not applicable (e.g. A2)."""
    arm = run.get("arm")
    metrics = run.get("metrics", {})
    if arm == "A2":
        return None

    total_rules = metrics.get("total_rules") or 0
    if total_rules == 0 and arm == "A0":
        # Ad-hoc with no contract_rules: traceability score is ~0
        lint_warn = metrics.get("prompt_lint_warnings") or 0
        lint_part = max(0.0, 1.0 - min(lint_warn, 10) / 10.0)
        return round(lint_part * TEF_WEIGHTS["lint_clean"], 4)

    if total_rules == 0:
        return None

    checked = metrics.get("checked_rules") or 0
    story_only = metrics.get("story_only_rules") or 0
    test_only = metrics.get("test_only_rules") or 0
    unchecked = metrics.get("unchecked_rules") or 0
    contract_errors = metrics.get("contract_check_errors") or 0
    lint_warnings = metrics.get("prompt_lint_warnings") or 0
    test_pass = metrics.get("test_pass_rate")
    evidence = metrics.get("evidence_manifest_present")
    formal_candidates = metrics.get("formal_candidate_rules") or 0

    rule_cov = checked / total_rules
    story_cov = (checked + story_only) / total_rules
    enforce_cov = (checked + test_only) / total_rules

    score = (
        TEF_WEIGHTS["rule_coverage"] * rule_cov
        + TEF_WEIGHTS["story_coverage"] * story_cov
        + TEF_WEIGHTS["test_pass"] * (test_pass if test_pass is not None else enforce_cov)
    )
    if evidence is True:
        score += TEF_WEIGHTS["evidence"]
    score += TEF_WEIGHTS["lint_clean"] * max(0.0, 1.0 - min(lint_warnings, 10) / 10.0)
    score += TEF_WEIGHTS["formalization"] * min(formal_candidates / max(total_rules, 1), 1.0)

    if unchecked > 0:
        score -= TEF_PENALTY_UNCHECKED * (unchecked / total_rules)
    if contract_errors > 0:
        score -= TEF_PENALTY_CONTRACT_ERRORS

    return round(max(0.0, min(1.0, score)), 4)


def _run_by_task_arm(runs: list[dict[str, Any]]) -> dict[str, dict[str, dict[str, Any]]]:
    indexed: dict[str, dict[str, dict[str, Any]]] = {}
    for run in runs:
        indexed.setdefault(run["task_id"], {})[run["arm"]] = run
    return indexed


def _delta(a1: Optional[float], a0: Optional[float]) -> Optional[float]:
    if a1 is None or a0 is None:
        return None
    return round(a1 - a0, 4)


def build_summary(aggregate: dict[str, Any]) -> dict[str, Any]:
    """Build comparison summary from aggregate.json payload."""
    runs = aggregate.get("runs") or []
    indexed = _run_by_task_arm(runs)
    comparisons: list[dict[str, Any]] = []

    for task_id in sorted(indexed):
        arms = indexed[task_id]
        a0 = arms.get("A0")
        a1 = arms.get("A1")
        a2 = arms.get("A2")
        m0 = (a0 or {}).get("metrics", {})
        m1 = (a1 or {}).get("metrics", {})
        epic_a1 = (a1 or {}).get("epic833") or {}
        entry = {
            "task_id": task_id,
            "tef": {
                "A0": compute_tef(a0) if a0 else None,
                "A1": compute_tef(a1) if a1 else None,
                "A2": compute_tef(a2) if a2 else None,
            },
            "epic833_A1": {
                "checks_passed": epic_a1.get("checks_passed"),
                "checks_failed": epic_a1.get("checks_failed"),
                "checks_warn": epic_a1.get("checks_warn"),
                "checks_total": epic_a1.get("checks_total"),
                "source_set_answers": epic_a1.get("source_set_answers", {}),
            },
            "primary_delta_A0_to_A1": {
                "total_rules": _delta(_metric(a1, "total_rules"), _metric(a0, "total_rules")),
                "formal_candidate_rules": _delta(
                    _metric(a1, "formal_candidate_rules"),
                    _metric(a0, "formal_candidate_rules"),
                ),
                "z3_test_count": _delta(_metric(a1, "z3_test_count"), _metric(a0, "z3_test_count")),
                "prompt_lint_warnings": _delta(
                    _metric(a1, "prompt_lint_warnings"),
                    _metric(a0, "prompt_lint_warnings"),
                ),
                "checked_rules": _delta(_metric(a1, "checked_rules"), _metric(a0, "checked_rules")),
                "unchecked_rules": _delta(
                    _metric(a1, "unchecked_rules"),
                    _metric(a0, "unchecked_rules"),
                ),
                "tef": _delta(
                    compute_tef(a1) if a1 else None,
                    compute_tef(a0) if a0 else None,
                ),
            },
            "arms": {
                "A0": _arm_snapshot(a0),
                "A1": _arm_snapshot(a1),
                "A2": _arm_snapshot(a2),
            },
        }
        comparisons.append(entry)

    return {
        "benchmark_version": aggregate.get("benchmark_version", "0.2.0"),
        "collected_at": aggregate.get("collected_at"),
        "task_ids": aggregate.get("task_ids", []),
        "tef_weights": TEF_WEIGHTS,
        "comparisons": comparisons,
        "headline": _headline(comparisons),
    }


def _arm_snapshot(run: Optional[dict[str, Any]]) -> Optional[dict[str, Any]]:
    if run is None:
        return None
    m = run.get("metrics", {})
    return {
        "command_success": run.get("command_success"),
        "tef": compute_tef(run),
        "total_rules": m.get("total_rules"),
        "checked_rules": m.get("checked_rules"),
        "unchecked_rules": m.get("unchecked_rules"),
        "prompt_lint_warnings": m.get("prompt_lint_warnings"),
        "formal_candidate_rules": m.get("formal_candidate_rules"),
        "z3_test_count": m.get("z3_test_count"),
        "test_pass_rate": m.get("test_pass_rate"),
        "test_total": m.get("test_total"),
    }


def _headline(comparisons: list[dict[str, Any]]) -> str:
    parts: list[str] = []
    for comp in comparisons:
        delta = comp["primary_delta_A0_to_A1"]
        rules = delta.get("total_rules")
        tef = delta.get("tef")
        if rules is not None and rules > 0:
            parts.append(f"{comp['task_id']}: +{int(rules)} contract rules (A0→A1)")
        elif delta.get("prompt_lint_warnings") is not None:
            lint_d = delta.get("prompt_lint_warnings")
            if lint_d is not None and lint_d < 0:
                parts.append(f"{comp['task_id']}: {int(lint_d)} fewer lint warnings (A0→A1)")
        if tef is not None and tef > 0:
            parts.append(f"TEF +{tef:.2f}")
    if not parts:
        return "Run benchmark with A0 and A1 arms to populate comparison deltas."
    return "; ".join(parts)


def format_report_markdown(summary: dict[str, Any]) -> str:
    """Render a human-readable markdown comparison table."""
    lines = [
        "# PDD formalization benchmark report",
        "",
        f"**Headline:** {summary.get('headline', '')}",
        "",
        "## Per-task comparison (A0 ad-hoc → A1 formalized)",
        "",
        "| Task | TEF A0 | TEF A1 | Δ rules | Δ formal | Δ Z3 | Δ lint warn | "
        "Δ unchecked | Tests A1 |",
        "|------|--------|--------|---------|----------|------|-------------|"
        "-------------|----------|",
    ]
    for comp in summary.get("comparisons", []):
        d = comp["primary_delta_A0_to_A1"]
        a1 = comp["arms"].get("A1") or {}
        lines.append(
            f"| {comp['task_id']} "
            f"| {_fmt(comp['tef'].get('A0'))} "
            f"| {_fmt(comp['tef'].get('A1'))} "
            f"| {_fmt(d.get('total_rules'))} "
            f"| {_fmt(d.get('formal_candidate_rules'))} "
            f"| {_fmt(d.get('z3_test_count'))} "
            f"| {_fmt(d.get('prompt_lint_warnings'))} "
            f"| {_fmt(d.get('unchecked_rules'))} "
            f"| {_fmt_test(a1)} |"
        )
    lines.extend(
        [
            "",
            "## Epic #833 scorecard (A1 formalized arms)",
            "",
            "| Task | Epic checks pass | Epic warn | Epic fail | Source-set OK |",
            "|------|------------------|-----------|-----------|---------------|",
        ]
    )
    for comp in summary.get("comparisons", []):
        epic = comp.get("epic833_A1") or {}
        answers = epic.get("source_set_answers") or {}
        ok_count = sum(1 for v in answers.values() if v)
        ok_total = len(answers)
        lines.append(
            f"| {comp['task_id']} "
            f"| {epic.get('checks_passed', '—')}/{epic.get('checks_total', '—')} "
            f"| {epic.get('checks_warn', '—')} "
            f"| {epic.get('checks_failed', '—')} "
            f"| {ok_count}/{ok_total} |"
        )
    lines.extend(
        [
            "",
            "Detail: `jq '.epic833' results/<task>/A1.json`. See [EPIC833.md](EPIC833.md).",
            "",
            "## Arm snapshots",
            "",
            "See `summary.json` for full metrics. TEF weights are in [BASELINE.md](BASELINE.md).",
            "",
            "### Manual follow-ups (not auto-run)",
            "",
            "- **#825 Gate:** `pdd checkup gate --policy .pdd/policy.yml`",
            "- **#831 Drift:** `pdd checkup drift <devunit> --runs 3`",
            "- **#827 Grounding:** run `pdd generate --evidence` with cloud grounding",
            "- **Lean/SMT:** optional calibration tasks",
            "",
        ]
    )
    return "\n".join(lines)


def _fmt(value: Any) -> str:
    if value is None:
        return "—"
    if isinstance(value, float):
        return f"{value:.2f}" if value != int(value) else str(int(value))
    return str(value)


def _fmt_test(arm: dict[str, Any]) -> str:
    rate = arm.get("test_pass_rate")
    total = arm.get("test_total")
    if rate is None:
        return "—"
    if total is not None and total > 0:
        return f"{rate:.0%} ({total})"
    return f"{rate:.0%}"


def write_summary_artifacts(
    aggregate: dict[str, Any],
    results_dir: Path,
    *,
    print_report: bool = True,
) -> dict[str, Any]:
    """Write summary.json and REPORT.md under results_dir."""
    summary = build_summary(aggregate)
    results_dir.mkdir(parents=True, exist_ok=True)
    summary_path = results_dir / "summary.json"
    summary_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    report_md = format_report_markdown(summary)
    report_path = results_dir / "REPORT.md"
    report_path.write_text(report_md, encoding="utf-8")
    if print_report:
        print(report_md)
    return summary


def load_aggregate(results_dir: Path) -> dict[str, Any]:
    path = results_dir / "aggregate.json"
    if not path.is_file():
        raise FileNotFoundError(f"No aggregate at {path}; run the benchmark first.")
    return json.loads(path.read_text(encoding="utf-8"))
