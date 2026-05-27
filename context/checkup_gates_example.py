"""Runnable example: PR-Scope Convergence Guard public API for `pdd/checkup_gates.py`.

This example shows the shapes the agentic checkup orchestrator (`pdd checkup --pr`)
expects from the new helpers added in issue promptdriven/pdd#1228. The full
implementation lives in `pdd/checkup_gates.py` and is governed by
`prompts/checkup_gates_python.prompt`.

The five helpers (`parse_step5_signal`, `compute_in_scope_paths`,
`enforce_scope`, `diff_sanity_gate`, `causality_check`) all share the same
contract as the existing review-loop gates (items 22-25 in the prompt):

  * return `[]` (or `None` for the parser) on a clean / unparseable signal.
  * return one or more `ReviewFinding` rows on a violation.
  * NEVER raise — internal IO/parse errors are swallowed and surfaced via the
    return type so the orchestrator can fail open with an advisory finding
    instead of crashing the checkup run.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import (
    Callable,
    Iterable,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
)

# The real module re-uses the existing ReviewFinding from checkup_review_loop.
# This stub is sufficient for the example; the production module imports it
# lazily to avoid a top-of-module cycle.
@dataclass
class ReviewFinding:
    severity: str
    reviewer: str
    area: str
    location: str
    finding: str
    evidence: str
    required_fix: str
    round_number: int = 0
    status: str = "open"

    @property
    def key(self) -> str:
        return f"{self.severity}|{self.location}|{self.finding}|{self.required_fix}"


# ---------------------------------------------------------------------------
# Dataclasses — the structured Step 5 signal the orchestrator surfaces to
# Step 6 (via <step5_signal>) and Step 7 (via <step5_signal> + causality check).
# ---------------------------------------------------------------------------

@dataclass
class Step5Failure:
    nodeid: str
    file: str
    lineno: Optional[int]
    message: str
    traceback_top: str
    category: str  # import_error|assertion|fixture|timeout|config|other


@dataclass
class Step5Signal:
    exit_code: int
    total: int
    passed: int
    failed: int
    skipped: int
    errors: int
    failures: List[Step5Failure] = field(default_factory=list)
    pr_changed_files_used: bool = False
    targeted_scope_used: bool = False

    @property
    def is_clean(self) -> bool:
        """Convenience used by the orchestrator's NO_CHANGES_REQUIRED short-circuit."""
        return self.exit_code == 0 and not self.failures


# ---------------------------------------------------------------------------
# Parser — extract the structured signal from either the Step 5 LLM block or
# the junit-xml the runner was instructed to emit.
# ---------------------------------------------------------------------------

_STEP5_BLOCK_RE = re.compile(
    r"<step5_signal>\s*(\{.*?\})\s*</step5_signal>", re.DOTALL
)


def parse_step5_signal(
    text: str,
    *,
    worktree: Path,
    junit_xml_path: Optional[Path] = None,
) -> Optional[Step5Signal]:
    """Extract a Step5Signal from junit XML or from the Step 5 LLM output.

    Returns None when neither source is parseable. NEVER raises — XML/JSON
    decoding errors are swallowed so the orchestrator can fail open and the
    PR-Scope Convergence Guard records an advisory parse-failure finding
    instead of crashing the checkup pipeline.
    """
    # 1. Preferred path: junit XML (machine-authoritative).
    if junit_xml_path is not None and junit_xml_path.exists():
        try:
            from junitparser import JUnitXml  # local import to keep deps light
            xml = JUnitXml.fromfile(str(junit_xml_path))
            failures: List[Step5Failure] = []
            totals = {"total": 0, "passed": 0, "failed": 0, "skipped": 0, "errors": 0}
            for suite in xml:
                totals["total"] += suite.tests or 0
                totals["failed"] += suite.failures or 0
                totals["skipped"] += suite.skipped or 0
                totals["errors"] += suite.errors or 0
                for case in suite:
                    if case.result and len(failures) < 50:
                        first = case.result[0]
                        failures.append(
                            Step5Failure(
                                nodeid=f"{case.classname}::{case.name}",
                                file=_posix_relative(case.file or "", worktree),
                                lineno=getattr(case, "line", None),
                                message=_truncate(getattr(first, "message", ""), 500),
                                traceback_top=_truncate(
                                    str(getattr(first, "text", "")), 500
                                ),
                                category=_classify_failure(first),
                            )
                        )
            totals["passed"] = max(0, totals["total"] - totals["failed"]
                                   - totals["errors"] - totals["skipped"])
            return Step5Signal(
                exit_code=1 if (totals["failed"] or totals["errors"]) else 0,
                **totals,
                failures=failures,
            )
        except Exception:  # pragma: no cover - fail open per contract
            pass

    # 2. Fallback: the <step5_signal>{...}</step5_signal> LLM block.
    match = _STEP5_BLOCK_RE.search(text or "")
    if not match:
        return None
    try:
        payload = json.loads(match.group(1))
    except json.JSONDecodeError:
        return None

    raw_failures = payload.get("failures", []) or []
    failures = [
        Step5Failure(
            nodeid=str(f.get("nodeid", "")),
            file=_posix_relative(str(f.get("file", "")), worktree),
            lineno=f.get("lineno"),
            message=_truncate(str(f.get("message", "")), 500),
            traceback_top=_truncate(str(f.get("traceback_top", "")), 500),
            category=str(f.get("category", "other")),
        )
        for f in raw_failures[:50]
    ]
    return Step5Signal(
        exit_code=int(payload.get("exit_code", 0)),
        total=int(payload.get("total", 0)),
        passed=int(payload.get("passed", 0)),
        failed=int(payload.get("failed", 0)),
        skipped=int(payload.get("skipped", 0)),
        errors=int(payload.get("errors", 0)),
        failures=failures,
        pr_changed_files_used=bool(payload.get("pr_changed_files_used", False)),
        targeted_scope_used=bool(payload.get("targeted_scope_used", False)),
    )


# ---------------------------------------------------------------------------
# In-scope path set — union of PR-changed files, failing-test files, and the
# test files for changed sources. Step 6 substitutes this into the fixer
# prompt's <in_scope_paths> placeholder.
# ---------------------------------------------------------------------------

def _default_test_resolver(source_path: str) -> Iterable[str]:
    """Default mapper: `pdd/<stem>.py` -> `tests/test_<stem>.py`."""
    p = Path(source_path)
    if p.parts and p.parts[0] == "pdd" and p.suffix == ".py":
        yield f"tests/test_{p.stem}.py"


def compute_in_scope_paths(
    pr_changed_files: Sequence[str],
    step5_signal: Optional[Step5Signal],
    *,
    worktree: Path,
    test_file_resolver: Optional[Callable[[str], Iterable[str]]] = None,
) -> Set[Path]:
    """Return the union of PR-changed files, failing-test files, and matching test files.

    Paths are returned as POSIX-form Path objects relative to `worktree`.
    Files outside `worktree` are dropped. NEVER raises.
    """
    resolver = test_file_resolver or _default_test_resolver
    result: Set[Path] = set()

    def _add(raw: str) -> None:
        rel = _posix_relative(raw, worktree)
        if rel and ".." not in Path(rel).parts:
            result.add(Path(rel))

    for f in pr_changed_files or ():
        _add(f)

    if step5_signal:
        for failure in step5_signal.failures:
            _add(failure.file)

    for source in list(pr_changed_files or ()):
        try:
            for test_path in resolver(source):
                if (worktree / test_path).exists():
                    _add(test_path)
        except Exception:  # pragma: no cover
            continue

    return result


# ---------------------------------------------------------------------------
# Scope enforcement — verifies every fixer-touched path is in scope or
# explicitly listed in EXPANSION_ITEMS. Returns one blocker per violation.
# ---------------------------------------------------------------------------

def enforce_scope(
    diff_paths: Sequence[Path],
    in_scope: Set[Path],
    expansion_items: Sequence[str] = (),
    *,
    worktree: Path,
) -> List[ReviewFinding]:
    """Reject any fixer-touched path that is neither in scope nor justified."""
    findings: List[ReviewFinding] = []
    expanded = {item.strip() for item in expansion_items if item.strip()}

    for path in diff_paths or ():
        rel = Path(_posix_relative(str(path), worktree))
        if rel in in_scope:
            continue
        if any(rel.as_posix() in item or item in rel.as_posix() for item in expanded):
            continue
        findings.append(
            ReviewFinding(
                severity="blocker",
                reviewer="gate:pr-scope-enforce",
                area="pr-scope-guard",
                location=rel.as_posix(),
                finding="File modified outside PR-scope and not listed in EXPANSION_ITEMS",
                evidence=(
                    f"{rel.as_posix()} is not in the computed in-scope path set "
                    f"({len(in_scope)} entries) and has no matching EXPANSION_ITEMS line."
                ),
                required_fix=(
                    "Either remove this change from the diff or add an explicit "
                    "`EXPANSION_ITEMS:` line referencing a failing nodeid or PR file "
                    "in the Step 6a comment."
                ),
            )
        )
    return findings


# ---------------------------------------------------------------------------
# Diff sanity gate — pre-push LOC-budget check. Runs JUST before push, after
# Step 7, so it is the last line of defence against runaway fixer diffs.
# ---------------------------------------------------------------------------

def diff_sanity_gate(
    prior_pr_diff_paths: Sequence[Path],
    new_diff_paths: Sequence[Path],
    loc_delta: int,
    *,
    worktree: Path,
    in_scope: Set[Path],
    expansion_items: Sequence[str],
    step5_signal: Optional[Step5Signal],
    failing_test_count: int,
    max_loc_multiplier: float = 10.0,
    floor_lines: int = 200,
) -> List[ReviewFinding]:
    """Refuse a push whose diff exceeds the LOC budget or escapes scope."""
    failing_surface_loc = 0
    if step5_signal:
        seen: Set[str] = set()
        for failure in step5_signal.failures:
            if failure.file in seen:
                continue
            seen.add(failure.file)
            target = worktree / failure.file
            if target.exists():
                try:
                    failing_surface_loc += sum(
                        1 for _ in target.open("r", encoding="utf-8", errors="ignore")
                    )
                except Exception:  # pragma: no cover
                    continue

    budget = max(int(max_loc_multiplier * failing_surface_loc), int(floor_lines))
    findings: List[ReviewFinding] = []
    expansion_set = {item.strip() for item in expansion_items if item.strip()}
    override = any(item.startswith("BUDGET_OVERRIDE:") for item in expansion_set)

    if loc_delta > budget and not override:
        findings.append(
            ReviewFinding(
                severity="blocker",
                reviewer="gate:pr-scope-diff-sanity",
                area="pr-scope-guard",
                location="<diff>",
                finding=(
                    f"Fixer diff added {loc_delta} LOC, exceeding budget {budget} "
                    f"(= max({max_loc_multiplier} x failing-test surface "
                    f"{failing_surface_loc}, {floor_lines}))"
                ),
                evidence=(
                    f"prior_diff={len(prior_pr_diff_paths)} files, "
                    f"new_diff={len(new_diff_paths)} files, "
                    f"failing_tests={failing_test_count}"
                ),
                required_fix=(
                    "Trim the diff to the in-scope path set, or add a "
                    "`BUDGET_OVERRIDE:` line in EXPANSION_ITEMS with explicit "
                    "justification."
                ),
            )
        )

    # Defence-in-depth: re-run scope enforcement on the final pre-push tree.
    prior_set = {Path(_posix_relative(str(p), worktree)) for p in prior_pr_diff_paths}
    new_only = [p for p in new_diff_paths
                if Path(_posix_relative(str(p), worktree)) not in prior_set]
    findings.extend(enforce_scope(new_only, in_scope, expansion_items, worktree=worktree))
    return findings


# ---------------------------------------------------------------------------
# Causality check — orchestrator-authoritative gate that the fixer diff
# actually addresses Step 5's failing-test signal.
# ---------------------------------------------------------------------------

def causality_check(
    step5_signal: Optional[Step5Signal],
    pr_changed_files: Sequence[str],
    fixer_diff_paths: Sequence[Path],
    *,
    worktree: Path,
    traces_to_by_path: Mapping[str, Sequence[str]],
    expansion_items: Sequence[str],
) -> List[ReviewFinding]:
    """Verify the fixer diff is causally connected to the reported failures.

    Returns one finding per unrelated file plus one summary finding when the
    set of unresolved failures is non-empty. This check is authoritative —
    Step 7's prompt explicitly defers to this orchestrator-side call.
    """
    findings: List[ReviewFinding] = []
    if step5_signal is None:
        return findings  # parse-failure case is handled by an advisory finding upstream

    in_scope = compute_in_scope_paths(pr_changed_files, step5_signal, worktree=worktree)
    expansion_set = {item.strip() for item in expansion_items if item.strip()}

    # (a) Unrelated files: in the fixer diff but not in the related set.
    for path in fixer_diff_paths or ():
        rel = Path(_posix_relative(str(path), worktree))
        if rel in in_scope:
            continue
        if any(rel.as_posix() in item for item in expansion_set):
            continue
        findings.append(
            ReviewFinding(
                severity="critical",
                reviewer="gate:pr-scope-causality",
                area="pr-scope-guard",
                location=rel.as_posix(),
                finding="Fixer touched a file unrelated to the Step 5 failure signal",
                evidence=(
                    f"category=causality_failure file={rel.as_posix()} "
                    f"failing_files={[f.file for f in step5_signal.failures]}"
                ),
                required_fix=(
                    "Either show this file is causally required (add a "
                    "`# traces_to: <nodeid>` comment AND an EXPANSION_ITEMS entry "
                    "naming the failing nodeid/PR file) or remove it from the diff."
                ),
            )
        )

    # (b) Unresolved failures: failing nodeids with no traces_to and no EXPANSION_ITEMS justification.
    all_traces: Set[str] = set()
    for traces in traces_to_by_path.values():
        all_traces.update(traces)
    unresolved = [
        f for f in step5_signal.failures
        if f.nodeid not in all_traces
        and not any(f.file in item or f.nodeid in item for item in expansion_set)
    ]
    if unresolved:
        findings.append(
            ReviewFinding(
                severity="critical",
                reviewer="gate:pr-scope-causality",
                area="pr-scope-guard",
                location="<step5_signal>",
                finding=(
                    f"{len(unresolved)} Step 5 failing tests are not addressed by "
                    "any fixer-diff `# traces_to:` annotation or EXPANSION_ITEMS line."
                ),
                evidence="; ".join(f.nodeid for f in unresolved[:10]),
                required_fix=(
                    "Add a `# traces_to: <nodeid>` comment to the file that fixes "
                    "each failing test, or list the nodeid in EXPANSION_ITEMS with "
                    "a one-line justification."
                ),
            )
        )
    return findings


# ---------------------------------------------------------------------------
# Tiny helpers used by the public API above.
# ---------------------------------------------------------------------------

def _truncate(text: str, limit: int) -> str:
    if text and len(text) > limit:
        return text[: limit - 14] + "[...truncated]"
    return text or ""


def _posix_relative(raw: str, worktree: Path) -> str:
    if not raw:
        return ""
    p = Path(raw)
    if p.is_absolute():
        try:
            return p.relative_to(worktree).as_posix()
        except ValueError:
            return p.as_posix()
    return p.as_posix()


def _classify_failure(first) -> str:
    text = (getattr(first, "message", "") or "") + " " + (str(getattr(first, "text", "") or ""))
    text = text.lower()
    if "import" in text and "error" in text:
        return "import_error"
    if "timeout" in text:
        return "timeout"
    if "fixture" in text:
        return "fixture"
    if "config" in text:
        return "config"
    if "assert" in text:
        return "assertion"
    return "other"


if __name__ == "__main__":
    # Smoke test — exercises parse + scope helpers with a synthetic Step 5 block.
    sample = """
    <step5_signal>{"exit_code": 1, "total": 10, "passed": 9, "failed": 1,
    "skipped": 0, "errors": 0, "pr_changed_files_used": true,
    "targeted_scope_used": false, "failures": [{"nodeid":
    "tests/test_foo.py::test_bar", "file": "tests/test_foo.py", "lineno": 12,
    "message": "AssertionError: 1 != 2", "traceback_top": "assert 1 == 2",
    "category": "assertion"}]}</step5_signal>
    """
    sig = parse_step5_signal(sample, worktree=Path("/tmp/example-worktree"))
    assert sig is not None and sig.failed == 1
    assert sig.failures[0].nodeid == "tests/test_foo.py::test_bar"
    scope = compute_in_scope_paths(
        pr_changed_files=["pdd/foo.py"],
        step5_signal=sig,
        worktree=Path("/tmp/example-worktree"),
    )
    assert Path("pdd/foo.py") in scope
    print("checkup_gates_example: smoke test passed")
