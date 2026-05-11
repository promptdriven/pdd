from __future__ import annotations

import json
import logging
import os
import re
import subprocess
import time
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path
from typing import (
    Any,
    Dict,
    Iterable,
    Iterator,
    List,
    Optional,
    Sequence,
    Tuple,
)

from rich.console import Console

from .agentic_common import run_agentic_task
from .agentic_change import _run_gh_command
from .agentic_checkup_orchestrator import _get_git_root, _setup_pr_worktree
from .agentic_e2e_fix_orchestrator import push_with_retry
from .list_drift_detection import detect_static_list_drift

console = Console()
logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Role normalization
# ---------------------------------------------------------------------------

ROLE_ALIASES: Dict[str, str] = {
    "codex": "codex",
    "chatgpt": "codex",
    "openai": "codex",
    "claude": "claude",
    "anthropic": "claude",
    "gemini": "gemini",
    "google": "gemini",
}

ROLE_TO_PROVIDER: Dict[str, str] = {
    "codex": "openai",
    "claude": "anthropic",
    "gemini": "google",
}

DEFAULT_REVIEWER = "codex"
DEFAULT_FIXER = "claude"

HARD_NOT_CLEAN: Tuple[str, ...] = ("failed", "degraded", "missing")


def parse_reviewers(value: str | Sequence[str] | None) -> Tuple[str, ...]:
    """Normalize reviewer/fixer role names from CLI strings or sequences."""
    if value is None:
        return tuple()
    if isinstance(value, str):
        raw_items = re.split(r"[,\s]+", value)
    else:
        raw_items: List[str] = []
        for item in value:
            if item is None:
                continue
            raw_items.extend(re.split(r"[,\s]+", str(item)))

    out: List[str] = []
    seen: set[str] = set()
    for raw in raw_items:
        token = raw.strip().lower()
        if not token:
            continue
        norm = ROLE_ALIASES.get(token)
        if norm is None:
            continue
        if norm in seen:
            continue
        seen.add(norm)
        out.append(norm)
    return tuple(out)


# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------


@dataclass
class ReviewLoopContext:
    """Context for a checkup review loop."""

    issue_number: int
    issue_url: str
    issue_title: str = ""
    issue_body: str = ""
    pr_number: int = 0
    pr_url: str = ""
    pr_owner: str = ""
    pr_repo: str = ""
    pr_title: str = ""
    pr_body: str = ""
    pr_head_ref: str = ""
    pr_base_ref: str = ""
    pr_changed_files: Tuple[str, ...] = field(default_factory=tuple)
    pr_comments: Tuple[Dict[str, Any], ...] = field(default_factory=tuple)
    pr_reviews: Tuple[Dict[str, Any], ...] = field(default_factory=tuple)
    repo_owner: str = ""
    repo_name: str = ""
    architecture: str = ""
    extra_context: str = ""


@dataclass
class ReviewLoopConfig:
    """Configuration for the review loop."""

    reviewers: Tuple[str, ...] = field(default_factory=tuple)
    reviewer: Optional[str] = None
    fixer: Optional[str] = None
    review_only: bool = False
    max_rounds: int = 3
    max_cost: float = 5.0
    max_minutes: float = 60.0
    require_all_reviewers_clean: bool = True
    continue_on_reviewer_limit: bool = False
    require_final_fresh_review: bool = True
    blocking_severities: Tuple[str, ...] = ("blocker", "critical", "medium")
    clean_reviewer_states: Tuple[str, ...] = ("clean",)
    reviewer_fallback: bool = True
    timeout_adder: float = 0.0
    reasoning_time: Optional[float] = None


@dataclass
class ReviewFinding:
    severity: str = "medium"
    reviewer: str = ""
    area: str = ""
    evidence: str = ""
    finding: str = ""
    required_fix: str = ""
    location: str = ""
    status: str = "open"  # open | fixed | not_valid | partially_fixed | blocked
    round_number: int = 0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "severity": self.severity,
            "reviewer": self.reviewer,
            "area": self.area,
            "evidence": self.evidence,
            "finding": self.finding,
            "required_fix": self.required_fix,
            "location": self.location,
            "status": self.status,
            "round_number": self.round_number,
        }

    def dedup_key(self) -> str:
        compact_finding = re.sub(r"\s+", " ", self.finding or "").strip()
        compact_required = re.sub(r"\s+", " ", self.required_fix or "").strip()
        key = f"{(self.severity or '').lower()}|{self.location or ''}|{compact_finding}|{compact_required}"
        return key[:500]


@dataclass
class ReviewResult:
    role: str = ""
    status: str = "missing"  # clean | findings | failed | degraded | missing
    findings: List[ReviewFinding] = field(default_factory=list)
    raw_output: str = ""
    cost: float = 0.0
    model: str = ""
    status_reason: str = ""
    exit_code: Optional[int] = None
    stderr_tail: str = ""
    error_class: str = ""


@dataclass
class FixResult:
    role: str = ""
    success: bool = False
    summary: str = ""
    raw_output: str = ""
    cost: float = 0.0
    model: str = ""
    changed_files: List[str] = field(default_factory=list)
    dispositions: Dict[str, str] = field(default_factory=dict)  # finding_key -> disposition
    rationales: Dict[str, str] = field(default_factory=dict)  # finding_key -> rationale
    pushed: bool = False
    push_error: str = ""
    for_reviewer: str = ""
    round_number: int = 0


@dataclass
class ReviewLoopState:
    reviewer_status: str = "missing"
    fixer_role: str = ""
    fresh_final_status: str = "missing"
    stop_reason: str = ""
    total_cost: float = 0.0
    last_model: str = ""
    max_rounds_reached: bool = False
    max_cost_reached: bool = False
    max_duration_reached: bool = False
    rounds_completed: int = 0
    findings_by_key: Dict[str, ReviewFinding] = field(default_factory=dict)
    fix_attempts_by_key: Dict[str, int] = field(default_factory=dict)
    dispute_notes_by_key: Dict[str, str] = field(default_factory=dict)
    reviewer_feedback_by_key: Dict[str, str] = field(default_factory=dict)
    fix_results: List[FixResult] = field(default_factory=list)
    last_review_result: Optional[ReviewResult] = None
    primary_unavailable_note: str = ""
    last_status_reason: str = ""
    last_exit_code: Optional[int] = None
    last_stderr_tail: str = ""
    last_error_class: str = ""


# ---------------------------------------------------------------------------
# Provider context manager
# ---------------------------------------------------------------------------


@contextmanager
def _force_provider(role: str) -> Iterator[None]:
    provider = ROLE_TO_PROVIDER.get(role)
    env_var = "PDD_AGENTIC_PROVIDER"
    prior = os.environ.get(env_var)
    try:
        if provider:
            os.environ[env_var] = provider
        yield
    finally:
        if prior is None:
            os.environ.pop(env_var, None)
        else:
            os.environ[env_var] = prior


# ---------------------------------------------------------------------------
# Helpers: roles
# ---------------------------------------------------------------------------


def _resolve_roles(config: ReviewLoopConfig) -> Tuple[str, str]:
    """Resolve (reviewer_role, fixer_role) from config, applying defaults."""
    reviewer = None
    fixer = None

    if config.reviewer:
        normalized = parse_reviewers(config.reviewer)
        if normalized:
            reviewer = normalized[0]
    if config.fixer:
        normalized = parse_reviewers(config.fixer)
        if normalized:
            fixer = normalized[0]

    if reviewer is None or fixer is None:
        shorthand = parse_reviewers(config.reviewers) if config.reviewers else tuple()
        if reviewer is None and len(shorthand) >= 1:
            reviewer = shorthand[0]
        if fixer is None and len(shorthand) >= 2:
            fixer = shorthand[1]

    if reviewer is None:
        reviewer = DEFAULT_REVIEWER
    if fixer is None:
        fixer = DEFAULT_FIXER

    return reviewer, fixer


# ---------------------------------------------------------------------------
# Failure classification
# ---------------------------------------------------------------------------

_PROVIDER_LIMIT_PATTERNS = [
    r"rate.{0,5}limit",
    r"quota",
    r"context.{0,5}window",
    r"context.{0,5}length",
    r"too\s+many\s+tokens",
    r"max.{0,5}tokens",
    r"timed?\s*out",
    r"timeout",
]


def _classify_error(output: str) -> str:
    """Classify reviewer subprocess failure type."""
    low = (output or "").lower()
    if "auth" in low or "401" in low or "permission" in low:
        return "auth"
    if any(re.search(p, low) for p in [r"rate.{0,5}limit", r"quota"]):
        return "rate_limit"
    if "timeout" in low or "timed out" in low:
        return "timeout"
    if "context" in low and ("window" in low or "length" in low or "limit" in low):
        return "context_window"
    if "network" in low or "connection" in low or "unreachable" in low:
        return "network"
    if "not parseable" in low or "unparsable" in low:
        return "parse"
    return "crash"


def _failure_status(output: str, *, continue_on_reviewer_limit: bool, success: bool) -> Tuple[str, str]:
    """Return (status, reason) for failed/degraded/missing classification."""
    if not output:
        return "missing", "empty reviewer output"

    low = output.lower()
    is_limit = any(re.search(p, low) for p in _PROVIDER_LIMIT_PATTERNS)

    # Don't misclassify findings prose containing "context" as degraded.
    has_window = ("context" in low and ("window" in low or "length" in low or "limit" in low))
    is_limit = is_limit or has_window

    if not success:
        if is_limit:
            if continue_on_reviewer_limit:
                return "degraded", "provider/rate/quota/context-window/timeout limit"
            return "failed", "provider/rate/quota/context-window/timeout limit"
        return "failed", "reviewer subprocess failed"

    # Successful but unparsable
    return "failed", "reviewer output not parseable"


# ---------------------------------------------------------------------------
# Output parsing
# ---------------------------------------------------------------------------

CLEAN_MARKERS_EXACT = {
    "findings: none",
    "no actionable findings",
    "no actionable findings.",
    "status: clean",
}

CLEAN_LINE_PREFIXES = ("no actionable issues found.",)
NEGATING_WORDS = ("but", "however", "failed", "error")


def _looks_clean(text: str) -> bool:
    if not text:
        return False
    stripped = text.strip()
    low = stripped.lower()
    for marker in CLEAN_MARKERS_EXACT:
        if marker in low:
            return True
    # Only first line for prefix
    first_line = stripped.splitlines()[0].strip().lower() if stripped else ""
    for prefix in CLEAN_LINE_PREFIXES:
        if first_line.startswith(prefix):
            rest_of_line = first_line[len(prefix):]
            if not any(w in rest_of_line for w in NEGATING_WORDS):
                return True
    return False


_PRIORITY_TO_SEVERITY = {
    "p0": "blocker",
    "p1": "critical",
    "p2": "medium",
    "p3": "low",
}

_WORD_TO_SEVERITY = {
    "blocking": "blocker",
    "blocker": "blocker",
    "critical": "critical",
    "high": "critical",
    "medium": "medium",
    "med": "medium",
    "low": "low",
    "info": "info",
    "informational": "info",
}

VALID_SEVERITIES = {"blocker", "critical", "medium", "low", "info"}


def _normalize_severity(raw: str) -> str:
    if not raw:
        return "medium"
    low = raw.strip().lower()
    if low in VALID_SEVERITIES:
        return low
    if low in _PRIORITY_TO_SEVERITY:
        return _PRIORITY_TO_SEVERITY[low]
    if low in _WORD_TO_SEVERITY:
        return _WORD_TO_SEVERITY[low]
    return "medium"


def _extract_json_blob(text: str) -> Optional[Any]:
    """Extract JSON from fenced blocks or first/last brace fallback."""
    if not text:
        return None
    # Fenced ```json
    m = re.search(r"```json\s*(.*?)```", text, re.DOTALL | re.IGNORECASE)
    if m:
        try:
            return json.loads(m.group(1).strip())
        except json.JSONDecodeError:
            pass
    # Fenced ```
    m = re.search(r"```\s*(.*?)```", text, re.DOTALL)
    if m:
        body = m.group(1).strip()
        try:
            return json.loads(body)
        except json.JSONDecodeError:
            pass
    # First/last brace
    first_brace = text.find("{")
    last_brace = text.rfind("}")
    if first_brace != -1 and last_brace > first_brace:
        try:
            return json.loads(text[first_brace : last_brace + 1])
        except json.JSONDecodeError:
            pass
    # First/last bracket
    first_bracket = text.find("[")
    last_bracket = text.rfind("]")
    if first_bracket != -1 and last_bracket > first_bracket:
        try:
            return json.loads(text[first_bracket : last_bracket + 1])
        except json.JSONDecodeError:
            pass
    return None


def _findings_from_json(data: Any, reviewer: str, round_number: int) -> Tuple[Optional[str], List[ReviewFinding]]:
    """Return (status_or_None, findings) parsed from JSON data."""
    findings: List[ReviewFinding] = []
    status: Optional[str] = None

    if isinstance(data, dict):
        status_raw = data.get("status")
        if isinstance(status_raw, str):
            s = status_raw.strip().lower()
            if s in {"clean", "findings", "failed", "degraded", "missing"}:
                status = s
        f_list = data.get("findings")
        if isinstance(f_list, list):
            findings.extend(_findings_from_list(f_list, reviewer, round_number))
    elif isinstance(data, list):
        findings.extend(_findings_from_list(data, reviewer, round_number))

    return status, findings


def _findings_from_list(items: List[Any], reviewer: str, round_number: int) -> List[ReviewFinding]:
    out: List[ReviewFinding] = []
    for item in items:
        if not isinstance(item, dict):
            continue
        finding = ReviewFinding(
            severity=_normalize_severity(str(item.get("severity", "medium"))),
            reviewer=reviewer,
            area=str(item.get("area", "")),
            evidence=str(item.get("evidence", "")),
            finding=str(item.get("finding", item.get("message", item.get("description", "")))),
            required_fix=str(item.get("required_fix", item.get("fix", ""))),
            location=str(item.get("location", item.get("file", ""))),
            status="open",
            round_number=round_number,
        )
        if finding.finding or finding.location:
            out.append(finding)
    return out


_PRIORITY_BULLET_RE = re.compile(
    r"^\s*[-*]\s*\[(P[0-3])\]\s*(?:\[([^\]]+)\]\(([^)]+)\)\s*)?(.+)$",
    re.MULTILINE,
)

_BRACKET_SEVERITY_RE = re.compile(
    r"^\s*[-*]?\s*\[(blocker|critical|medium|low|info|high|blocking)\]\s*(.+)$",
    re.MULTILINE | re.IGNORECASE,
)

_NUMBERED_SEVERITY_RE = re.compile(
    r"^\s*\d+\.\s+(Blocking|Blocker|Critical|High|Medium|Low|Info|Informational)\s*(?:[:\-]|workflow|hole|issue|bug|finding)?\s*[:\-]?\s*(.+)$",
    re.MULTILINE | re.IGNORECASE,
)

_NUMBERED_HEADING_RE = re.compile(
    r"^\s*\d+\.\s+\*\*([^*]+?)\*\*\s*\.?\s*$",
    re.MULTILINE,
)

_DASH_SEVERITY_RE = re.compile(
    r"^\s*[-*]\s+(Blocking|Blocker|Critical|High|Medium|Low|Info)\s*[:\-]\s*(.+)$",
    re.MULTILINE | re.IGNORECASE,
)

_PATH_LINE_RE = re.compile(r"\[([^\]]+\.[a-zA-Z0-9]+:\d+)\]\(([^)]+)\)")
_BARE_PATH_LINE_RE = re.compile(r"([A-Za-z0-9_./\-]+\.[a-zA-Z0-9]+:\d+)")


def _extract_first_location(text: str) -> str:
    m = _PATH_LINE_RE.search(text or "")
    if m:
        return m.group(1)
    m = _BARE_PATH_LINE_RE.search(text or "")
    if m:
        return m.group(1)
    return ""


def _findings_from_markdown(text: str, reviewer: str, round_number: int) -> List[ReviewFinding]:
    """Parse free-text reviewer output for severity-tagged bullets/lines."""
    out: List[ReviewFinding] = []
    seen_keys: set[str] = set()

    def _add(severity: str, message: str, location: str, evidence: str = "") -> None:
        message = (message or "").strip().rstrip(".")
        if not message and not location:
            return
        f = ReviewFinding(
            severity=_normalize_severity(severity),
            reviewer=reviewer,
            area="",
            evidence=evidence.strip(),
            finding=message,
            required_fix="",
            location=location.strip(),
            status="open",
            round_number=round_number,
        )
        k = f.dedup_key()
        if k in seen_keys:
            return
        seen_keys.add(k)
        out.append(f)

    # Codex priority bullets: - [P1] [file](path:line) message
    for m in _PRIORITY_BULLET_RE.finditer(text or ""):
        priority, link_label, link_target, msg = m.group(1), m.group(2), m.group(3), m.group(4)
        sev = _PRIORITY_TO_SEVERITY.get(priority.lower(), "medium")
        location = link_label or link_target or _extract_first_location(msg)
        _add(sev, msg, location)

    # Numbered "1. Blocking: ..."
    for m in _NUMBERED_SEVERITY_RE.finditer(text or ""):
        sev_word, msg = m.group(1), m.group(2)
        _add(sev_word, msg, _extract_first_location(msg))

    # "- Medium: ..."
    for m in _DASH_SEVERITY_RE.finditer(text or ""):
        sev_word, msg = m.group(1), m.group(2)
        _add(sev_word, msg, _extract_first_location(msg))

    # Bracketed [severity] message
    for m in _BRACKET_SEVERITY_RE.finditer(text or ""):
        sev, msg = m.group(1), m.group(2)
        _add(sev, msg, _extract_first_location(msg))

    # Numbered headings with following paragraph
    lines = (text or "").splitlines()
    for i, line in enumerate(lines):
        m = _NUMBERED_HEADING_RE.match(line)
        if not m:
            # Try free-form: "1. Blocking workflow hole: ..."
            mm = re.match(r"^\s*\d+\.\s+([A-Za-z]+)\b", line)
            if mm and mm.group(1).lower() in _WORD_TO_SEVERITY:
                # Already covered by _NUMBERED_SEVERITY_RE typically
                continue
            continue
        title = m.group(1)
        # Look ahead a few lines for paragraph & location
        ahead = "\n".join(lines[i + 1 : i + 6]).strip()
        location = _extract_first_location(ahead) or _extract_first_location(title)
        _add("medium", title, location, evidence=ahead[:500])

    # Concrete bullets under **Findings**: - [path.py:12](.../path.py:12) message
    in_findings = False
    for line in lines:
        if re.match(r"^\s*\*\*Findings\*\*", line, re.IGNORECASE):
            in_findings = True
            continue
        if in_findings:
            if line.strip().startswith("###") or line.strip().startswith("**"):
                # End of findings block (heuristic)
                if not re.match(r"^\s*\*\*Findings\*\*", line, re.IGNORECASE):
                    in_findings = False
                    continue
            bm = re.match(r"^\s*[-*]\s+(.+)$", line)
            if bm:
                content = bm.group(1)
                loc = _extract_first_location(content)
                if loc:
                    _add("medium", content, loc)

    return out


_EXTERNAL_READINESS_TERMS = (
    "auto-heal-pr",
    "github status check",
    "cloud build",
    "mergeability",
    "pending check",
    "action-required",
    "required check",
    "synthetic merge",
    "auto heal",
)


def _is_external_readiness_only(finding: ReviewFinding) -> bool:
    """True if a finding only describes external CI readiness state with no concrete file."""
    if finding.location and re.search(r"\.[a-zA-Z]+(:\d+)?", finding.location):
        return False
    text = " ".join([finding.finding, finding.evidence, finding.required_fix, finding.area]).lower()
    if not text.strip():
        return False
    if any(term in text for term in _EXTERNAL_READINESS_TERMS):
        # And no mention of a real file
        if not _BARE_PATH_LINE_RE.search(text) and not re.search(r"[a-zA-Z0-9_]+\.py\b", text):
            return True
    return False


def _normalize_findings(
    raw_output: str,
    reviewer: str,
    round_number: int,
    *,
    success: bool,
    continue_on_reviewer_limit: bool,
) -> Tuple[str, List[ReviewFinding], str]:
    """Normalize reviewer output -> (status, findings, status_reason)."""

    if not success:
        # Even on subprocess failure, see if there's anything parseable.
        # But mostly classify as failed/degraded.
        status, reason = _failure_status(raw_output, continue_on_reviewer_limit=continue_on_reviewer_limit, success=False)
        return status, [], reason

    if not raw_output or not raw_output.strip():
        return "missing", [], "empty reviewer output"

    # Try JSON
    data = _extract_json_blob(raw_output)
    if data is not None:
        status, findings = _findings_from_json(data, reviewer, round_number)
        if status is not None or findings:
            # Filter external-readiness-only
            filtered = [f for f in findings if not _is_external_readiness_only(f)]
            dropped = len(findings) - len(filtered)
            if status == "findings" and not filtered:
                status = "clean"
            elif status is None:
                status = "findings" if filtered else "clean"
            elif status in HARD_NOT_CLEAN:
                # preserve hard-not-clean
                pass
            reason = f"dropped {dropped} external-readiness findings" if dropped else ""
            return status, filtered, reason

    # Markdown parsing
    md_findings = _findings_from_markdown(raw_output, reviewer, round_number)
    if md_findings:
        filtered = [f for f in md_findings if not _is_external_readiness_only(f)]
        if not filtered:
            return "clean", [], "all parsed findings were external-readiness only"
        return "findings", filtered, ""

    # No findings parsed: check explicit clean markers.
    if _looks_clean(raw_output):
        return "clean", [], "explicit clean marker"

    status, reason = _failure_status(raw_output, continue_on_reviewer_limit=continue_on_reviewer_limit, success=True)
    return status, [], reason


# ---------------------------------------------------------------------------
# Artifact helpers
# ---------------------------------------------------------------------------


def _write_artifact(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _artifacts_dir(cwd: Path, issue_number: int, pr_number: int) -> Path:
    git_root = _get_git_root(cwd) or cwd
    return git_root / ".pdd" / "checkup-review-loop" / f"issue-{issue_number}-pr-{pr_number}"


def _write_findings_json(path: Path, findings: Iterable[ReviewFinding]) -> None:
    data = [f.to_dict() for f in findings]
    _write_artifact(path, json.dumps(data, indent=2))


def _write_dedup_state(path: Path, state: ReviewLoopState) -> None:
    payload = {
        "round": state.rounds_completed,
        "findings": [
            {
                "key": k,
                **f.to_dict(),
            }
            for k, f in state.findings_by_key.items()
        ],
    }
    _write_artifact(path, json.dumps(payload, indent=2))


# ---------------------------------------------------------------------------
# PR metadata
# ---------------------------------------------------------------------------


def _fetch_pr_metadata(pr_owner: str, pr_repo: str, pr_number: int) -> Tuple[Dict[str, Any], str]:
    """Return (metadata_dict, error_message)."""
    success, output = _run_gh_command(
        ["api", f"repos/{pr_owner}/{pr_repo}/pulls/{pr_number}"], timeout=30
    )
    if not success:
        return {}, output
    try:
        data = json.loads(output)
        if not isinstance(data, dict):
            return {}, "PR metadata not a dict"
        return data, ""
    except json.JSONDecodeError as e:
        return {}, f"Failed to parse PR metadata: {e}"


def _pr_changed_python_files(worktree: Path, pr_metadata: Dict[str, Any]) -> List[Path]:
    """Get PR-changed Python files via merge-base diff."""
    base_ref = (pr_metadata.get("base") or {}).get("ref") or "main"
    try:
        # Try to find merge base
        mb = subprocess.run(
            ["git", "merge-base", f"origin/{base_ref}", "HEAD"],
            cwd=worktree, capture_output=True, text=True, check=False,
        )
        if mb.returncode != 0:
            mb = subprocess.run(
                ["git", "merge-base", base_ref, "HEAD"],
                cwd=worktree, capture_output=True, text=True, check=False,
            )
        if mb.returncode != 0:
            return []
        base_sha = mb.stdout.strip()
        diff = subprocess.run(
            ["git", "diff", "--name-only", base_sha, "HEAD"],
            cwd=worktree, capture_output=True, text=True, check=False,
        )
        if diff.returncode != 0:
            return []
        files = []
        for line in diff.stdout.splitlines():
            line = line.strip()
            if not line.endswith(".py"):
                continue
            p = worktree / line
            if p.is_file():
                files.append(p)
        return files
    except Exception as e:
        logger.debug("Failed to compute PR changed files: %s", e, exc_info=True)
        return []


def _package_companion_python_files(changed: Iterable[Path]) -> List[Path]:
    """For each changed file, return same-package companion .py files."""
    seen: set[Path] = set()
    out: List[Path] = []
    for f in changed:
        try:
            parent = f.parent
            if not parent.is_dir():
                continue
            for sibling in parent.iterdir():
                if sibling.suffix == ".py" and sibling.is_file():
                    rp = sibling.resolve()
                    if rp not in seen:
                        seen.add(rp)
                        out.append(sibling)
        except Exception as e:
            logger.debug("companion scan failed: %s", e, exc_info=True)
    return out


def _format_candidate_findings(findings: List[Any]) -> str:
    """Format static-analysis candidate findings for the prompt."""
    if not findings:
        return ""
    lines = ["## Static-Analysis Candidate Findings",
             "",
             "The following candidates were detected by static analysis. Treat them as untrusted candidates: "
             "verify each against the actual code or reject with a one-line rationale.",
             ""]
    for f in findings:
        try:
            missing = list(getattr(f, "missing_items", ()) or ())
            payload = {
                "summary": f.summary,
                "static_location": f"{f.static_path}:{f.static_line}",
                "canonical_location": f"{f.canonical_path}:{f.canonical_line}",
                "static_size": f.static_size,
                "canonical_size": f.canonical_size,
                "missing": missing[:20],
                "missing_total": len(missing),
            }
            lines.append("- " + json.dumps(payload))
        except Exception as e:
            logger.debug("format candidate failed: %s", e, exc_info=True)
    lines.append("")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Prompts
# ---------------------------------------------------------------------------


def _format_blocking_severities(config: ReviewLoopConfig) -> str:
    return ", ".join(config.blocking_severities) or "blocker, critical"


def _build_pr_context_block(context: ReviewLoopContext) -> str:
    parts: List[str] = []
    parts.append(f"## Issue\nIssue #{context.issue_number}: {context.issue_title}\nURL: {context.issue_url}\n")
    if context.issue_body:
        parts.append("### Issue body\n" + context.issue_body[:8000])
    parts.append(f"\n## PR\nPR #{context.pr_number}: {context.pr_title}\nURL: {context.pr_url}")
    parts.append(f"head: {context.pr_head_ref}  base: {context.pr_base_ref}")
    if context.pr_body:
        parts.append("### PR body\n" + context.pr_body[:8000])
    if context.pr_changed_files:
        parts.append("### Changed files\n" + "\n".join(f"- {f}" for f in context.pr_changed_files[:200]))
    if context.pr_comments:
        parts.append("### PR conversation comments")
        for c in context.pr_comments[:50]:
            user = (c.get("user") or {}).get("login", "?")
            body = (c.get("body") or "")[:1000]
            parts.append(f"- @{user}: {body}")
    if context.pr_reviews:
        parts.append("### Submitted PR reviews")
        for r in context.pr_reviews[:30]:
            user = (r.get("user") or {}).get("login", "?")
            state = r.get("state", "")
            body = (r.get("body") or "")[:800]
            parts.append(f"- @{user} [{state}]: {body}")
    if context.architecture:
        parts.append("\n## Architecture\n" + context.architecture[:8000])
    if context.extra_context:
        parts.append("\n## Extra context\n" + context.extra_context[:8000])
    return "\n".join(parts)


_MANUAL_REVIEW_STANDARD_TEMPLATE = """\
## Manual Review Standard (read first)

This is the automated equivalent of the manual request:
"review PR as a user workflow perspective; check if any prompt, example, or
architecture update is needed; fully review the PR with the existing codebase;
check for no regressions; verify it fully aligns with and resolves the issue;
make sure it does not open more holes."

Highest-priority severities: {blocking_severities}. Do NOT flag severities
the user has narrowed off. Every valid in-scope finding remains actionable
until fixed or explicitly accepted by you as resolved.

You MUST:

1. Perform a full PR review from a real user-workflow perspective FIRST,
   before any code-internal checks. Trace how a CLI/API user experiences the
   changed behavior. Verify the PR fully resolves the issue, aligns with the
   existing codebase, and decide whether prompts/examples/architecture/docs/
   CLI help/tests need updates. Look for regressions or newly opened holes
   in security, billing/cost, API, reliability, UX, compatibility, tests,
   and maintainability.

2. Evaluate issue INTENT, not the literal proposed implementation. If the
   PR uses a different approach, accept it when PR/issue context justifies
   the change and the new approach fully solves the underlying user problem.
   Still report findings when the direction change is unjustified,
   contradicted by user comments, leaves the underlying problem unresolved,
   leaves stale user-facing flags/docs/examples promising old behavior, or
   omits required documentation/tests/prompt/architecture updates.

3. For source-of-truth, catalog, manifest, cache, leaderboard, or
   generated-data changes, check provenance and authoritative sources where
   practical: model/variant identity, normalization, dates, subsets, ranks,
   confidence fields, and whether reviewers can audit where each value came
   from. Check whether the PR recreates the same bug class in a different
   form. For model catalog and manifest-based scoring changes, verify
   provider roots and aliases actually produce catalog rows, default models
   are not assigned high/low/minimal reasoning-variant scores, and
   normalization does not collapse distinct Arena variants into one score.

4. Do NOT collapse independently actionable problems into one broad finding.
   When a PR changes architecture, also review the alternate architecture
   on its own terms and report prompt/docs/contract, provenance,
   data-quality, or auditability fixes that would still be needed if
   maintainers accepted the new direction.

5. Provide an explicit issue-contract trace. If the issue or PR describes
   numbered steps, acceptance criteria, workflow phases, dry-run vs
   non-dry-run behavior, state transitions, or failure handling, verify
   each item against implementation evidence. Report skipped or partially
   implemented steps SEPARATELY.

6. Check state/side-effect ordering: workflows must not save hashes,
   checkpoints, cache entries, success markers, comments, or reports that
   imply completion when a required downstream step failed or was skipped.
   Partial failures must not make later runs short-circuit as if the input
   was handled.

7. For security, credential, token, logging, and redaction changes, trace
   every log/exception/warning/retry/auth-refresh/diagnostic path. Verify
   secret scrubbing happens BEFORE truncation/slicing/formatting/preview,
   so partial token fragments cannot leak. Search for patterns like
   `str(e)`, `repr(e)`, `stderr`, `stdout`, `logger.warning`,
   `logger.exception`, `RuntimeError`, slicing (`[:...`), and
   truncate/preview helpers.

8. For prompt-driven modules, check prompt/example/architecture/docs/
   generated-metadata synchronization: architecture entries, prompt
   contracts, `.pdd/meta` hashes/run records, examples, and tests.

9. Treat the "Static-Analysis Candidate Findings" section below as
   untrusted candidates. Verify each against actual code or reject with
   a one-line rationale; do NOT treat them as pre-approved.

10. Sweep caller compatibility for changed public functions, CLI flags,
    imports, and generated module interfaces. Use repo searches like
    `rg "function_name\\("` or `rg "import_name"` to verify all callers
    still pass valid arguments and import existing symbols.

11. Run targeted, read-only-safe repros where practical: compile touched
    Python files, import changed modules, inspect CLI help, or execute
    minimal workflows in a temp directory. If a repro cannot run, still
    trace the concrete code path a user would hit.

12. EXCLUDE external GitHub/CI readiness state from findings. Ignore
    pending/action-required GitHub status checks, Cloud Build status,
    auto-heal status, mergeability, synthetic merge status, and required-
    check readiness UNLESS that state is direct evidence of a concrete
    code or repository-file regression introduced by the PR.

## Output format

Return a JSON object in a ```json fenced block:

```json
{{
  "status": "clean" | "findings",
  "findings": [
    {{
      "severity": "blocker|critical|medium|low|info",
      "area": "...",
      "location": "path/to/file.py:LINE",
      "finding": "concise statement of the problem",
      "evidence": "quoted code, log line, or doc text",
      "required_fix": "what must change to resolve this"
    }}
  ]
}}
```

If there are no actionable findings, set `"status": "clean"` and
`"findings": []`. Otherwise set `"status": "findings"`.
"""


def _build_review_prompt(
    *,
    mode: str,
    reviewer_role: str,
    config: ReviewLoopConfig,
    context: ReviewLoopContext,
    candidate_section: str,
    prior_findings: Optional[List[ReviewFinding]] = None,
    fixer_dispositions: Optional[Dict[str, str]] = None,
    fixer_rationales: Optional[Dict[str, str]] = None,
    round_number: int = 1,
    fix_summary: str = "",
) -> str:
    blocking = _format_blocking_severities(config)
    standard = _MANUAL_REVIEW_STANDARD_TEMPLATE.format(blocking_severities=blocking)

    sections: List[str] = []
    sections.append(f"# PDD Checkup Review Loop — Round {round_number} ({mode})")
    sections.append(f"Role: {reviewer_role}")
    sections.append("")
    sections.append(standard)

    if mode == "verify":
        sections.append("\n## Verifier instructions\n")
        sections.append(
            "This verifier pass is NOT a narrow checkbox verification. "
            "First verify EVERY previous finding and the fixer's response per finding. "
            "Then perform a FRESH FULL PR REVIEW again using the manual-review standard above. "
            "Look for newly visible issues, missed issues, regressions from the fix, and "
            "prompt/example/architecture/docs/test drift. The loop repeats until you report "
            "no actionable findings or max_rounds is reached.\n"
        )
        if prior_findings:
            sections.append("### Prior findings to verify\n")
            for i, f in enumerate(prior_findings, 1):
                disp = (fixer_dispositions or {}).get(f.dedup_key(), "unknown")
                rationale = (fixer_rationales or {}).get(f.dedup_key(), "")
                sections.append(
                    f"{i}. [{f.severity}] @ {f.location or 'n/a'}\n"
                    f"   finding: {f.finding}\n"
                    f"   required_fix: {f.required_fix}\n"
                    f"   fixer_disposition: {disp}\n"
                    f"   fixer_rationale: {rationale}\n"
                )
            sections.append(
                "If the fixer returned `not_valid`, `partially_fixed`, or `blocked` and you accept "
                "the rationale, OMIT that finding from your output (it will be marked fixed). "
                "If you reject the rationale, RE-REPORT the finding with concrete evidence and a "
                "reason the fixer should act on it.\n"
            )
        if fix_summary:
            sections.append("### Fixer summary\n" + fix_summary[:4000])

    if candidate_section:
        sections.append(candidate_section)

    sections.append(_build_pr_context_block(context))
    return "\n".join(sections)


def _build_fixer_prompt(
    *,
    fixer_role: str,
    config: ReviewLoopConfig,
    context: ReviewLoopContext,
    findings: List[ReviewFinding],
    round_number: int,
) -> str:
    blocking = _format_blocking_severities(config)
    sections: List[str] = []
    sections.append(f"# PDD Checkup Fix Round {round_number}")
    sections.append(f"Fixer role: {fixer_role}")
    sections.append("")
    sections.append(
        f"Highest-priority severities: {blocking}. The loop continues until those are resolved. "
        "Address EVERY valid, in-scope finding when practical, while prioritizing those severities. "
        "'Focused fixes' means avoid unrelated refactors and broad churn — not leaving real issues "
        "unfixed. If you leave any valid finding unfixed, return `partially_fixed` or `blocked` "
        "with a concrete rationale per finding."
    )
    sections.append("")
    sections.append("## Findings from primary reviewer (act on each)")
    for i, f in enumerate(findings, 1):
        sections.append(
            f"\n{i}. key=`{f.dedup_key()}`\n"
            f"   severity: {f.severity}\n"
            f"   location: {f.location or 'n/a'}\n"
            f"   finding: {f.finding}\n"
            f"   evidence: {f.evidence}\n"
            f"   required_fix: {f.required_fix}\n"
        )
    sections.append(
        "\n## Output format\n"
        "After making code changes, return a JSON object in a ```json fenced block:\n"
        "```json\n"
        "{\n"
        '  "summary": "what you changed and why",\n'
        '  "changed_files": ["path/to/file.py", ...],\n'
        '  "dispositions": {\n'
        '    "<finding_key>": "fixed" | "not_valid" | "partially_fixed" | "blocked"\n'
        "  },\n"
        '  "rationales": {\n'
        '    "<finding_key>": "short rationale"\n'
        "  }\n"
        "}\n"
        "```\n"
        "Use the exact `key=` values shown above. Legacy `not_a_bug` is normalized to `not_valid`.\n"
    )
    sections.append(_build_pr_context_block(context))
    return "\n".join(sections)


def _build_repair_prompt(raw: str, role: str) -> str:
    return (
        f"# Parse-Repair Pass for {role}\n\n"
        "Convert the reviewer text below into the required JSON schema. "
        "Do NOT perform a new review or add findings beyond what is already stated. "
        "Do NOT change severities. Just emit valid JSON.\n\n"
        "Required schema (in a ```json fence):\n"
        "```json\n"
        '{ "status": "clean"|"findings"|"failed",\n'
        '  "findings": [ { "severity": "...", "area": "...", "location": "...", '
        '"finding": "...", "evidence": "...", "required_fix": "..." } ] }\n'
        "```\n\n"
        "## Original reviewer output\n\n"
        f"{raw[:20000]}\n"
    )


# ---------------------------------------------------------------------------
# Reviewer / Fixer execution
# ---------------------------------------------------------------------------


def _persist_review_artifacts(
    artifacts: Path,
    round_number: int,
    mode: str,
    role: str,
    prompt: str,
    output: str,
    findings: List[ReviewFinding],
    candidates: Optional[List[Any]] = None,
) -> None:
    base = artifacts / f"round-{round_number}-{mode}-{role}"
    _write_artifact(base.with_suffix(".prompt.txt"), prompt)
    _write_artifact(base.with_suffix(".output.txt"), output)
    _write_findings_json(base.with_suffix(".findings.json"), findings)
    if candidates:
        cand_path = artifacts / f"round-{round_number}-{mode}-static-analysis-candidates.json"
        try:
            payload = []
            for c in candidates:
                payload.append({
                    "summary": getattr(c, "summary", ""),
                    "static_path": str(getattr(c, "static_path", "")),
                    "static_line": getattr(c, "static_line", 0),
                    "static_size": getattr(c, "static_size", 0),
                    "canonical_path": str(getattr(c, "canonical_path", "")),
                    "canonical_line": getattr(c, "canonical_line", 0),
                    "canonical_size": getattr(c, "canonical_size", 0),
                    "missing_items": list(getattr(c, "missing_items", ()) or ()),
                })
            _write_artifact(cand_path, json.dumps(payload, indent=2))
        except Exception as e:
            logger.debug("persist candidates failed: %s", e, exc_info=True)


def _capture_stderr_tail(text: str, n: int = 20) -> str:
    if not text:
        return ""
    lines = text.splitlines()
    return "\n".join(lines[-n:])



def _run_role_task(
    role: str,
    instruction: str,
    *,
    cwd: Optional[Path] = None,
    verbose: bool = False,
    quiet: bool = False,
    label: str = "task",
    deadline: Optional[float] = None,
    reasoning_time: Optional[float] = None,
) -> Tuple[bool, str, float, str]:
    with _force_provider(role):
        return run_agentic_task(
            instruction,
            cwd=cwd,
            verbose=verbose,
            quiet=quiet,
            label=label,
            deadline=deadline,
            reasoning_time=reasoning_time,
        )


def _run_review(
    *,
    mode: str,
    reviewer_role: str,
    config: ReviewLoopConfig,
    context: ReviewLoopContext,
    worktree: Path,
    artifacts: Path,
    round_number: int,
    prior_findings: Optional[List[ReviewFinding]] = None,
    fixer_dispositions: Optional[Dict[str, str]] = None,
    fixer_rationales: Optional[Dict[str, str]] = None,
    fix_summary: str = "",
    verbose: bool = False,
    quiet: bool = False,
    deadline: Optional[float] = None,
) -> ReviewResult:
    """Execute a single reviewer pass against the worktree."""
    # Static-analysis candidates
    changed: List[Path] = []
    base_ref = context.pr_base_ref or "main"
    try:
        diff_proc = subprocess.run(
            ["git", "diff", "--name-only", f"origin/{base_ref}...HEAD"],
            cwd=worktree, capture_output=True, text=True, check=False
        )
        if diff_proc.returncode == 0:
            for line in diff_proc.stdout.splitlines():
                line = line.strip()
                if line.endswith(".py"):
                    changed.append(worktree / line)
    except Exception as e:
        logger.debug("diff failed: %s", e, exc_info=True)
    companions = _package_companion_python_files(changed)
    candidates: List[Any] = []
    try:
        all_paths = list({p.resolve(): p for p in (changed + companions)}.values())
        raw = detect_static_list_drift(all_paths)
        changed_set = {p.resolve() for p in changed}
        for f in raw:
            try:
                static_in = Path(f.static_path).resolve() in changed_set
                canon_in = Path(f.canonical_path).resolve() in changed_set
                if static_in or canon_in:
                    candidates.append(f)
            except Exception as e:
                logger.debug("candidate filter failed: %s", e, exc_info=True)
    except Exception as e:
        logger.debug("drift detection failed: %s", e, exc_info=True)

    candidate_section = _format_candidate_findings(candidates)

    prompt = _build_review_prompt(
        mode=mode,
        reviewer_role=reviewer_role,
        config=config,
        context=context,
        candidate_section=candidate_section,
        prior_findings=prior_findings,
        fixer_dispositions=fixer_dispositions,
        fixer_rationales=fixer_rationales,
        round_number=round_number,
        fix_summary=fix_summary,
    )

    label = f"checkup-review-loop-{mode}-{reviewer_role}-round{round_number}"
    success, output, cost, model = _run_role_task(
        reviewer_role,
        prompt,
            cwd=worktree,
            verbose=verbose,
            quiet=quiet,
            label=label,
            deadline=deadline,
            reasoning_time=config.reasoning_time,
        )

    status, findings, reason = _normalize_findings(
        output,
        reviewer_role,
        round_number,
        success=success,
        continue_on_reviewer_limit=config.continue_on_reviewer_limit,
    )

    # One bounded same-role parse-repair if successful but unparsable.
    if success and status not in {"clean", "findings"} and not findings:
        try:
            repair_prompt = _build_repair_prompt(output, reviewer_role)
            rs, ro, rc, rm = _run_role_task(
                reviewer_role,
                repair_prompt,
                    cwd=worktree,
                    verbose=verbose,
                    quiet=quiet,
                    label=label + " parse-repair",
                    deadline=deadline,
                    reasoning_time=config.reasoning_time,
                )
            cost += rc
            if rm:
                model = rm
            r_status, r_findings, r_reason = _normalize_findings(
                ro,
                reviewer_role,
                round_number,
                success=rs,
                continue_on_reviewer_limit=config.continue_on_reviewer_limit,
            )
            if r_status in {"clean", "findings", "failed"} and (r_findings or r_status == "clean"):
                status, findings, reason = r_status, r_findings, "parse-repair: " + r_reason
                output = output + "\n\n## parse-repair\n" + ro
        except Exception as e:
            logger.debug("parse-repair failed: %s", e, exc_info=True)

    error_class = _classify_error(output) if status in HARD_NOT_CLEAN else ""

    result = ReviewResult(
        role=reviewer_role,
        status=status,
        findings=findings,
        raw_output=output,
        cost=cost,
        model=model,
        status_reason=reason,
        exit_code=0 if success else 1,
        stderr_tail=_capture_stderr_tail(output if not success else ""),
        error_class=error_class,
    )

    _persist_review_artifacts(artifacts, round_number, mode, reviewer_role, prompt, output, findings, candidates)
    return result


def _parse_fixer_output(
    raw: str,
    findings: List[ReviewFinding],
    fixer_role: str,
    round_number: int,
) -> Dict[str, Any]:
    """Parse fixer JSON output -> dict with summary/changed_files/dispositions/rationales."""
    out = {
        "summary": "",
        "changed_files": [],
        "dispositions": {},
        "rationales": {},
    }
    data = _extract_json_blob(raw)
    if isinstance(data, dict):
        out["summary"] = str(data.get("summary", ""))
        cf = data.get("changed_files")
        if isinstance(cf, list):
            out["changed_files"] = [str(x) for x in cf]
        disp = data.get("dispositions")
        if isinstance(disp, dict):
            for k, v in disp.items():
                v_norm = str(v).lower().strip()
                if v_norm == "not_a_bug":
                    v_norm = "not_valid"
                if v_norm in {"fixed", "not_valid", "partially_fixed", "blocked"}:
                    out["dispositions"][str(k)] = v_norm
        rats = data.get("rationales")
        if isinstance(rats, dict):
            for k, v in rats.items():
                out["rationales"][str(k)] = str(v)
    if not out["summary"]:
        out["summary"] = (raw or "")[:500]
    return out


def _commit_and_push_if_changed(
    worktree: Path,
    context: ReviewLoopContext,
    quiet: bool = False,
) -> Tuple[bool, str]:
    """Stage, commit (with bot identity) and push to PR head ref. Returns (pushed, error)."""
    # Stage
    subprocess.run(["git", "add", "-A"], cwd=worktree, capture_output=True, text=True, check=False)

    status_proc = subprocess.run(
        ["git", "status", "--porcelain"], cwd=worktree, capture_output=True, text=True, check=False
    )
    if status_proc.returncode != 0:
        return False, f"git status failed: {status_proc.stderr}"

    if not status_proc.stdout.strip():
        # Nothing to commit
        return False, ""

    commit = subprocess.run(
        [
            "git", "-c", "user.name=PDD Bot",
            "-c", "user.email=pdd-bot@users.noreply.github.com",
            "commit", "-m", "pdd checkup --review-loop: apply fixer changes",
        ],
        cwd=worktree, capture_output=True, text=True, check=False,
    )
    if commit.returncode != 0:
        return False, f"git commit failed: {commit.stderr}"

    # Resolve PR head ref + clone URL
    pr_metadata, err = _fetch_pr_metadata(context.pr_owner, context.pr_repo, context.pr_number)
    if err or not pr_metadata:
        return False, f"failed to fetch PR metadata: {err or 'empty'}"

    head = pr_metadata.get("head") or {}
    head_ref = head.get("ref")
    head_repo = head.get("repo") or {}
    clone_url = head_repo.get("clone_url")
    head_owner = (head_repo.get("owner") or {}).get("login")
    head_name = head_repo.get("name")

    if not head_ref or not clone_url or not head_owner or not head_name:
        return False, "PR metadata missing head ref or clone_url"

    refspec = f"HEAD:{head_ref}"
    if not quiet:
        console.print(f"[dim]Pushing fix to {clone_url} {refspec}[/dim]")

    success, push_err = push_with_retry(
        worktree,
        repo_owner=head_owner,
        repo_name=head_name,
        remote=clone_url,
        refspec=refspec,
        set_upstream=False,
    )
    if not success:
        return False, push_err
    return True, ""


def _run_fix(
    *,
    fixer_role: str,
    reviewer_role: str,
    config: ReviewLoopConfig,
    context: ReviewLoopContext,
    worktree: Path,
    artifacts: Path,
    round_number: int,
    findings: List[ReviewFinding],
    verbose: bool = False,
    quiet: bool = False,
    deadline: Optional[float] = None,
) -> FixResult:
    prompt = _build_fixer_prompt(
        fixer_role=fixer_role,
        config=config,
        context=context,
        findings=findings,
        round_number=round_number,
    )
    label = f"checkup-review-loop-fix-{fixer_role}-for-{reviewer_role}-round{round_number}"
    success, output, cost, model = _run_role_task(
        fixer_role,
        prompt,
            cwd=worktree,
            verbose=verbose,
            quiet=quiet,
            label=label,
            deadline=deadline,
            reasoning_time=config.reasoning_time,
        )

    parsed = _parse_fixer_output(output, findings, fixer_role, round_number)

    # Commit & push
    pushed = False
    push_error = ""
    if success:
        pushed, push_error = _commit_and_push_if_changed(worktree, context, quiet=quiet)
    else:
        push_error = "fixer subprocess failed; not pushing"

    result = FixResult(
        role=fixer_role,
        success=success and (pushed or not parsed["changed_files"]),
        summary=parsed["summary"],
        raw_output=output,
        cost=cost,
        model=model,
        changed_files=parsed["changed_files"],
        dispositions=parsed["dispositions"],
        rationales=parsed["rationales"],
        pushed=pushed,
        push_error=push_error,
        for_reviewer=reviewer_role,
        round_number=round_number,
    )

    base = artifacts / f"round-{round_number}-fix-{fixer_role}-for-{reviewer_role}"
    _write_artifact(base.with_suffix(".prompt.txt"), prompt)
    _write_artifact(base.with_suffix(".output.txt"), output)
    fixer_payload = {
        "summary": result.summary,
        "changed_files": result.changed_files,
        "dispositions": result.dispositions,
        "rationales": result.rationales,
        "pushed": result.pushed,
        "push_error": result.push_error,
    }
    _write_artifact(base.with_suffix(".findings.json"), json.dumps(fixer_payload, indent=2))

    return result


# ---------------------------------------------------------------------------
# Final report
# ---------------------------------------------------------------------------


def _required_findings(findings: Iterable[ReviewFinding], config: ReviewLoopConfig) -> List[ReviewFinding]:
    block = {s.lower() for s in config.blocking_severities}
    return [f for f in findings if f.severity.lower() in block and f.status == "open"]


def _escape_table_cell(text: str) -> str:
    if text is None:
        return ""
    return str(text).replace("|", "\\|").replace("\n", " ").replace("\r", " ").strip()


def _build_final_report(
    *,
    state: ReviewLoopState,
    config: ReviewLoopConfig,
    context: ReviewLoopContext,
    reviewer_role: str,
    fixer_role: str,
    issue_aligned: bool,
) -> str:
    lines: List[str] = []
    lines.append("## Step 7/8: Review Loop Final Report")
    lines.append("")
    lines.append(f"PR: {context.pr_url}")
    lines.append(f"Issue: {context.issue_url}")
    lines.append(f"issue_aligned: {'true' if issue_aligned else 'false'}")
    lines.append(
        f"reviewer-status: {reviewer_role}={state.reviewer_status} "
        f"{fixer_role}=fixer fresh-final={state.fresh_final_status}"
    )
    lines.append(f"fresh-final-review: {state.fresh_final_status}")
    lines.append(f"max-rounds-reached: {'true' if state.max_rounds_reached else 'false'}")
    lines.append(f"max-cost-reached: {'true' if state.max_cost_reached else 'false'}")
    lines.append(f"max-duration-reached: {'true' if state.max_duration_reached else 'false'}")
    lines.append("")

    lines.append("### Summary")
    lines.append("")
    lines.append(f"- Stop reason: {state.stop_reason or 'completed'}")
    lines.append(f"- Rounds completed: {state.rounds_completed}")
    lines.append(f"- Total cost: ${state.total_cost:.4f}")
    lines.append(f"- Last model: {state.last_model or 'n/a'}")
    if state.primary_unavailable_note:
        lines.append(f"- Note: {state.primary_unavailable_note}")
    if state.last_status_reason or state.last_error_class or state.last_exit_code is not None:
        lines.append("")
        lines.append("#### Diagnostics (last reviewer)")
        lines.append(f"- status_reason: {state.last_status_reason or 'n/a'}")
        lines.append(f"- error_class: {state.last_error_class or 'n/a'}")
        lines.append(f"- exit_code: {state.last_exit_code if state.last_exit_code is not None else 'n/a'}")
        if state.last_stderr_tail:
            lines.append("- stderr_tail:")
            lines.append("```")
            lines.append(state.last_stderr_tail)
            lines.append("```")
    lines.append("")

    lines.append("### Per-Reviewer Status")
    lines.append("")
    lines.append("| Role | Kind | Status |")
    lines.append("| --- | --- | --- |")
    lines.append(f"| {reviewer_role} | primary reviewer | {state.reviewer_status} |")
    lines.append(f"| {fixer_role} | fixer | applied={len(state.fix_results)} |")
    lines.append(f"| fresh-final | verifier | {state.fresh_final_status} |")
    lines.append("")

    lines.append("### Findings")
    lines.append("")
    lines.append("| Severity | Status | Location | Finding | Required fix | Reviewer |")
    lines.append("| --- | --- | --- | --- | --- | --- |")
    open_findings = [f for f in state.findings_by_key.values() if f.status not in {"fixed"}]
    if not open_findings:
        lines.append("| _none_ | - | - | - | - | - |")
    else:
        for f in open_findings:
            lines.append(
                f"| {_escape_table_cell(f.severity)} | {_escape_table_cell(f.status)} | "
                f"{_escape_table_cell(f.location)} | {_escape_table_cell(f.finding)} | "
                f"{_escape_table_cell(f.required_fix)} | {_escape_table_cell(f.reviewer)} |"
            )
    lines.append("")

    lines.append("### Fixer Rationale")
    lines.append("")
    if not open_findings:
        lines.append("- none")
    else:
        for f in open_findings:
            key = f.dedup_key()
            disp = ""
            for fr in reversed(state.fix_results):
                if key in fr.dispositions:
                    disp = fr.dispositions[key]
                    rationale = fr.rationales.get(key, "")
                    lines.append(f"- [{f.severity}] {_escape_table_cell(f.location)} — {disp}: {_escape_table_cell(rationale)}")
                    break
            if not disp:
                lines.append(f"- [{f.severity}] {_escape_table_cell(f.location)} — no fixer disposition recorded")
    lines.append("")

    lines.append("### Fixes Attempted")
    lines.append("")
    if not state.fix_results:
        lines.append("- none")
    else:
        # Determine global verification state
        no_open = not [f for f in state.findings_by_key.values() if f.status == "open"]
        safe_stop = not (state.max_rounds_reached or state.max_cost_reached or state.max_duration_reached)
        verifier_ok = state.fresh_final_status == "clean"
        verified = no_open and safe_stop and verifier_ok
        verification = "verified" if verified else "unverified"
        for fr in state.fix_results:
            files_part = f"files={len(fr.changed_files)}"
            push_part = "pushed" if fr.pushed else f"push_failed={_escape_table_cell(fr.push_error)}"
            lines.append(
                f"- round {fr.round_number}: {fr.role} for {fr.for_reviewer} — "
                f"{files_part}, {push_part}, verification={verification}, "
                f"summary={_escape_table_cell(fr.summary)[:200]}"
            )
    lines.append("")

    return "\n".join(lines)


def _post_to_github(
    *,
    use_github_state: bool,
    context: ReviewLoopContext,
    report: str,
    quiet: bool,
) -> None:
    if not use_github_state:
        return
    # Post to issue
    if context.repo_owner and context.repo_name and context.issue_number:
        body_json = json.dumps({"body": report})
        _ok, _out = _run_gh_command(
            [
                "api",
                "-X", "POST",
                f"repos/{context.repo_owner}/{context.repo_name}/issues/{context.issue_number}/comments",
                "-H", "Accept: application/vnd.github+json",
                "--input", "-",
            ],
            timeout=60,
        )
        # Use simpler approach: write to temp and gh issue comment
        try:
            import tempfile
            with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False, encoding="utf-8") as tf:
                tf.write(report)
                tmp_path = tf.name
            _run_gh_command(
                [
                    "issue", "comment", str(context.issue_number),
                    "--repo", f"{context.repo_owner}/{context.repo_name}",
                    "--body-file", tmp_path,
                ],
                timeout=60,
            )
        except Exception as e:
            if not quiet:
                console.print(f"[yellow]Failed to post issue comment: {e}[/yellow]")

    # Post to PR
    if context.pr_owner and context.pr_repo and context.pr_number:
        try:
            import tempfile
            with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False, encoding="utf-8") as tf:
                tf.write(report)
                tmp_path = tf.name
            _run_gh_command(
                [
                    "pr", "comment", str(context.pr_number),
                    "--repo", f"{context.pr_owner}/{context.pr_repo}",
                    "--body-file", tmp_path,
                ],
                timeout=60,
            )
        except Exception as e:
            if not quiet:
                console.print(f"[yellow]Failed to post PR comment: {e}[/yellow]")


# ---------------------------------------------------------------------------
# Main entry
# ---------------------------------------------------------------------------


def _merge_findings(
    state: ReviewLoopState,
    findings: List[ReviewFinding],
    *,
    reviewer_role: str,
) -> List[ReviewFinding]:
    """Merge new findings into state.findings_by_key. Return the deduped new findings."""
    new_or_updated: List[ReviewFinding] = []
    for f in findings:
        f.reviewer = f.reviewer or reviewer_role
        k = f.dedup_key()
        if k in state.findings_by_key:
            existing = state.findings_by_key[k]
            existing.round_number = f.round_number
            if existing.status == "fixed":
                existing.status = "open"
            new_or_updated.append(existing)
        else:
            state.findings_by_key[k] = f
            new_or_updated.append(f)
    return new_or_updated


def _mark_absent_as_fixed(
    state: ReviewLoopState,
    prior_keys: Iterable[str],
    re_reported_keys: set[str],
) -> None:
    for k in prior_keys:
        if k in re_reported_keys:
            continue
        if k in state.findings_by_key:
            state.findings_by_key[k].status = "fixed"


def _apply_fixer_dispositions(state: ReviewLoopState, fix_result: FixResult) -> None:
    for k, disp in fix_result.dispositions.items():
        if k not in state.findings_by_key:
            continue
        # The finding only closes if the primary reviewer accepts the rationale
        # on the next verify pass. We just record the latest disposition.
        state.dispute_notes_by_key[k] = f"{disp}: {fix_result.rationales.get(k, '')}"
        state.fix_attempts_by_key[k] = state.fix_attempts_by_key.get(k, 0) + 1


def _is_hard_not_clean(status: str) -> bool:
    return status in HARD_NOT_CLEAN


def run_checkup_review_loop(
    *,
    context: ReviewLoopContext,
    config: ReviewLoopConfig,
    cwd: Path,
    verbose: bool = False,
    quiet: bool = False,
    use_github_state: bool = True,
) -> Tuple[bool, str, float, str]:
    """Run the PR-mode primary-reviewer/fixer review loop.

    Returns (success, report_str, total_cost, last_model).
    """
    state = ReviewLoopState()
    artifacts = _artifacts_dir(cwd, context.issue_number, context.pr_number)
    artifacts.mkdir(parents=True, exist_ok=True)

    reviewer_role, fixer_role = _resolve_roles(config)
    state.fixer_role = fixer_role

    # Reviewer/fixer must be different (skip in review-only mode).
    if not config.review_only and reviewer_role == fixer_role:
        state.reviewer_status = "failed"
        state.fresh_final_status = "missing"
        state.stop_reason = (
            f"reviewer and fixer must be different roles "
            f"(both resolved to '{reviewer_role}')"
        )
        report = _build_final_report(
            state=state, config=config, context=context,
            reviewer_role=reviewer_role, fixer_role=fixer_role,
            issue_aligned=False,
        )
        _write_artifact(artifacts / "final-report.md", report)
        _write_artifact(artifacts / "final-state.json", json.dumps(_state_to_dict(state), indent=2))
        _post_to_github(use_github_state=use_github_state, context=context, report=report, quiet=quiet)
        return True, report, 0.0, ""

    # Set up the worktree once for the whole loop.
    worktree: Optional[Path] = None
    if context.pr_owner and context.pr_repo and context.pr_number:
        wt, err = _setup_pr_worktree(
            cwd, context.pr_owner, context.pr_repo, context.pr_number,
            quiet=quiet, resume_existing=False,
        )
        if wt is None:
            state.reviewer_status = "failed"
            state.fresh_final_status = "missing"
            state.stop_reason = f"failed to set up PR worktree: {err}"
            report = _build_final_report(
                state=state, config=config, context=context,
                reviewer_role=reviewer_role, fixer_role=fixer_role,
                issue_aligned=False,
            )
            _write_artifact(artifacts / "final-report.md", report)
            _write_artifact(artifacts / "final-state.json", json.dumps(_state_to_dict(state), indent=2))
            _post_to_github(use_github_state=use_github_state, context=context, report=report, quiet=quiet)
            return True, report, 0.0, ""
        worktree = wt
    else:
        # No PR context — fall back to git root.
        worktree = _get_git_root(cwd) or cwd

    start_time = time.time()
    deadline = start_time + (config.max_minutes * 60.0)

    def _budget_check() -> bool:
        """Return True if any budget cap has been exceeded."""
        if state.total_cost >= config.max_cost:
            state.max_cost_reached = True
            state.stop_reason = state.stop_reason or f"max_cost ${config.max_cost} reached"
            return True
        elapsed_min = (time.time() - start_time) / 60.0
        if elapsed_min >= config.max_minutes:
            state.max_duration_reached = True
            state.stop_reason = state.stop_reason or f"max_minutes {config.max_minutes} reached"
            return True
        return False

    pending_findings: List[ReviewFinding] = []
    last_fix_result: Optional[FixResult] = None
    round_number = 0

    while round_number < max(1, config.max_rounds):
        round_number += 1
        state.rounds_completed = round_number

        # Decide mode: first round or no pending verifier findings -> review.
        # If we have pending findings to verify (after a fix), use verify mode.
        if last_fix_result is not None and pending_findings:
            mode = "verify"
        else:
            mode = "review"

        # === Reviewer pass (primary) ===
        review = _run_review(
            mode=mode,
            reviewer_role=reviewer_role,
            config=config,
            context=context,
            worktree=worktree,
            artifacts=artifacts,
            round_number=round_number,
            prior_findings=pending_findings if mode == "verify" else None,
            fixer_dispositions=last_fix_result.dispositions if last_fix_result else None,
            fixer_rationales=last_fix_result.rationales if last_fix_result else None,
            fix_summary=last_fix_result.summary if last_fix_result else "",
            verbose=verbose,
            quiet=quiet,
            deadline=deadline,
        )

        state.total_cost += review.cost
        if review.model:
            state.last_model = review.model
        state.last_review_result = review
        state.reviewer_status = review.status
        state.last_status_reason = review.status_reason
        state.last_exit_code = review.exit_code
        state.last_stderr_tail = review.stderr_tail
        state.last_error_class = review.error_class

        # Promote-on-failure: try secondary reviewer (the fixer role) for the same review pass.
        if _is_hard_not_clean(review.status) and config.reviewer_fallback and not config.review_only:
            if not quiet:
                console.print(
                    f"[yellow]Primary reviewer '{reviewer_role}' status={review.status}; "
                    f"trying secondary reviewer '{fixer_role}'[/yellow]"
                )
            secondary = _run_review(
                mode=mode,
                reviewer_role=fixer_role,
                config=config,
                context=context,
                worktree=worktree,
                artifacts=artifacts,
                round_number=round_number,
                prior_findings=pending_findings if mode == "verify" else None,
                fixer_dispositions=last_fix_result.dispositions if last_fix_result else None,
                fixer_rationales=last_fix_result.rationales if last_fix_result else None,
                fix_summary=last_fix_result.summary if last_fix_result else "",
                verbose=verbose,
                quiet=quiet,
                deadline=deadline,
            )
            state.total_cost += secondary.cost
            if secondary.model:
                state.last_model = secondary.model
            if not _is_hard_not_clean(secondary.status):
                state.primary_unavailable_note = (
                    f"Primary reviewer '{reviewer_role}' was unavailable "
                    f"({review.status}: {review.status_reason}); "
                    f"used secondary reviewer '{fixer_role}'."
                )
                review = secondary
                state.reviewer_status = review.status
                state.last_status_reason = review.status_reason
                state.last_exit_code = review.exit_code
                state.last_stderr_tail = review.stderr_tail
                state.last_error_class = review.error_class
                state.last_review_result = review
            else:
                # Both failed; preserve original primary failure but record secondary attempted
                state.primary_unavailable_note = (
                    f"Primary '{reviewer_role}' and secondary '{fixer_role}' both failed."
                )

        # Process review outcome
        prior_keys = [f.dedup_key() for f in pending_findings] if mode == "verify" else []

        if review.status == "clean":
            # Mark all prior pending findings as fixed
            if mode == "verify":
                for k in prior_keys:
                    if k in state.findings_by_key:
                        state.findings_by_key[k].status = "fixed"
            state.fresh_final_status = "clean"
            state.stop_reason = state.stop_reason or "reviewer reported no actionable findings"
            _write_dedup_state(artifacts / f"dedup-state-round-{round_number}.json", state)
            break

        if _is_hard_not_clean(review.status):
            state.fresh_final_status = review.status
            state.stop_reason = state.stop_reason or f"reviewer status={review.status}: {review.status_reason}"
            _write_dedup_state(artifacts / f"dedup-state-round-{round_number}.json", state)
            break

        # status == "findings"
        merged = _merge_findings(state, review.findings, reviewer_role=review.role)
        new_keys = {f.dedup_key() for f in merged}

        if mode == "verify":
            # Mark absent prior findings fixed; keep only re-reported open
            _mark_absent_as_fixed(state, prior_keys, new_keys)

        # Mark fresh-final state
        state.fresh_final_status = "findings"

        _write_dedup_state(artifacts / f"dedup-state-round-{round_number}.json", state)

        # === review_only short-circuit ===
        if config.review_only:
            state.stop_reason = state.stop_reason or "review-only mode reported findings"
            state.fresh_final_status = "missing"
            break

        # Budget gate before fix
        if _budget_check():
            break

        # === Fixer pass ===
        actionable = [f for f in state.findings_by_key.values() if f.status == "open"]
        if not actionable:
            state.fresh_final_status = "clean"
            state.stop_reason = state.stop_reason or "no open findings remain"
            break

        fix_result = _run_fix(
            fixer_role=fixer_role,
            reviewer_role=reviewer_role,
            config=config,
            context=context,
            worktree=worktree,
            artifacts=artifacts,
            round_number=round_number,
            findings=actionable,
            verbose=verbose,
            quiet=quiet,
            deadline=deadline,
        )
        state.total_cost += fix_result.cost
        if fix_result.model:
            state.last_model = fix_result.model
        state.fix_results.append(fix_result)
        _apply_fixer_dispositions(state, fix_result)
        _write_dedup_state(artifacts / f"dedup-state-round-{round_number}.json", state)

        if not fix_result.pushed and fix_result.changed_files:
            state.stop_reason = (
                f"fixer push failed: {fix_result.push_error or 'unknown'}; "
                "verifier not run against unpushed changes"
            )
            state.fresh_final_status = "missing"
            break

        if not fix_result.pushed and not fix_result.changed_files:
            # Fixer made no code changes (likely all not_valid/blocked).
            # Feed back to reviewer in next round as verify with these dispositions.
            pending_findings = list(actionable)
            last_fix_result = fix_result
        else:
            pending_findings = list(actionable)
            last_fix_result = fix_result

        # Budget gate after fix
        if _budget_check():
            break

    else:
        # Loop finished normally without break — max_rounds reached
        state.max_rounds_reached = True
        state.stop_reason = state.stop_reason or f"max_rounds {config.max_rounds} reached"
        if state.fresh_final_status not in {"clean"}:
            # Leave whatever fresh_final_status we last set
            pass

    # Detect max_rounds reached even when we exited via `break`
    if round_number >= config.max_rounds and state.fresh_final_status not in {"clean"} and not state.max_rounds_reached:
        # Only set if we genuinely exhausted rounds
        if state.fresh_final_status == "findings":
            state.max_rounds_reached = True
            state.stop_reason = state.stop_reason or f"max_rounds {config.max_rounds} reached"
    # Issue alignment heuristic
    issue_aligned = state.fresh_final_status == "clean"

    report = _build_final_report(
        state=state,
        config=config,
        context=context,
        reviewer_role=reviewer_role,
        fixer_role=fixer_role,
        issue_aligned=issue_aligned,
    )


    _write_artifact(artifacts / "final-report.md", report)
    _write_artifact(artifacts / "final-state.json", json.dumps(_state_to_dict(state), indent=2))

    _post_to_github(use_github_state=use_github_state, context=context, report=report, quiet=quiet)

    return True, report, state.total_cost, state.last_model


def _state_to_dict(state: ReviewLoopState) -> Dict[str, Any]:
    return {
        "reviewer_status": state.reviewer_status,
        "fresh_final_status": state.fresh_final_status,
        "stop_reason": state.stop_reason,
        "total_cost": state.total_cost,
        "last_model": state.last_model,
        "max_rounds_reached": state.max_rounds_reached,
        "max_cost_reached": state.max_cost_reached,
        "max_duration_reached": state.max_duration_reached,
        "fix_attempts_by_key": state.fix_attempts_by_key,
        "dispute_notes_by_key": state.dispute_notes_by_key,
        "reviewer_feedback_by_key": state.reviewer_feedback_by_key,
        "primary_unavailable_note": state.primary_unavailable_note,
        "diagnostics": {
            "status_reason": state.last_status_reason,
            "exit_code": state.last_exit_code,
            "stderr_tail": state.last_stderr_tail,
            "error_class": state.last_error_class,
        },
        "findings": [
            {"key": k, **f.to_dict()} for k, f in state.findings_by_key.items()
        ],
    }