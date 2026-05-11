from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
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
from urllib.parse import quote

from .agentic_e2e_fix_orchestrator import push_with_retry
from rich.console import Console

console = Console()


# ---------------------------------------------------------------------------
# Constants
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

DEFAULT_REVIEWER: str = "codex"
DEFAULT_FIXER: str = "claude"

DEFAULT_BLOCKING_SEVERITIES: Tuple[str, ...] = ("blocker", "critical", "medium")
DEFAULT_CLEAN_REVIEWER_STATES: Tuple[str, ...] = ("clean",)
HARD_NOT_CLEAN_STATES: Tuple[str, ...] = ("degraded", "failed", "missing")

SEVERITY_ORDER: Tuple[str, ...] = ("blocker", "critical", "high", "medium", "low", "info")

# Markers to classify reviewer failures.
PROVIDER_LIMIT_MARKERS: Tuple[str, ...] = (
    "rate limit",
    "rate-limit",
    "rate_limit",
    "quota",
    "context window",
    "context-window",
    "context length",
    "max tokens",
    "context_length_exceeded",
    "timeout",
    "timed out",
)

INFRA_FAILURE_MARKERS: Tuple[str, ...] = (
    "auth",
    "unauthorized",
    "login",
    "network",
    "connection",
    "non-zero exit",
    "exit code",
    "exit status",
    "permission denied",
    "sandbox",
)


# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------


@dataclass
class ReviewLoopContext:
    """Inputs the orchestrator gathers before invoking the loop."""

    pr_url: str
    pr_owner: str
    pr_repo: str
    pr_number: int
    issue_url: str
    issue_owner: str
    issue_repo: str
    issue_number: int
    issue_title: str = ""
    issue_body: str = ""
    pr_title: str = ""
    pr_body: str = ""
    pr_head_ref: str = ""
    pr_base_ref: str = ""
    pr_head_clone_url: str = ""
    pr_changed_files: Tuple[str, ...] = field(default_factory=tuple)
    pr_comments: Tuple[Dict[str, Any], ...] = field(default_factory=tuple)
    pr_reviews: Tuple[Dict[str, Any], ...] = field(default_factory=tuple)
    architecture_json: str = ""
    pddrc_content: str = ""


@dataclass
class ReviewLoopConfig:
    """Knobs controlling reviewer/fixer behavior and budget caps."""

    reviewers: Sequence[str] = field(default_factory=tuple)
    reviewer: Optional[str] = None
    fixer: Optional[str] = None
    reviewer_fallback: Optional[str] = None
    max_rounds: int = 3
    max_cost: float = 10.0
    max_minutes: float = 60.0
    review_only: bool = False
    blocking_severities: Tuple[str, ...] = DEFAULT_BLOCKING_SEVERITIES
    clean_reviewer_states: Tuple[str, ...] = DEFAULT_CLEAN_REVIEWER_STATES
    require_all_reviewers_clean: bool = True
    continue_on_reviewer_limit: bool = False


@dataclass
class ReviewFinding:
    """A normalized finding from a reviewer."""

    severity: str
    reviewer: str
    area: str
    evidence: str
    finding: str
    required_fix: str
    location: str
    status: str = "open"  # open|fixed|disputed
    round_number: int = 0

    def dedup_key(self) -> str:
        return _dedup_key(self.severity, self.location, self.finding, self.required_fix)

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


@dataclass
class ReviewResult:
    """Result of a single reviewer (or verifier) invocation."""

    reviewer: str
    mode: str  # "review" or "verify"
    status: str  # clean|findings|failed|degraded|missing
    findings: List[ReviewFinding]
    raw_output: str
    cost: float
    model: str
    round_number: int


@dataclass
class FixResult:
    """Result of a single fixer invocation."""

    fixer: str
    summary: str
    changed_files: List[str]
    dispositions: Dict[str, str]
    rationales: Dict[str, str]
    cost: float
    model: str
    round_number: int
    pushed: bool = False
    push_message: str = ""
    verified: bool = False


@dataclass
class ReviewLoopState:
    """Mutable state carried across rounds."""

    reviewer_status: Dict[str, str] = field(default_factory=dict)
    active_reviewer: str = ""
    fresh_final_status: str = "missing"
    stop_reason: str = ""
    total_cost: float = 0.0
    last_model: str = ""
    max_rounds_reached: bool = False
    max_cost_reached: bool = False
    max_duration_reached: bool = False
    findings_by_key: Dict[str, ReviewFinding] = field(default_factory=dict)
    fix_attempts_by_key: Dict[str, int] = field(default_factory=dict)
    dispute_notes_by_key: Dict[str, str] = field(default_factory=dict)
    reviewer_feedback_by_key: Dict[str, str] = field(default_factory=dict)
    fix_results: List[FixResult] = field(default_factory=list)
    review_results: List[ReviewResult] = field(default_factory=list)
    fallback_used: bool = False
    primary_reviewer: str = ""
    fixer_role: str = ""
    fallback_role: Optional[str] = None


# ---------------------------------------------------------------------------
# Helpers: parsing / normalization
# ---------------------------------------------------------------------------


def parse_reviewers(value: str | Sequence[str] | None) -> Tuple[str, ...]:
    """Normalize a reviewers spec to a tuple of canonical role names."""
    if value is None:
        return ()
    if isinstance(value, str):
        raw_parts = [p.strip() for p in re.split(r"[,\s]+", value) if p.strip()]
    else:
        raw_parts = []
        for item in value:
            if not isinstance(item, str):
                continue
            raw_parts.extend([p.strip() for p in re.split(r"[,\s]+", item) if p.strip()])
    out: List[str] = []
    seen: set[str] = set()
    for part in raw_parts:
        canonical = ROLE_ALIASES.get(part.lower())
        if canonical and canonical not in seen:
            out.append(canonical)
            seen.add(canonical)
    return tuple(out)


def _normalize_role(value: Optional[str]) -> Optional[str]:
    """Normalize a single role string via the alias table."""
    if not value:
        return None
    return ROLE_ALIASES.get(value.strip().lower())


def _dedup_key(severity: str, location: str, finding: str, required_fix: str) -> str:
    raw = "|".join([
        (severity or "").strip().lower(),
        (location or "").strip(),
        _compact(finding),
        _compact(required_fix),
    ])
    return raw[:500]


def _compact(text: str) -> str:
    if not text:
        return ""
    return re.sub(r"\s+", " ", text).strip()


def _normalize_severity(value: str) -> str:
    if not value:
        return "medium"
    s = value.strip().lower()
    mapping = {
        "p0": "blocker",
        "p1": "critical",
        "p2": "medium",
        "p3": "low",
        "blocking": "blocker",
        "high": "critical",
        "minor": "low",
    }
    if s in mapping:
        return mapping[s]
    if s in SEVERITY_ORDER:
        return s
    return "medium"


# ---------------------------------------------------------------------------
# Findings parsing
# ---------------------------------------------------------------------------


_EXTERNAL_NOISE_TERMS: Tuple[str, ...] = (
    "auto-heal-pr",
    "auto heal pr",
    "github status",
    "cloud build",
    "mergeability",
    "synthetic merge",
    "required check",
    "required-check",
    "action required",
    "action-required",
    "pending check",
)


def _is_external_noise(finding: ReviewFinding) -> bool:
    """Drop external CI/PR-state findings that have no concrete repo location."""
    if finding.location and (("/" in finding.location) or finding.location.endswith(".py")):
        return False
    text = " ".join([finding.finding, finding.required_fix, finding.evidence]).lower()
    return any(term in text for term in _EXTERNAL_NOISE_TERMS)


def _extract_json_block(text: str) -> Optional[str]:
    """Extract a JSON object/array string from reviewer output."""
    if not text:
        return None
    fenced = re.findall(r"```json\s*(.+?)```", text, re.DOTALL | re.IGNORECASE)
    if fenced:
        return fenced[0].strip()
    fenced_any = re.findall(r"```\s*(\{.+?\}|\[.+?\])\s*```", text, re.DOTALL)
    if fenced_any:
        return fenced_any[0].strip()
    # First/last brace fallback for objects.
    first_brace = text.find("{")
    last_brace = text.rfind("}")
    if first_brace != -1 and last_brace > first_brace:
        candidate = text[first_brace : last_brace + 1]
        try:
            json.loads(candidate)
            return candidate
        except Exception:
            pass
    first_bracket = text.find("[")
    last_bracket = text.rfind("]")
    if first_bracket != -1 and last_bracket > first_bracket:
        candidate = text[first_bracket : last_bracket + 1]
        try:
            json.loads(candidate)
            return candidate
        except Exception:
            pass
    return None


def _findings_from_json(payload: Any, reviewer: str, round_number: int) -> Tuple[Optional[str], List[ReviewFinding]]:
    """Return (status, findings) from a parsed JSON payload."""
    findings: List[ReviewFinding] = []
    status: Optional[str] = None

    if isinstance(payload, dict):
        status_val = payload.get("status")
        if isinstance(status_val, str):
            s = status_val.strip().lower()
            if s in ("clean", "findings", "failed", "degraded", "missing"):
                status = s
        items = payload.get("findings")
        if isinstance(items, list):
            for item in items:
                f = _finding_from_dict(item, reviewer, round_number)
                if f is not None:
                    findings.append(f)
    elif isinstance(payload, list):
        for item in payload:
            f = _finding_from_dict(item, reviewer, round_number)
            if f is not None:
                findings.append(f)

    return status, findings


def _finding_from_dict(item: Any, reviewer: str, round_number: int) -> Optional[ReviewFinding]:
    if not isinstance(item, dict):
        return None
    severity = _normalize_severity(str(item.get("severity", "medium")))
    finding_text = str(item.get("finding") or item.get("message") or item.get("description") or "").strip()
    if not finding_text:
        return None
    return ReviewFinding(
        severity=severity,
        reviewer=reviewer,
        area=str(item.get("area", "")).strip(),
        evidence=str(item.get("evidence", "")).strip(),
        finding=finding_text,
        required_fix=str(item.get("required_fix") or item.get("fix") or "").strip(),
        location=str(item.get("location") or item.get("file") or "").strip(),
        status="open",
        round_number=round_number,
    )


_BRACKET_LINE_RE = re.compile(r"^\s*[-*]?\s*\[(?P<sev>[A-Za-z0-9]+)\]\s*(?P<rest>.+)$")
_PRIORITY_LINK_RE = re.compile(
    r"^\s*[-*]\s*\[(?P<prio>P[0-3])\]\s*\[(?P<label>[^\]]+)\]\(\s*(?P<loc>[^)]+)\)\s*(?P<rest>.+)$"
)
_NUMBERED_SEV_RE = re.compile(
    r"^\s*\d+\.\s*(?P<sev>Blocking|High|Critical|Blocker|Medium|Low|Info)\s*[:\-]\s*(?P<rest>.+)$",
    re.IGNORECASE,
)
_BULLET_SEV_RE = re.compile(
    r"^\s*[-*]\s*(?P<sev>Blocking|High|Critical|Blocker|Medium|Low|Info)\s*[:\-]\s*(?P<rest>.+)$",
    re.IGNORECASE,
)
_NUMBERED_BOLD_RE = re.compile(r"^\s*\d+\.\s*\*\*(?P<title>[^*]+)\*\*\s*(?P<rest>.*)$")
_LINK_PATH_RE = re.compile(r"\[(?P<label>[^\]]+)\]\(\s*(?P<loc>[^)]+\.py(?::\d+)?)\s*\)")
_FREEFORM_LEAD_RE = re.compile(r"^(?P<sev>Blocking|Blocker|Critical|High|Medium|Low|Info)\b", re.IGNORECASE)


def _parse_text_findings(text: str, reviewer: str, round_number: int) -> List[ReviewFinding]:
    """Best-effort parse of free-form reviewer text into findings."""
    findings: List[ReviewFinding] = []
    if not text:
        return findings

    lines = text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        m = _PRIORITY_LINK_RE.match(stripped)
        if m:
            findings.append(
                ReviewFinding(
                    severity=_normalize_severity(m.group("prio")),
                    reviewer=reviewer,
                    area="",
                    evidence="",
                    finding=m.group("rest").strip(),
                    required_fix="",
                    location=m.group("loc").strip(),
                    status="open",
                    round_number=round_number,
                )
            )
            i += 1
            continue

        m = _BRACKET_LINE_RE.match(stripped)
        if m:
            findings.append(
                ReviewFinding(
                    severity=_normalize_severity(m.group("sev")),
                    reviewer=reviewer,
                    area="",
                    evidence="",
                    finding=m.group("rest").strip(),
                    required_fix="",
                    location="",
                    status="open",
                    round_number=round_number,
                )
            )
            i += 1
            continue

        m = _NUMBERED_SEV_RE.match(stripped) or _BULLET_SEV_RE.match(stripped)
        if m:
            findings.append(
                ReviewFinding(
                    severity=_normalize_severity(m.group("sev")),
                    reviewer=reviewer,
                    area="",
                    evidence="",
                    finding=m.group("rest").strip(),
                    required_fix="",
                    location="",
                    status="open",
                    round_number=round_number,
                )
            )
            i += 1
            continue

        m = _NUMBERED_BOLD_RE.match(stripped)
        if m:
            title = m.group("title").strip().rstrip(".")
            rest = m.group("rest").strip()
            # Heading-level severity inference.
            sev_match = _FREEFORM_LEAD_RE.match(title)
            severity = _normalize_severity(sev_match.group("sev")) if sev_match else "medium"
            # Look ahead for explanatory paragraph for evidence/location.
            evidence_lines: List[str] = []
            location = ""
            j = i + 1
            while j < len(lines):
                nxt = lines[j].strip()
                if not nxt:
                    j += 1
                    continue
                if _NUMBERED_BOLD_RE.match(nxt) or _NUMBERED_SEV_RE.match(nxt) or _BULLET_SEV_RE.match(nxt):
                    break
                evidence_lines.append(nxt)
                if not location:
                    link = _LINK_PATH_RE.search(nxt)
                    if link:
                        location = link.group("loc").strip()
                # Stop after a small window
                if len(evidence_lines) >= 3:
                    j += 1
                    break
                j += 1
            findings.append(
                ReviewFinding(
                    severity=severity,
                    reviewer=reviewer,
                    area="",
                    evidence=" ".join(evidence_lines)[:1000],
                    finding=(title + " " + rest).strip(),
                    required_fix="",
                    location=location,
                    status="open",
                    round_number=round_number,
                )
            )
            i = j if j > i else i + 1
            continue

        # Concrete unprioritized markdown bullet under **Findings**: `- [path:line](url) message`
        link = _LINK_PATH_RE.search(stripped)
        if link and stripped.lstrip().startswith(("-", "*")):
            findings.append(
                ReviewFinding(
                    severity="medium",
                    reviewer=reviewer,
                    area="",
                    evidence="",
                    finding=stripped.lstrip("-* ").strip(),
                    required_fix="",
                    location=link.group("loc").strip(),
                    status="open",
                    round_number=round_number,
                )
            )
            i += 1
            continue

        i += 1

    return findings


_CLEAN_LINE_PATTERNS: Tuple[re.Pattern[str], ...] = (
    re.compile(r"^\s*findings:\s*none\s*\.?\s*$", re.IGNORECASE),
    re.compile(r"^\s*no actionable findings\.?\s*$", re.IGNORECASE),
)
_VERIFIER_CLEAN_PREFIX_RE = re.compile(r"^\s*no actionable issues found\.?\s*(.*)$", re.IGNORECASE)
_NEGATING_WORDS: Tuple[str, ...] = (" but ", " however", " failed", " error")


def _is_explicit_clean(text: str) -> bool:
    if not text:
        return False
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        for pat in _CLEAN_LINE_PATTERNS:
            if pat.match(line):
                return True
        m = _VERIFIER_CLEAN_PREFIX_RE.match(line)
        if m:
            tail = (" " + m.group(1).lower() + " ")
            if not any(w in tail for w in _NEGATING_WORDS):
                return True
    return False


def _failure_status(text: str, *, success: bool, continue_on_limit: bool) -> Optional[str]:
    """Classify reviewer failure mode based on output / success flag."""
    lower = (text or "").lower()
    has_provider_limit = any(m in lower for m in PROVIDER_LIMIT_MARKERS)
    has_infra = any(m in lower for m in INFRA_FAILURE_MARKERS)
    if not success or has_provider_limit or has_infra:
        if continue_on_limit:
            return "degraded"
        return "failed"
    return None


def _normalize_findings(
    raw_output: str,
    *,
    reviewer: str,
    round_number: int,
    success: bool,
    continue_on_limit: bool,
) -> Tuple[str, List[ReviewFinding]]:
    """Normalize raw reviewer output into (status, findings)."""

    failure = _failure_status(raw_output, success=success, continue_on_limit=continue_on_limit)
    if failure is not None and not raw_output.strip():
        return failure, []

    json_text = _extract_json_block(raw_output)
    parsed_status: Optional[str] = None
    findings: List[ReviewFinding] = []
    if json_text:
        try:
            payload = json.loads(json_text)
            parsed_status, findings = _findings_from_json(payload, reviewer, round_number)
        except Exception:
            parsed_status = None
            findings = []

    if not findings:
        findings = _parse_text_findings(raw_output, reviewer, round_number)

    # Filter external CI/PR-state noise.
    filtered = [f for f in findings if not _is_external_noise(f)]
    dropped_external = bool(findings) and not filtered
    findings = filtered

    if findings:
        return ("findings" if parsed_status not in ("clean",) else parsed_status), findings

    if parsed_status == "clean":
        return "clean", []

    if dropped_external:
        # All parsed findings were external noise; treat as clean unless hard not-clean.
        if failure in HARD_NOT_CLEAN_STATES:
            return failure, []
        return "clean", []

    if _is_explicit_clean(raw_output):
        return "clean", []

    if failure is not None:
        return failure, []

    # Successful call returned non-JSON unparsable output.
    return "unparsable", []


# ---------------------------------------------------------------------------
# Worktree / git helpers
# ---------------------------------------------------------------------------


def _run_git(args: List[str], cwd: Path, *, check: bool = False) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=str(cwd),
        capture_output=True,
        text=True,
        check=check,
    )


def _get_git_root(cwd: Path) -> Path:
    try:
        proc = _run_git(["rev-parse", "--show-toplevel"], cwd)
        if proc.returncode == 0 and proc.stdout.strip():
            return Path(proc.stdout.strip())
    except Exception:
        pass
    return cwd


def _setup_pr_worktree(
    cwd: Path,
    pr_owner: str,
    pr_repo: str,
    pr_number: int,
    quiet: bool,
    *,
    resume_existing: bool = False,
) -> Tuple[Optional[Path], Optional[str]]:
    """Create a single worktree for the PR head ref.

    Returns ``(worktree_path, error_message)``; ``error_message`` is ``None`` on success.
    """
    git_root = _get_git_root(cwd)
    worktree_dir = git_root / ".pdd" / "checkup-review-loop" / f"worktree-pr-{pr_number}"
    branch_name = f"pdd-checkup-review-pr-{pr_number}"
    ref = f"pull/{pr_number}/head"

    try:
        # Fetch the PR head into a local ref.
        fetch = _run_git(["fetch", "origin", f"{ref}:{branch_name}"], git_root)
        if fetch.returncode != 0:
            # Try alternate fetch syntax.
            fetch_alt = _run_git(["fetch", "origin", ref], git_root)
            if fetch_alt.returncode != 0:
                return None, f"git fetch failed: {fetch.stderr.strip() or fetch_alt.stderr.strip()}"

        if worktree_dir.exists():
            # Reuse existing worktree by checking out branch inside it.
            if not quiet:
                console.print(f"[yellow]Reusing existing worktree at {worktree_dir}[/yellow]")
        else:
            worktree_dir.parent.mkdir(parents=True, exist_ok=True)
            add = _run_git(
                ["worktree", "add", "-B", branch_name, str(worktree_dir), f"origin/{branch_name}"],
                git_root,
            )
            if add.returncode != 0:
                # Try without -B, using FETCH_HEAD if we just fetched.
                add2 = _run_git(["worktree", "add", str(worktree_dir), branch_name], git_root)
                if add2.returncode != 0:
                    add3 = _run_git(["worktree", "add", str(worktree_dir), "FETCH_HEAD"], git_root)
                    if add3.returncode != 0:
                        return None, (
                            f"git worktree add failed: {add.stderr.strip() or add2.stderr.strip() or add3.stderr.strip()}"
                        )
        return worktree_dir, None
    except Exception as exc:  # pragma: no cover - defensive
        return None, f"worktree setup error: {exc}"


# ---------------------------------------------------------------------------
# PR metadata + push
# ---------------------------------------------------------------------------


def _fetch_pr_metadata(
    pr_owner: str,
    pr_repo: str,
    pr_number: int,
    cwd: Path,
) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    """Fetch PR metadata from `gh api`. Returns (metadata, error)."""
    if not shutil.which("gh"):
        return None, "gh CLI not found"
    try:
        proc = subprocess.run(
            ["gh", "api", f"repos/{pr_owner}/{pr_repo}/pulls/{pr_number}"],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode != 0:
            return None, f"gh api failed: {proc.stderr.strip()}"
        data = json.loads(proc.stdout)
        head = data.get("head") or {}
        head_ref = head.get("ref", "")
        head_repo = head.get("repo") or {}
        clone_url = head_repo.get("clone_url", "")
        if not head_ref or not clone_url:
            return None, "missing head_ref/clone_url in PR metadata"
        return {"head_ref": head_ref, "clone_url": clone_url, "raw": data}, None
    except Exception as exc:  # pragma: no cover - defensive
        return None, f"PR metadata error: {exc}"


def _read_token_from_file() -> Optional[str]:
    path = os.environ.get("PDD_GH_TOKEN_FILE")
    if not path:
        return None
    try:
        token = Path(path).read_text(encoding="utf-8").strip()
        return token or None
    except Exception:
        return None


def _resolve_gh_token() -> Optional[str]:
    token = _read_token_from_file()
    if token:
        return token
    for env_var in ("GH_TOKEN", "GITHUB_TOKEN", "PDD_GITHUB_TOKEN"):
        val = os.environ.get(env_var, "").strip()
        if val:
            return val
    return None


def _is_auth_failure(stderr: str) -> bool:
    if not stderr:
        return False
    s = stderr.lower()
    return any(
        marker in s
        for marker in (
            "authentication failed",
            "http 401",
            "could not read username",
            "http basic: access denied",
        )
    )


def push_with_retry(
    cwd: Path,
    remote: str,
    repo_owner: str,
    repo_name: str,
    refspec: str,
) -> Tuple[bool, str]:
    """Authenticated push helper shared with agentic_e2e_fix_orchestrator."""
    # Try plain push first.
    proc = subprocess.run(
        ["git", "push", remote, refspec],
        cwd=str(cwd),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode == 0:
        return True, proc.stdout.strip() or "pushed"

    stderr = proc.stderr or ""
    # Non-fast-forward retry.
    if "non-fast-forward" in stderr.lower() or "rejected" in stderr.lower():
        proc2 = subprocess.run(
            ["git", "push", "--force-with-lease", remote, refspec],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            check=False,
        )
        if proc2.returncode == 0:
            return True, proc2.stdout.strip() or "pushed (force-with-lease)"
        stderr = proc2.stderr or stderr

    if _is_auth_failure(stderr):
        token = _resolve_gh_token()
        if not token:
            return False, f"auth failure and no token available: {stderr.strip()}"
        # Save original URL.
        original_url_proc = subprocess.run(
            ["git", "remote", "get-url", remote],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            check=False,
        )
        original_url = original_url_proc.stdout.strip() if original_url_proc.returncode == 0 else ""
        token_url = f"https://x-access-token:{quote(token, safe='')}@github.com/{repo_owner}/{repo_name}.git"
        try:
            subprocess.run(
                ["git", "remote", "set-url", remote, token_url],
                cwd=str(cwd),
                capture_output=True,
                text=True,
                check=False,
            )
            proc3 = subprocess.run(
                ["git", "push", remote, refspec],
                cwd=str(cwd),
                capture_output=True,
                text=True,
                check=False,
            )
            if proc3.returncode != 0 and ("non-fast-forward" in (proc3.stderr or "").lower() or "rejected" in (proc3.stderr or "").lower()):
                proc3 = subprocess.run(
                    ["git", "push", "--force-with-lease", remote, refspec],
                    cwd=str(cwd),
                    capture_output=True,
                    text=True,
                    check=False,
                )
            if proc3.returncode == 0:
                return True, "pushed with token auth"
            return False, f"push failed after token auth: {(proc3.stderr or '').strip()}"
        finally:
            if original_url:
                subprocess.run(
                    ["git", "remote", "set-url", remote, original_url],
                    cwd=str(cwd),
                    capture_output=True,
                    text=True,
                    check=False,
                )

    return False, f"push failed: {stderr.strip()}"


def _commit_and_push_if_changed(
    worktree: Path,
    pr_owner: str,
    pr_repo: str,
    pr_number: int,
    *,
    commit_message: str,
    quiet: bool,
) -> Tuple[bool, str]:
    """Stage, commit, and push using the bot identity. Returns (pushed, message)."""
    status = _run_git(["status", "--porcelain"], worktree)
    if status.returncode != 0:
        return False, f"git status failed: {status.stderr.strip()}"

    if not status.stdout.strip():
        # Nothing to commit; treat as success "no-op".
        # We still need to ensure the remote is up to date with HEAD; nothing to push.
        return True, "no changes to commit"

    add = _run_git(["add", "-A"], worktree)
    if add.returncode != 0:
        return False, f"git add failed: {add.stderr.strip()}"

    commit_env = os.environ.copy()
    commit_env["GIT_AUTHOR_NAME"] = "PDD Bot"
    commit_env["GIT_AUTHOR_EMAIL"] = "pdd-bot@users.noreply.github.com"
    commit_env["GIT_COMMITTER_NAME"] = "PDD Bot"
    commit_env["GIT_COMMITTER_EMAIL"] = "pdd-bot@users.noreply.github.com"
    commit = subprocess.run(
        ["git", "commit", "-m", commit_message],
        cwd=str(worktree),
        capture_output=True,
        text=True,
        check=False,
        env=commit_env,
    )
    if commit.returncode != 0:
        return False, f"git commit failed: {commit.stderr.strip() or commit.stdout.strip()}"

    metadata, err = _fetch_pr_metadata(pr_owner, pr_repo, pr_number, worktree)
    if not metadata:
        return False, f"could not resolve PR head metadata: {err}"

    clone_url = metadata["clone_url"]
    head_ref = metadata["head_ref"]

    # Configure a one-off remote for this push.
    remote_name = "pdd-pr-head"
    subprocess.run(
        ["git", "remote", "remove", remote_name],
        cwd=str(worktree),
        capture_output=True,
        text=True,
        check=False,
    )
    add_remote = subprocess.run(
        ["git", "remote", "add", remote_name, clone_url],
        cwd=str(worktree),
        capture_output=True,
        text=True,
        check=False,
    )
    if add_remote.returncode != 0:
        return False, f"git remote add failed: {add_remote.stderr.strip()}"

    try:
        ok, msg = push_with_retry(
            worktree,
            remote_name,
            pr_owner,
            pr_repo,
            f"HEAD:{head_ref}",
        )
        return ok, msg
    finally:
        subprocess.run(
            ["git", "remote", "remove", remote_name],
            cwd=str(worktree),
            capture_output=True,
            text=True,
            check=False,
        )


# ---------------------------------------------------------------------------
# Static analysis candidates
# ---------------------------------------------------------------------------


def _pr_changed_python_files(worktree: Path, pr_metadata: Optional[Dict[str, Any]]) -> List[Path]:
    """Return PR-changed Python files derived from merge-base diff."""
    base_ref = ""
    if pr_metadata and isinstance(pr_metadata.get("raw"), dict):
        base = pr_metadata["raw"].get("base") or {}
        base_ref = base.get("ref", "") or ""
    if not base_ref:
        base_ref = "main"
    candidates_refs = [f"origin/{base_ref}", base_ref]
    for ref in candidates_refs:
        try:
            proc = _run_git(["merge-base", "HEAD", ref], worktree)
            if proc.returncode == 0 and proc.stdout.strip():
                merge_base = proc.stdout.strip()
                diff = _run_git(["diff", "--name-only", merge_base, "HEAD"], worktree)
                if diff.returncode == 0:
                    files = []
                    for line in diff.stdout.splitlines():
                        line = line.strip()
                        if line.endswith(".py"):
                            files.append(worktree / line)
                    return files
        except Exception:
            continue
    return []


def _package_companion_python_files(changed_files: Iterable[Path]) -> List[Path]:
    """Return same-package companion Python files for the changed set."""
    out: List[Path] = []
    seen: set[Path] = set()
    for f in changed_files:
        try:
            parent = f.parent
            if not parent.exists():
                continue
            for sibling in parent.glob("*.py"):
                if sibling.resolve() not in seen:
                    seen.add(sibling.resolve())
                    out.append(sibling)
        except Exception:
            continue
    return out


def _detect_static_candidates(
    worktree: Path,
    pr_metadata: Optional[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    """Run static-list-drift detection and return candidate dicts."""
    try:
        from .list_drift_detection import detect_static_list_drift
    except Exception:
        return []

    try:
        changed = _pr_changed_python_files(worktree, pr_metadata)
        if not changed:
            return []
        companions = _package_companion_python_files(changed)
        all_paths = list({p.resolve(): p for p in (changed + companions)}.values())
        findings = detect_static_list_drift(all_paths)
        changed_set = {p.resolve() for p in changed}
        out: List[Dict[str, Any]] = []
        for f in findings:
            try:
                static_resolved = Path(f.static_path).resolve()
                canonical_resolved = Path(f.canonical_path).resolve()
            except Exception:
                continue
            if static_resolved not in changed_set and canonical_resolved not in changed_set:
                continue
            missing = list(f.missing_items)
            out.append({
                "summary": f.summary,
                "static_location": f"{f.static_path}:{f.static_line}",
                "canonical_location": f"{f.canonical_path}:{f.canonical_line}",
                "static_size": f.static_size,
                "canonical_size": f.canonical_size,
                "missing": missing[:25],
                "missing_total": len(missing),
            })
        return out
    except Exception:
        return []


def _format_candidate_findings(candidates: List[Dict[str, Any]]) -> str:
    if not candidates:
        return ""
    lines: List[str] = ["## Static-Analysis Candidate Findings", ""]
    lines.append(
        "These are unverified candidates produced by a static AST scan. "
        "Treat them as findings to verify against the actual code, not as pre-approved findings. "
        "If a candidate does not represent a real drift, reject it with a one-line rationale."
    )
    lines.append("")
    for i, cand in enumerate(candidates, 1):
        lines.append(f"{i}. {cand['summary']}")
        lines.append(f"   - Static list: {cand['static_location']} ({cand['static_size']} items)")
        lines.append(f"   - Canonical source: {cand['canonical_location']} ({cand['canonical_size']} items)")
        if cand["missing"]:
            preview = ", ".join(cand["missing"])
            extra = f" (+{cand['missing_total'] - len(cand['missing'])} more)" if cand["missing_total"] > len(cand["missing"]) else ""
            lines.append(f"   - Missing items: {preview}{extra}")
        lines.append("")
    return "\n".join(lines).strip() + "\n"


# ---------------------------------------------------------------------------
# Prompt construction
# ---------------------------------------------------------------------------


_MANUAL_REVIEW_STANDARD = """\
You are performing the automated equivalent of this manual request:
"review PR as a user workflow perspective; check if any prompt, example, or architecture update is needed; fully review the PR with the existing codebase; check for no regressions; verify it fully aligns with and resolves the issue; make sure it does not open more holes."

Manual-Review Standard (apply BEFORE reading the issue/PR/architecture context below):

1. User-workflow first: trace how a real CLI/API user experiences the changed behavior end-to-end. Verify the PR fully resolves the underlying user problem the issue describes — not just its literal proposed implementation.
2. Codebase alignment: cross-check the PR against the existing codebase. Decide whether prompts, examples, architecture entries, docs, CLI help, or tests need updates.
3. Regression and hole-opening sweep: look for regressions or newly opened holes in security, billing/cost, API, reliability, UX, compatibility, tests, and maintainability.
4. Issue intent vs. literal implementation: if the PR intentionally uses a different approach than the issue's proposed implementation, accept it when the PR/issue context justifies the change AND the new approach fully solves the underlying user problem. Still report findings when the direction change is unjustified, contradicted by user comments, leaves the underlying problem unresolved, leaves stale user-facing flags/docs/examples/acceptance language promising the old behavior, omits required documentation/tests/prompt/architecture updates, or creates new risks.
5. Provenance and source-of-truth checks: for source-of-truth, catalog, manifest, cache, leaderboard, or generated-data changes, verify provenance and authoritative sources when practical, including model/variant identity, normalization, dates, subsets, ranks, confidence fields, and whether reviewers can audit where each value came from. Check whether the PR recreates the same bug class in a different form. For model catalog and manifest-based scoring changes specifically, verify that provider roots and aliases actually produce catalog rows, default models are not assigned high/low/minimal reasoning-variant scores, and normalization does not collapse distinct Arena variants into one score.
6. Independent findings: do NOT collapse independently actionable problems into one broad finding. If the PR changes architecture, also review the alternate architecture on its own terms and report prompt/docs/contract, provenance, data-quality, or auditability fixes that would still be needed if maintainers accepted the new direction.
7. Issue-contract trace: if the issue or PR describes numbered steps, acceptance criteria, workflow phases, dry-run/non-dry-run behavior, state transitions, or failure handling, verify each item against implementation evidence and report skipped or partially implemented steps SEPARATELY.
8. State/side-effect ordering: workflows must not save hashes, checkpoints, cache entries, success markers, comments, or reports that imply completion when a required downstream step failed or was skipped. Partial failures must not make later runs short-circuit as if the input was handled.
9. Security/credential/redaction: for security, credential, token, logging, and redaction changes, trace every log, exception, warning, retry, auth-refresh, and diagnostic path. Verify secret scrubbing happens BEFORE truncation/slicing/formatting/previewing so partial token fragments cannot leak. Sweep for exception/diagnostic patterns such as `str(e)`, `repr(e)`, `stderr`, `stdout`, `logger.warning`, `logger.exception`, `RuntimeError`, slicing (`[:...`), and truncate/preview helpers.
10. Prompt-driven sync: for prompt-driven modules, verify prompt/example/architecture/docs/generated-metadata synchronization, including architecture entries, prompt contracts, `.pdd/meta` hashes/run records, examples, and tests when they exist.
11. Caller-compatibility sweep: for changed public functions, CLI flags, imports, and generated module interfaces, verify all callers still pass valid arguments and import existing symbols (e.g. `rg "function_name\\("`, `rg "import_name"`).
12. Targeted read-only-safe repros when practical: compile touched Python files, import changed modules, inspect CLI help, or execute minimal workflows in a temporary directory. If a repro cannot run, still trace the concrete code path a user would hit.
13. EXCLUDE external GitHub/CI readiness from findings: ignore pending/action-required GitHub status checks, Cloud Build status, auto-heal status, mergeability, synthetic merge status, and required-check readiness UNLESS that state is direct evidence of a concrete code or repository-file regression introduced by the PR.

Highest-priority severities for this loop: {blocking_severities}. These are the severities that determine whether the loop continues; report ALL valid in-scope findings regardless of severity.

Output contract: respond with a JSON code block of the form:
```json
{{
  "status": "clean" | "findings",
  "findings": [
    {{
      "severity": "blocker|critical|medium|low|info",
      "area": "...",
      "evidence": "...",
      "finding": "...",
      "required_fix": "...",
      "location": "path/to/file.py:line"
    }}
  ]
}}
```
If there are no actionable findings, return `{{"status": "clean", "findings": []}}` and on a separate line write `Findings: none`.
"""


_VERIFY_NOTE = """\
This pass is the verification AND the next full PR review. It is NOT a narrow checkbox verification.
1. First verify every previous finding and the fixer's per-finding response.
2. Then perform a fresh full PR review again using the same Manual-Review Standard above.
3. Look for newly visible issues, missed issues, regressions introduced by the fix, and prompt/example/architecture/docs/test drift.
The loop repeats until you report no actionable findings (status=clean) or `max_rounds` is reached.

Disagreement protocol: for each previous finding, the fixer returned one of `fixed`, `not_valid`, `partially_fixed`, or `blocked` with a rationale.
- If you accept the fixer's rationale, OMIT that finding from your `findings` list (it will be marked fixed/resolved).
- If you reject the rationale, RE-REPORT the finding with concrete evidence and a reason the fixer should act on it.
"""


def _format_pr_context(context: ReviewLoopContext) -> str:
    parts: List[str] = []
    parts.append(f"PR URL: {context.pr_url}")
    parts.append(f"PR title: {context.pr_title}")
    parts.append(f"PR head ref: {context.pr_head_ref}")
    parts.append(f"PR base ref: {context.pr_base_ref}")
    if context.pr_body:
        parts.append("PR body:\n" + context.pr_body)
    if context.pr_changed_files:
        parts.append("Changed files:\n" + "\n".join(f"- {f}" for f in context.pr_changed_files))
    if context.pr_comments:
        parts.append("PR conversation comments:")
        for c in context.pr_comments[:50]:
            user = (c.get("user") or {}).get("login", "?") if isinstance(c.get("user"), dict) else c.get("user", "?")
            body = c.get("body", "")
            parts.append(f"- @{user}: {body}")
    if context.pr_reviews:
        parts.append("Submitted PR reviews:")
        for r in context.pr_reviews[:50]:
            user = (r.get("user") or {}).get("login", "?") if isinstance(r.get("user"), dict) else r.get("user", "?")
            state = r.get("state", "")
            body = r.get("body", "")
            parts.append(f"- @{user} [{state}]: {body}")
    return "\n\n".join(parts)


def _format_issue_context(context: ReviewLoopContext) -> str:
    parts: List[str] = [
        f"Issue URL: {context.issue_url}",
        f"Issue title: {context.issue_title}",
    ]
    if context.issue_body:
        parts.append("Issue body:\n" + context.issue_body)
    return "\n\n".join(parts)


def _build_reviewer_prompt(
    *,
    mode: str,
    reviewer: str,
    context: ReviewLoopContext,
    config: ReviewLoopConfig,
    candidate_findings: List[Dict[str, Any]],
    open_findings: Optional[List[ReviewFinding]] = None,
    fix_result: Optional[FixResult] = None,
    round_number: int,
) -> str:
    parts: List[str] = []
    blocking_str = ", ".join(config.blocking_severities) or "(none)"
    parts.append(_MANUAL_REVIEW_STANDARD.format(blocking_severities=blocking_str))

    if mode == "verify":
        parts.append(_VERIFY_NOTE)

    candidate_section = _format_candidate_findings(candidate_findings)
    if candidate_section:
        parts.append(candidate_section)

    if mode == "verify" and open_findings:
        parts.append("## Previously Reported Findings\n")
        for f in open_findings:
            disp = ""
            rationale = ""
            if fix_result is not None:
                key = f.dedup_key()
                disp = fix_result.dispositions.get(key, "")
                rationale = fix_result.rationales.get(key, "")
            parts.append(
                f"- [{f.severity}] ({f.location or 'no-location'}) {f.finding}\n"
                f"  required_fix: {f.required_fix}\n"
                f"  fixer_disposition: {disp or 'unknown'}\n"
                f"  fixer_rationale: {rationale}"
            )

    parts.append("## Issue Context\n" + _format_issue_context(context))
    parts.append("## PR Context\n" + _format_pr_context(context))
    if context.architecture_json:
        parts.append("## Architecture\n```json\n" + context.architecture_json + "\n```")

    parts.append(f"You are role: {reviewer}. Round: {round_number}. Mode: {mode}.")
    return "\n\n".join(parts)


def _build_fixer_prompt(
    *,
    fixer: str,
    findings: List[ReviewFinding],
    context: ReviewLoopContext,
    config: ReviewLoopConfig,
    round_number: int,
) -> str:
    blocking_str = ", ".join(config.blocking_severities) or "(none)"
    parts: List[str] = []
    parts.append(
        f"You are role: {fixer}. You are the FIXER for round {round_number} of the PDD checkup review loop.\n"
        f"Highest-priority severities: {blocking_str}. These determine whether the loop continues; "
        "address every valid in-scope finding when practical, prioritizing those severities.\n"
        "'Focused fixes' means avoiding unrelated refactors and broad churn — NOT leaving real issues unfixed.\n"
        "If you leave any valid finding unfixed, return `partially_fixed` or `blocked` with a concrete rationale."
    )
    parts.append("## Findings to address")
    for f in findings:
        parts.append(
            f"- key: {f.dedup_key()}\n"
            f"  severity: {f.severity}\n"
            f"  location: {f.location}\n"
            f"  finding: {f.finding}\n"
            f"  required_fix: {f.required_fix}\n"
            f"  evidence: {f.evidence}"
        )

    parts.append(
        "## Output contract\n"
        "After applying fixes, respond with a single JSON code block:\n"
        "```json\n"
        "{\n"
        '  "summary": "what you changed and why",\n'
        '  "changed_files": ["path/to/file.py", ...],\n'
        '  "dispositions": {"<finding_key>": "fixed|not_valid|partially_fixed|blocked", ...},\n'
        '  "rationales": {"<finding_key>": "short rationale", ...}\n'
        "}\n"
        "```\n"
        "Use the exact `key` strings shown above. Legacy `not_a_bug` will be normalized to `not_valid`."
    )
    parts.append("## Issue/PR Context\n" + _format_issue_context(context) + "\n\n" + _format_pr_context(context))
    return "\n\n".join(parts)


# ---------------------------------------------------------------------------
# Fixer output parsing
# ---------------------------------------------------------------------------


def _parse_fixer_output(raw_output: str) -> Tuple[str, List[str], Dict[str, str], Dict[str, str]]:
    summary = ""
    changed_files: List[str] = []
    dispositions: Dict[str, str] = {}
    rationales: Dict[str, str] = {}

    json_text = _extract_json_block(raw_output)
    if json_text:
        try:
            payload = json.loads(json_text)
            if isinstance(payload, dict):
                summary = str(payload.get("summary", "")).strip()
                cf = payload.get("changed_files")
                if isinstance(cf, list):
                    changed_files = [str(p) for p in cf if isinstance(p, str)]
                disp = payload.get("dispositions")
                if isinstance(disp, dict):
                    for k, v in disp.items():
                        if isinstance(k, str) and isinstance(v, str):
                            dv = v.strip().lower()
                            if dv == "not_a_bug":
                                dv = "not_valid"
                            dispositions[k] = dv
                rats = payload.get("rationales")
                if isinstance(rats, dict):
                    for k, v in rats.items():
                        if isinstance(k, str) and isinstance(v, str):
                            rationales[k] = v.strip()
        except Exception:
            pass

    if not summary:
        # Fall back: use first non-empty line.
        for line in raw_output.splitlines():
            if line.strip():
                summary = line.strip()
                break
    return summary, changed_files, dispositions, rationales


# ---------------------------------------------------------------------------
# Provider context manager + agentic invocation
# ---------------------------------------------------------------------------


@contextmanager
def _provider_for_role(role: str) -> Iterator[None]:
    """Set PDD_AGENTIC_PROVIDER for the role and always restore."""
    provider = ROLE_TO_PROVIDER.get(role)
    if not provider:
        yield
        return
    prior = os.environ.get("PDD_AGENTIC_PROVIDER")
    os.environ["PDD_AGENTIC_PROVIDER"] = provider
    try:
        yield
    finally:
        if prior is None:
            os.environ.pop("PDD_AGENTIC_PROVIDER", None)
        else:
            os.environ["PDD_AGENTIC_PROVIDER"] = prior


def _invoke_agentic(
    *,
    prompt: str,
    role: str,
    cwd: Path,
    label: str,
    verbose: bool,
    quiet: bool,
) -> Tuple[bool, str, float, str]:
    """Run an agentic task with the role's provider preference."""
    try:
        from .agentic_common import run_agentic_task
    except Exception as exc:
        return False, f"failed to import run_agentic_task: {exc}", 0.0, role

    with _provider_for_role(role):
        try:
            success, output, cost, provider = run_agentic_task(
                prompt,
                cwd,
                verbose=verbose,
                quiet=quiet,
                label=label,
                max_retries=1,
            )
            return success, output or "", float(cost or 0.0), str(provider or role)
        except TypeError:
            try:
                success, output, cost, provider = run_agentic_task(prompt, cwd)
                return success, output or "", float(cost or 0.0), str(provider or role)
            except Exception as exc:
                return False, f"agentic invocation error: {exc}", 0.0, role
        except Exception as exc:
            return False, f"agentic invocation error: {exc}", 0.0, role


# ---------------------------------------------------------------------------
# Artifact persistence
# ---------------------------------------------------------------------------


def _artifact_dir(cwd: Path, issue_number: int, pr_number: int) -> Path:
    git_root = _get_git_root(cwd)
    return git_root / ".pdd" / "checkup-review-loop" / f"issue-{issue_number}-pr-{pr_number}"


def _write_artifact(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _persist_review_step(
    artifact_dir: Path,
    *,
    round_number: int,
    mode: str,
    role: str,
    prompt: str,
    output: str,
    findings: List[ReviewFinding],
    candidates: Optional[List[Dict[str, Any]]] = None,
) -> None:
    base = artifact_dir / f"round-{round_number}-{mode}-{role}"
    _write_artifact(base.with_suffix(".prompt.txt"), prompt)
    _write_artifact(base.with_suffix(".output.txt"), output)
    _write_artifact(
        base.with_suffix(".findings.json"),
        json.dumps([f.to_dict() for f in findings], indent=2),
    )
    if candidates is not None:
        cand_path = artifact_dir / f"round-{round_number}-{mode}-static-analysis-candidates.json"
        _write_artifact(cand_path, json.dumps(candidates, indent=2))


def _persist_fix_step(
    artifact_dir: Path,
    *,
    round_number: int,
    role: str,
    prompt: str,
    output: str,
    fix_result: FixResult,
) -> None:
    base = artifact_dir / f"round-{round_number}-fix-{role}"
    _write_artifact(base.with_suffix(".prompt.txt"), prompt)
    _write_artifact(base.with_suffix(".output.txt"), output)
    payload = {
        "summary": fix_result.summary,
        "changed_files": fix_result.changed_files,
        "dispositions": fix_result.dispositions,
        "rationales": fix_result.rationales,
    }
    _write_artifact(base.with_suffix(".findings.json"), json.dumps(payload, indent=2))


def _persist_dedup_state(
    artifact_dir: Path,
    round_number: int,
    state: ReviewLoopState,
) -> None:
    payload = {
        key: f.to_dict() for key, f in state.findings_by_key.items()
    }
    _write_artifact(
        artifact_dir / f"dedup-state-round-{round_number}.json",
        json.dumps(payload, indent=2),
    )


# ---------------------------------------------------------------------------
# Final report rendering
# ---------------------------------------------------------------------------


def _escape_table_cell(value: str) -> str:
    if value is None:
        return ""
    return value.replace("|", "\\|").replace("\n", " ").replace("\r", " ")


def _render_final_report(
    *,
    context: ReviewLoopContext,
    config: ReviewLoopConfig,
    state: ReviewLoopState,
) -> str:
    issue_aligned = "true" if (
        state.fresh_final_status == "clean"
        and state.active_reviewer
        and state.reviewer_status.get(state.active_reviewer) == "clean"
    ) else "false"

    # reviewer-status header line
    status_parts: List[str] = []
    rs = state.reviewer_status
    primary = state.primary_reviewer
    fixer_role = state.fixer_role
    fallback = state.fallback_role

    if primary and primary in rs:
        status_parts.append(f"{primary}={rs[primary]}")
    if fixer_role:
        status_parts.append(f"{fixer_role}=fixer")
    if fallback and fallback in rs and fallback != primary:
        status_parts.append(f"{fallback}={rs[fallback]}")
    status_parts.append(f"fresh-final={state.fresh_final_status}")

    lines: List[str] = []
    lines.append("## Step 7/8: Review Loop Final Report")
    lines.append("")
    lines.append(f"PR: {context.pr_url}")
    lines.append(f"Issue: {context.issue_url}")
    lines.append(f"issue_aligned: {issue_aligned}")
    lines.append(f"active-reviewer: {state.active_reviewer or '(none)'}")
    lines.append(f"reviewer-status: {' '.join(status_parts)}")
    lines.append(f"fresh-final-review: {state.fresh_final_status}")
    lines.append(f"max-rounds-reached: {'true' if state.max_rounds_reached else 'false'}")
    lines.append(f"max-cost-reached: {'true' if state.max_cost_reached else 'false'}")
    lines.append(f"max-duration-reached: {'true' if state.max_duration_reached else 'false'}")
    lines.append("")

    # Summary
    lines.append("### Summary")
    lines.append("")
    summary_parts: List[str] = []
    if state.stop_reason:
        summary_parts.append(state.stop_reason)
    summary_parts.append(f"Total cost: ${state.total_cost:.4f}")
    summary_parts.append(f"Rounds executed: {len(state.review_results)} review/verify steps, {len(state.fix_results)} fix steps")
    lines.append(" ".join(summary_parts))
    lines.append("")

    # Per-Reviewer Status table
    lines.append("### Per-Reviewer Status")
    lines.append("")
    lines.append("| Role | Function | Status |")
    lines.append("| --- | --- | --- |")
    primary_superseded = (
        state.fallback_used
        and primary
        and state.active_reviewer
        and state.active_reviewer != primary
    )
    if primary:
        function_label = "primary reviewer"
        status_token = rs.get(primary, "missing")
        if primary_superseded:
            status_token = f"{status_token} (optional, superseded by {state.active_reviewer})"
        lines.append(
            f"| {_escape_table_cell(primary)} | {_escape_table_cell(function_label)} | {_escape_table_cell(status_token)} |"
        )
    if fallback and fallback != primary:
        lines.append(
            f"| {_escape_table_cell(fallback)} | {_escape_table_cell('fallback reviewer')} | {_escape_table_cell(rs.get(fallback, 'missing'))} |"
        )
    if fixer_role:
        lines.append(
            f"| {_escape_table_cell(fixer_role)} | {_escape_table_cell('fixer')} | {_escape_table_cell('fixer')} |"
        )
    lines.append(
        f"| fresh-final | {_escape_table_cell('aggregate')} | {_escape_table_cell(state.fresh_final_status)} |"
    )
    lines.append("")

    # Findings table (open/unfixed only)
    lines.append("### Findings")
    lines.append("")
    lines.append("| Severity | Status | Location | Finding | Required fix | Reviewer |")
    lines.append("| --- | --- | --- | --- | --- | --- |")
    open_findings = [f for f in state.findings_by_key.values() if f.status != "fixed"]
    if not open_findings:
        lines.append("| - | - | - | _no remaining findings_ | - | - |")
    else:
        # Sort by severity priority then location
        sev_index = {s: i for i, s in enumerate(SEVERITY_ORDER)}
        open_findings.sort(key=lambda f: (sev_index.get(f.severity, 99), f.location))
        for f in open_findings:
            lines.append(
                "| {sev} | {st} | {loc} | {find} | {fix} | {rev} |".format(
                    sev=_escape_table_cell(f.severity),
                    st=_escape_table_cell(f.status),
                    loc=_escape_table_cell(f.location or "-"),
                    find=_escape_table_cell(f.finding),
                    fix=_escape_table_cell(f.required_fix or "-"),
                    rev=_escape_table_cell(f.reviewer),
                )
            )
    lines.append("")

    # Fixer Rationale
    lines.append("### Fixer Rationale")
    lines.append("")
    if not open_findings:
        lines.append("- none")
    else:
        for f in open_findings:
            key = f.dedup_key()
            disp = "unknown"
            rationale = ""
            for fr in reversed(state.fix_results):
                if key in fr.dispositions:
                    disp = fr.dispositions[key]
                    rationale = fr.rationales.get(key, "")
                    break
            lines.append(f"- [{f.severity}] {f.location or '-'}: disposition={disp}; rationale={rationale or '(none)'}")
    lines.append("")

    # Fixes Attempted
    lines.append("### Fixes Attempted")
    lines.append("")
    if not state.fix_results:
        lines.append("- none")
    else:
        for fr in state.fix_results:
            verification = "verified" if fr.verified else "unverified"
            files = ", ".join(fr.changed_files) if fr.changed_files else "(no file list)"
            lines.append(
                f"- round={fr.round_number} fixer={fr.fixer} pushed={fr.pushed} verification={verification} files={files} summary={fr.summary[:200]}"
            )
    lines.append("")

    return "\n".join(lines).rstrip() + "\n"


# ---------------------------------------------------------------------------
# GitHub posting
# ---------------------------------------------------------------------------


def _post_final_report_to_github(
    context: ReviewLoopContext,
    cwd: Path,
    report: str,
    quiet: bool,
) -> None:
    if not shutil.which("gh"):
        if not quiet:
            console.print("[yellow]gh CLI not found; skipping final-report posting[/yellow]")
        return
    # Issue comment
    try:
        subprocess.run(
            [
                "gh",
                "api",
                "-X",
                "POST",
                f"repos/{context.issue_owner}/{context.issue_repo}/issues/{context.issue_number}/comments",
                "-f",
                f"body={report}",
            ],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            check=False,
        )
    except Exception as exc:
        if not quiet:
            console.print(f"[yellow]Failed to post issue comment: {exc}[/yellow]")
    # PR comment
    try:
        subprocess.run(
            [
                "gh",
                "pr",
                "comment",
                str(context.pr_number),
                "--repo",
                f"{context.pr_owner}/{context.pr_repo}",
                "--body",
                report,
            ],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            check=False,
        )
    except Exception as exc:
        if not quiet:
            console.print(f"[yellow]Failed to post PR comment: {exc}[/yellow]")


# ---------------------------------------------------------------------------
# Reviewer step (with parse-repair)
# ---------------------------------------------------------------------------


def _run_review(
    *,
    mode: str,
    reviewer: str,
    context: ReviewLoopContext,
    config: ReviewLoopConfig,
    worktree: Path,
    artifact_dir: Path,
    pr_metadata: Optional[Dict[str, Any]],
    open_findings: Optional[List[ReviewFinding]],
    fix_result: Optional[FixResult],
    round_number: int,
    verbose: bool,
    quiet: bool,
) -> Tuple[ReviewResult, str]:
    """Run a single reviewer/verifier invocation. Returns (result, prompt)."""
    candidates = _detect_static_candidates(worktree, pr_metadata)

    prompt = _build_reviewer_prompt(
        mode=mode,
        reviewer=reviewer,
        context=context,
        config=config,
        candidate_findings=candidates,
        open_findings=open_findings,
        fix_result=fix_result,
        round_number=round_number,
    )
    label = f"checkup-review-r{round_number}-{mode}-{reviewer}"
    success, output, cost, model = _invoke_agentic(
        prompt=prompt,
        role=reviewer,
        cwd=worktree,
        label=label,
        verbose=verbose,
        quiet=quiet,
    )

    status, findings = _normalize_findings(
        output,
        reviewer=reviewer,
        round_number=round_number,
        success=success,
        continue_on_limit=config.continue_on_reviewer_limit,
    )

    # Bounded same-role parse-repair when call succeeded but output unparsable.
    if success and status == "unparsable":
        repair_prompt = (
            "The following text was your prior reviewer output. Convert it to the strict JSON contract:\n"
            "```json\n{\"status\": \"clean|findings|failed\", \"findings\": [...]}\n```\n"
            "Do NOT perform a new review. Do NOT add findings that were not in the original text. "
            "Only translate the original assessment.\n\n"
            "Original output:\n"
            f"{output}"
        )
        repair_label = label + "-repair"
        r_success, r_output, r_cost, r_model = _invoke_agentic(
            prompt=repair_prompt,
            role=reviewer,
            cwd=worktree,
            label=repair_label,
            verbose=verbose,
            quiet=quiet,
        )
        cost += r_cost
        if r_success:
            r_status, r_findings = _normalize_findings(
                r_output,
                reviewer=reviewer,
                round_number=round_number,
                success=True,
                continue_on_limit=config.continue_on_reviewer_limit,
            )
            if r_status in ("clean", "findings", "failed"):
                status = r_status
                findings = r_findings

    if status == "unparsable":
        # Preserve original failed/unparsable status as failed.
        status = "failed"

    candidates_to_persist = candidates if candidates else []
    _persist_review_step(
        artifact_dir,
        round_number=round_number,
        mode=mode,
        role=reviewer,
        prompt=prompt,
        output=output,
        findings=findings,
        candidates=candidates_to_persist if candidates_to_persist else None,
    )

    return (
        ReviewResult(
            reviewer=reviewer,
            mode=mode,
            status=status,
            findings=findings,
            raw_output=output,
            cost=cost,
            model=model,
            round_number=round_number,
        ),
        prompt,
    )


# ---------------------------------------------------------------------------
# Fixer step
# ---------------------------------------------------------------------------


def _run_fix(
    *,
    fixer: str,
    findings: List[ReviewFinding],
    context: ReviewLoopContext,
    config: ReviewLoopConfig,
    worktree: Path,
    artifact_dir: Path,
    round_number: int,
    verbose: bool,
    quiet: bool,
) -> FixResult:
    prompt = _build_fixer_prompt(
        fixer=fixer,
        findings=findings,
        context=context,
        config=config,
        round_number=round_number,
    )
    label = f"checkup-fix-r{round_number}-{fixer}"
    success, output, cost, model = _invoke_agentic(
        prompt=prompt,
        role=fixer,
        cwd=worktree,
        label=label,
        verbose=verbose,
        quiet=quiet,
    )
    summary, changed_files, dispositions, rationales = _parse_fixer_output(output)
    fix_result = FixResult(
        fixer=fixer,
        summary=summary or ("(fixer call failed)" if not success else "(no summary)"),
        changed_files=changed_files,
        dispositions=dispositions,
        rationales=rationales,
        cost=cost,
        model=model,
        round_number=round_number,
    )
    _persist_fix_step(
        artifact_dir,
        round_number=round_number,
        role=fixer,
        prompt=prompt,
        output=output,
        fix_result=fix_result,
    )
    return fix_result


# ---------------------------------------------------------------------------
# Main loop entry point
# ---------------------------------------------------------------------------


def _required_findings(
    findings: Iterable[ReviewFinding], blocking_severities: Tuple[str, ...]
) -> List[ReviewFinding]:
    block = {s.lower() for s in blocking_severities}
    return [f for f in findings if f.severity.lower() in block]


def _resolve_clean_states(states: Sequence[str]) -> Tuple[str, ...]:
    out: List[str] = []
    for s in states:
        sl = s.strip().lower()
        if sl in HARD_NOT_CLEAN_STATES:
            continue
        if sl and sl not in out:
            out.append(sl)
    if not out:
        out = ["clean"]
    return tuple(out)


def _resolve_roles(config: ReviewLoopConfig) -> Tuple[Optional[str], Optional[str], Optional[str]]:
    """Return (reviewer, fixer, fallback)."""
    reviewer = _normalize_role(config.reviewer)
    fixer = _normalize_role(config.fixer)

    if not reviewer or not fixer:
        # Use shorthand `reviewers` list.
        norm = parse_reviewers(config.reviewers)
        if not reviewer and len(norm) >= 1:
            reviewer = norm[0]
        if not fixer and len(norm) >= 2:
            fixer = norm[1]
    if not reviewer:
        reviewer = DEFAULT_REVIEWER
    if not fixer:
        fixer = DEFAULT_FIXER

    fallback = _normalize_role(config.reviewer_fallback)
    if fallback and (fallback == reviewer or fallback == fixer):
        fallback = None
    return reviewer, fixer, fallback


def _update_findings_from_review(
    state: ReviewLoopState,
    review: ReviewResult,
    *,
    previous_open_keys: Optional[set[str]] = None,
) -> List[ReviewFinding]:
    """Merge review findings into state. Returns list of currently open findings."""
    re_reported_keys: set[str] = set()
    for f in review.findings:
        key = f.dedup_key()
        re_reported_keys.add(key)
        if key in state.findings_by_key:
            existing = state.findings_by_key[key]
            existing.status = "open"
            existing.round_number = f.round_number
            existing.evidence = existing.evidence or f.evidence
            existing.required_fix = existing.required_fix or f.required_fix
        else:
            state.findings_by_key[key] = f

    # If verifier omitted previously-open findings, mark them fixed.
    if previous_open_keys is not None and review.mode == "verify":
        for key in previous_open_keys:
            if key not in re_reported_keys and key in state.findings_by_key:
                state.findings_by_key[key].status = "fixed"

    return [f for f in state.findings_by_key.values() if f.status != "fixed"]


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

    Returns ``(success, report_str, total_cost, last_model)``. ``success`` is ``True``
    whenever a final report could be produced — even if the reviewer status is non-clean.
    """
    state = ReviewLoopState()
    state.fresh_final_status = "missing"

    # Validate config gates.
    blocking = tuple(s.strip().lower() for s in config.blocking_severities if s and s.strip())
    if not blocking:
        blocking = DEFAULT_BLOCKING_SEVERITIES
    config.blocking_severities = blocking
    config.clean_reviewer_states = _resolve_clean_states(config.clean_reviewer_states)

    # Resolve roles.
    reviewer, fixer, fallback = _resolve_roles(config)
    state.primary_reviewer = reviewer or ""
    state.fixer_role = fixer or ""
    state.fallback_role = fallback
    state.active_reviewer = reviewer or ""

    artifact_dir = _artifact_dir(cwd, context.issue_number, context.pr_number)
    artifact_dir.mkdir(parents=True, exist_ok=True)

    # Distinct-role check (skip in review_only mode).
    if not config.review_only and reviewer and fixer and reviewer == fixer:
        state.reviewer_status[reviewer] = "failed"
        state.stop_reason = (
            f"reviewer and fixer must be different roles (both resolved to '{reviewer}')"
        )
        state.fresh_final_status = "missing"
        report = _render_final_report(context=context, config=config, state=state)
        _write_artifact(artifact_dir / "final-report.md", report)
        _write_artifact(artifact_dir / "final-state.json", _final_state_json(state))
        return True, report, state.total_cost, state.last_model

    # Fetch PR metadata once for use by static-analysis and pushes.
    pr_metadata, meta_err = _fetch_pr_metadata(
        context.pr_owner, context.pr_repo, context.pr_number, cwd
    )
    if meta_err and not quiet:
        console.print(f"[yellow]Could not fetch PR metadata up front: {meta_err}[/yellow]")

    # Worktree setup (always, exactly once).
    worktree, wt_err = _setup_pr_worktree(
        cwd, context.pr_owner, context.pr_repo, context.pr_number, quiet
    )
    if not worktree:
        state.reviewer_status[reviewer or DEFAULT_REVIEWER] = "missing"
        state.stop_reason = f"failed to create PR worktree: {wt_err}"
        report = _render_final_report(context=context, config=config, state=state)
        _write_artifact(artifact_dir / "final-report.md", report)
        _write_artifact(artifact_dir / "final-state.json", _final_state_json(state))
        return True, report, state.total_cost, state.last_model

    start_time = time.monotonic()

    def _budget_exceeded() -> Optional[str]:
        elapsed_min = (time.monotonic() - start_time) / 60.0
        if elapsed_min >= config.max_minutes:
            state.max_duration_reached = True
            return f"max duration reached ({elapsed_min:.1f} min)"
        if state.total_cost >= config.max_cost:
            state.max_cost_reached = True
            return f"max cost reached (${state.total_cost:.2f})"
        return None

    # ---- Review-only mode ----
    if config.review_only:
        review, _ = _run_review(
            mode="review",
            reviewer=reviewer or DEFAULT_REVIEWER,
            context=context,
            config=config,
            worktree=worktree,
            artifact_dir=artifact_dir,
            pr_metadata=pr_metadata,
            open_findings=None,
            fix_result=None,
            round_number=1,
            verbose=verbose,
            quiet=quiet,
        )
        state.review_results.append(review)
        state.total_cost += review.cost
        state.last_model = review.model or state.last_model
        state.reviewer_status[reviewer or DEFAULT_REVIEWER] = review.status
        _update_findings_from_review(state, review)
        _persist_dedup_state(artifact_dir, 1, state)

        if review.status == "clean":
            state.fresh_final_status = "clean"
            state.stop_reason = "review-only mode: reviewer reported no actionable findings"
        elif review.status == "findings":
            state.fresh_final_status = "missing"
            state.stop_reason = "review-only mode: reviewer reported findings"
        else:
            state.fresh_final_status = "missing"
            state.stop_reason = f"review-only mode: reviewer status={review.status}"

        report = _render_final_report(context=context, config=config, state=state)
        _write_artifact(artifact_dir / "final-report.md", report)
        _write_artifact(artifact_dir / "final-state.json", _final_state_json(state))
        if use_github_state:
            _post_final_report_to_github(context, cwd, report, quiet)
        return True, report, state.total_cost, state.last_model

    # ---- Full review loop ----
    pending_review: Optional[ReviewResult] = None  # Carry verifier-as-next-reviewer.
    round_number = 0
    fix_result: Optional[FixResult] = None

    while round_number < config.max_rounds:
        round_number += 1
        # (1) REVIEW step — unless we already have pending findings from previous verify.
        if pending_review is None:
            mode = "review"
            review, _ = _run_review(
                mode=mode,
                reviewer=state.active_reviewer,
                context=context,
                config=config,
                worktree=worktree,
                artifact_dir=artifact_dir,
                pr_metadata=pr_metadata,
                open_findings=None,
                fix_result=None,
                round_number=round_number,
                verbose=verbose,
                quiet=quiet,
            )
            state.review_results.append(review)
            state.total_cost += review.cost
            state.last_model = review.model or state.last_model
            state.reviewer_status[state.active_reviewer] = review.status

            # Fallback handling: if active reviewer in hard-not-clean and fallback available.
            if (
                review.status in HARD_NOT_CLEAN_STATES
                and fallback
                and not state.fallback_used
            ):
                if not quiet:
                    console.print(
                        f"[yellow]Primary reviewer {state.active_reviewer} status={review.status}; "
                        f"running fallback {fallback}[/yellow]"
                    )
                state.fallback_used = True
                fb_review, _ = _run_review(
                    mode=mode,
                    reviewer=fallback,
                    context=context,
                    config=config,
                    worktree=worktree,
                    artifact_dir=artifact_dir,
                    pr_metadata=pr_metadata,
                    open_findings=None,
                    fix_result=None,
                    round_number=round_number,
                    verbose=verbose,
                    quiet=quiet,
                )
                state.review_results.append(fb_review)
                state.total_cost += fb_review.cost
                state.last_model = fb_review.model or state.last_model
                state.reviewer_status[fallback] = fb_review.status
                if fb_review.status in ("clean", "findings"):
                    state.active_reviewer = fallback
                    review = fb_review
                else:
                    # Both hard not-clean: break.
                    state.stop_reason = (
                        f"primary reviewer status={state.reviewer_status.get(state.primary_reviewer)}, "
                        f"fallback reviewer status={fb_review.status}"
                    )
                    break

            previous_open_keys = {
                k for k, f in state.findings_by_key.items() if f.status != "fixed"
            }
            _update_findings_from_review(
                state, review, previous_open_keys=previous_open_keys
            )
            _persist_dedup_state(artifact_dir, round_number, state)

            if review.status == "clean":
                state.fresh_final_status = "clean"
                state.stop_reason = "reviewer reported no actionable findings"
                break

            if review.status in HARD_NOT_CLEAN_STATES:
                state.stop_reason = f"reviewer {state.active_reviewer} status={review.status}"
                state.fresh_final_status = "missing"
                break
        else:
            # Use carried pending_review as this round's "review".
            review = pending_review
            pending_review = None

        # We now have actionable findings for fixer.
        open_findings = [
            f for f in state.findings_by_key.values() if f.status != "fixed"
        ]
        if not open_findings:
            state.fresh_final_status = "clean"
            state.stop_reason = "no remaining open findings"
            break

        # Budget check before fix.
        budget_msg = _budget_exceeded()
        if budget_msg:
            state.stop_reason = budget_msg
            state.fresh_final_status = "missing"
            break

        # (2) FIX step.
        fix_result = _run_fix(
            fixer=fixer or DEFAULT_FIXER,
            findings=open_findings,
            context=context,
            config=config,
            worktree=worktree,
            artifact_dir=artifact_dir,
            round_number=round_number,
            verbose=verbose,
            quiet=quiet,
        )
        state.fix_results.append(fix_result)
        state.total_cost += fix_result.cost
        state.last_model = fix_result.model or state.last_model
        for key, disp in fix_result.dispositions.items():
            state.fix_attempts_by_key[key] = state.fix_attempts_by_key.get(key, 0) + 1
            if key in fix_result.rationales:
                state.dispute_notes_by_key[key] = fix_result.rationales[key]

        # (3) Commit + push.
        commit_msg = (
            f"pdd checkup: round {round_number} fixes from {fix_result.fixer}\n\n"
            f"{fix_result.summary}"
        )
        pushed, push_msg = _commit_and_push_if_changed(
            worktree,
            context.pr_owner,
            context.pr_repo,
            context.pr_number,
            commit_message=commit_msg,
            quiet=quiet,
        )
        fix_result.pushed = pushed
        fix_result.push_message = push_msg
        if not pushed:
            state.stop_reason = f"push failed in round {round_number}: {push_msg}"
            state.fresh_final_status = "missing"
            break

        # Budget check before verify.
        budget_msg = _budget_exceeded()
        if budget_msg:
            state.stop_reason = budget_msg
            state.fresh_final_status = "missing"
            break

        # (4) VERIFY step (also serves as next round's review).
        previous_open_keys = {
            k for k, f in state.findings_by_key.items() if f.status != "fixed"
        }
        verify, _ = _run_review(
            mode="verify",
            reviewer=state.active_reviewer,
            context=context,
            config=config,
            worktree=worktree,
            artifact_dir=artifact_dir,
            pr_metadata=pr_metadata,
            open_findings=open_findings,
            fix_result=fix_result,
            round_number=round_number,
            verbose=verbose,
            quiet=quiet,
        )
        state.review_results.append(verify)
        state.total_cost += verify.cost
        state.last_model = verify.model or state.last_model
        state.reviewer_status[state.active_reviewer] = verify.status

        # Fallback also possible at verify step (only if not yet used).
        if (
            verify.status in HARD_NOT_CLEAN_STATES
            and fallback
            and not state.fallback_used
        ):
            if not quiet:
                console.print(
                    f"[yellow]Verifier {state.active_reviewer} status={verify.status}; "
                    f"running fallback {fallback}[/yellow]"
                )
            state.fallback_used = True
            fb_verify, _ = _run_review(
                mode="verify",
                reviewer=fallback,
                context=context,
                config=config,
                worktree=worktree,
                artifact_dir=artifact_dir,
                pr_metadata=pr_metadata,
                open_findings=open_findings,
                fix_result=fix_result,
                round_number=round_number,
                verbose=verbose,
                quiet=quiet,
            )
            state.review_results.append(fb_verify)
            state.total_cost += fb_verify.cost
            state.last_model = fb_verify.model or state.last_model
            state.reviewer_status[fallback] = fb_verify.status
            if fb_verify.status in ("clean", "findings"):
                state.active_reviewer = fallback
                verify = fb_verify
            else:
                state.stop_reason = (
                    f"primary verifier status={state.reviewer_status.get(state.primary_reviewer)}, "
                    f"fallback verifier status={fb_verify.status}"
                )
                break

        _update_findings_from_review(
            state, verify, previous_open_keys=previous_open_keys
        )
        _persist_dedup_state(artifact_dir, round_number, state)

        # Mark fixer verified iff verifier clean and no remaining findings.
        remaining_after = [f for f in state.findings_by_key.values() if f.status != "fixed"]
        fix_result.verified = (
            verify.status == "clean"
            and not remaining_after
            and state.reviewer_status.get(state.active_reviewer) == "clean"
        )

        if verify.status == "clean":
            state.fresh_final_status = "clean"
            state.stop_reason = "verifier reported no actionable findings"
            break

        if verify.status in HARD_NOT_CLEAN_STATES:
            state.stop_reason = f"verifier {state.active_reviewer} status={verify.status}"
            state.fresh_final_status = "missing"
            break

        # Carry verifier findings as next round's review input.
        pending_review = verify

        # Budget check at end of round.
        budget_msg = _budget_exceeded()
        if budget_msg:
            state.stop_reason = budget_msg
            state.fresh_final_status = "missing"
            break

    else:
        # Loop fell through without break: max rounds reached.
        state.max_rounds_reached = True
        if not state.stop_reason:
            state.stop_reason = f"max rounds reached ({config.max_rounds})"
        state.fresh_final_status = "missing"

    # If active reviewer never produced a result, leave fresh_final as missing.
    if state.fresh_final_status == "clean":
        # Sanity: ensure the active reviewer's last status is clean.
        if state.reviewer_status.get(state.active_reviewer) != "clean":
            state.fresh_final_status = state.reviewer_status.get(state.active_reviewer, "missing")

    report = _render_final_report(context=context, config=config, state=state)
    _write_artifact(artifact_dir / "final-report.md", report)
    _write_artifact(artifact_dir / "final-state.json", _final_state_json(state))

    if use_github_state:
        _post_final_report_to_github(context, cwd, report, quiet)

    return True, report, state.total_cost, state.last_model


def _final_state_json(state: ReviewLoopState) -> str:
    payload = {
        "reviewer_status": dict(state.reviewer_status),
        "active_reviewer": state.active_reviewer,
        "fresh_final_status": state.fresh_final_status,
        "stop_reason": state.stop_reason,
        "total_cost": state.total_cost,
        "last_model": state.last_model,
        "max_rounds_reached": state.max_rounds_reached,
        "max_cost_reached": state.max_cost_reached,
        "max_duration_reached": state.max_duration_reached,
        "fix_attempts_by_key": dict(state.fix_attempts_by_key),
        "dispute_notes_by_key": dict(state.dispute_notes_by_key),
        "reviewer_feedback_by_key": dict(state.reviewer_feedback_by_key),
        "findings": [f.to_dict() for f in state.findings_by_key.values()],
    }
    return json.dumps(payload, indent=2)