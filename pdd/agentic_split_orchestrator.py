from __future__ import annotations

import json
import re
import signal
import subprocess
import sys
from dataclasses import dataclass, field, asdict, fields as dc_fields
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from rich.console import Console
from rich.table import Table

from .agentic_common import (
    DEFAULT_MAX_RETRIES,
    clear_agentic_progress,
    clear_workflow_state,
    load_workflow_state,
    run_agentic_task,
    save_workflow_state,
    set_agentic_progress,
    substitute_template_variables,
)
from .agentic_common_worktree import get_git_root, setup_worktree
from .architecture_sync import sync_all_prompts_to_architecture
from .get_language import get_language
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .split_validation import get_lint_commands, get_test_command, validate_extraction

console = Console()

SUPPORTED_LANGUAGES: List[str] = ["python"]
MAX_REFINEMENT_ITERATIONS: int = 1

VALID_INTENTS = {
    "REDUCE_MONOLITH",
    "ENABLE_PARALLEL_WORK",
    "EXTRACT_REUSABLE_LAYER",
    "REDUCE_TEST_TIME",
}
INTENT_ALIAS = {
    "reduce": "REDUCE_MONOLITH",
    "parallel": "ENABLE_PARALLEL_WORK",
    "reuse": "EXTRACT_REUSABLE_LAYER",
    "tests": "REDUCE_TEST_TIME",
}

SPLIT_STEP_TIMEOUTS: Dict[str, float] = {
    "0_intent": 200.0,
    "1_survey": 900.0,
    "2_diagnose": 400.0,
    "3_investigate": 600.0,
    "4_propose_options": 900.0,
    "5_setup_worktree": 30.0,
    "6a_phase_extract": 500.0,
    "6_extract": 1000.0,
    "7a_verify_local": 900.0,
    "7b_regen_gate": 1800.0,
    "7c_arch_sync": 60.0,
    "7_assess": 300.0,
    "8_repair": 600.0,
    "9_refine_check": 300.0,
}


# ----------------------------- Dataclasses -----------------------------


@dataclass
class Diagnosis:
    recommended_action: str = ""
    leave_alone_rationale: str = ""
    reasoning: str = ""
    confidence: float = 0.0
    target_file_lines: int = 0
    type: str = ""
    rationale: str = ""

    def __post_init__(self) -> None:
        if not self.type and self.recommended_action:
            self.type = self.recommended_action
        if not self.rationale:
            self.rationale = self.reasoning or self.leave_alone_rationale or ""


@dataclass
class ModuleInvestigation:
    test_seams: List[Any] = field(default_factory=list)
    ownership: Dict[str, Any] = field(default_factory=dict)
    shared_layer_candidates: List[Any] = field(default_factory=list)
    notes: str = ""


@dataclass
class SplitPlan:
    children: List[Any] = field(default_factory=list)
    parent_changes: Dict[str, Any] = field(default_factory=dict)
    test_ownership: Dict[str, Any] = field(default_factory=dict)
    metadata: Dict[str, Any] = field(default_factory=dict)
    shared_layer_children: List[Any] = field(default_factory=list)


@dataclass
class SplitOption:
    name: str = ""
    description: str = ""
    score: Any = 0.0
    plan: Any = field(default_factory=lambda: SplitPlan())
    parent_changes: Dict[str, Any] = field(default_factory=dict)

    @property
    def numeric_score(self) -> float:
        s = self.score
        try:
            if isinstance(s, dict):
                return float(s.get("total", 0.0))
            if isinstance(s, (int, float)):
                return float(s)
            return float(str(s))
        except Exception:
            return 0.0


@dataclass
class OptionsConsidered:
    options: List[Any] = field(default_factory=list)


@dataclass
class QualitativeAssessment:
    overall_verdict: str = "unknown"
    cohesion: Dict[str, Any] = field(default_factory=dict)
    boundary_clarity: Dict[str, Any] = field(default_factory=dict)
    change_decorrelation: Dict[str, Any] = field(default_factory=dict)
    projection_vs_reality: Any = ""
    score: Any = None
    rationale: str = ""


@dataclass
class IntentDecision:
    intent: str = "REDUCE_MONOLITH"
    confidence: float = 0.0
    rationale: str = ""


@dataclass
class Phase:
    name: str = ""
    description: str = ""
    line_range: Any = None
    inputs: List[Any] = field(default_factory=list)
    outputs: List[Any] = field(default_factory=list)
    side_effects: List[Any] = field(default_factory=list)


@dataclass
class PhaseExtractionPlan:
    should_extract: bool = False
    target_symbol: str = ""
    target_file: str = ""
    phases: List[Phase] = field(default_factory=list)
    parent_shell: str = ""
    rationale: str = ""
    reason: str = ""


@dataclass
class RefineCheck:
    should_refine: bool = False
    target_child_file: str = ""
    reason: str = ""
    suggested_intent: str = ""


# ----------------------------- Helpers -----------------------------


def _normalize_intent(raw: Optional[str]) -> Optional[str]:
    if not raw:
        return None
    s = str(raw).strip()
    if not s:
        return None
    if s in VALID_INTENTS:
        return s
    low = s.lower()
    if low in INTENT_ALIAS:
        return INTENT_ALIAS[low]
    upper = s.upper()
    if upper in VALID_INTENTS:
        return upper
    return None


def _stable_split_id(target_path: str) -> int:
    """Deterministic 32-bit-folded hash of a path string, mod 100000."""
    h = 0
    for c in target_path:
        h = (h * 31 + ord(c)) & 0xFFFFFFFF
    return h % 100000


def _detect_language(target_file: str) -> str:
    """Map a target file's suffix to a language string (lowercased)."""
    try:
        suffix = Path(target_file).suffix
        if not suffix:
            return ""
        lang = get_language(suffix) or ""
        return str(lang).lower()
    except Exception:
        return ""


def _find_architecture_json(target_file: str, cwd: Path) -> Optional[Path]:
    try:
        p = (cwd / target_file).resolve().parent
    except Exception:
        p = cwd
    for _ in range(8):
        candidate = p / "architecture.json"
        if candidate.exists():
            return candidate
        if p.parent == p:
            break
        p = p.parent
    return None


def _find_arch_dirs(target_file: str, cwd: Path) -> Tuple[Optional[Path], Optional[Path]]:
    try:
        p = (cwd / target_file).resolve().parent
    except Exception:
        p = cwd
    prompts_dir: Optional[Path] = None
    arch_path: Optional[Path] = None
    cur = p
    for _ in range(8):
        if (cur / "prompts").is_dir():
            pd = cur / "prompts"
            prompts_dir = pd / "src" if (pd / "src").is_dir() else pd
        if (cur / "architecture.json").exists():
            arch_path = cur / "architecture.json"
        if prompts_dir and arch_path:
            break
        if cur.parent == cur:
            break
        cur = cur.parent
    return prompts_dir, arch_path


def _strip_md(line: str) -> str:
    s = line.strip()
    while s and s[0] in {"*", "`", "#", ">", "-"}:
        s = s[1:].strip()
    while s and s[-1] in {"*", "`"}:
        s = s[:-1].strip()
    return s


# Hard-stop markers per step. Used by _check_hard_stop.
_STEP_HARD_STOPS: Dict[str, List[str]] = {
    "1_survey": ["ARCHITECTURE_STALE"],
    "2_diagnose": ["DIAGNOSIS: LEAVE_ALONE"],
    "3_investigate": ["ARCHITECTURE_STALE", "NO_TEST_FILE"],
    "4_propose_options": ["NO_IMPROVEMENT_POSSIBLE"],
    "6_extract": ["EXTRACTION_BLOCKED"],
    "7a_verify_local": ["ARCHITECTURAL_REGRESSION"],
    "7b_regen_gate": ["REGEN_FAILED"],
    "8_repair": ["REPAIR_EXHAUSTED"],
}


def _check_hard_stop(step_name: str, output: str, force_split: bool = False) -> Optional[str]:
    """Return the marker name if a step's hard-stop marker appears at the
    start of a trimmed line in *output*, else None.

    Markdown emphasis (``*``, `` ` ``, ``#``, ``>``, ``-``) at the start of a
    line is stripped before comparison. Match is case-insensitive prefix.
    When ``force_split`` is True, the ``DIAGNOSIS: LEAVE_ALONE`` marker is
    suppressed so the orchestrator proceeds past step 2.
    """
    markers = list(_STEP_HARD_STOPS.get(step_name, []))
    if force_split:
        markers = [m for m in markers if m.upper() != "DIAGNOSIS: LEAVE_ALONE"]
    if not output or not markers:
        return None
    lows = [m.lower() for m in markers]
    for raw in output.splitlines():
        s = _strip_md(raw).lower()
        if not s:
            continue
        for i, mk in enumerate(lows):
            if s.startswith(mk):
                return markers[i]
    return None


# ---------- JSON / dataclass parsing ----------

# Map dataclasses to acceptable BEGIN/END marker names. The first alias is the
# canonical one.
_DATACLASS_MARKERS: Dict[type, List[str]] = {
    Diagnosis: ["DIAGNOSIS"],
    ModuleInvestigation: ["INVESTIGATION", "MODULE_INVESTIGATION"],
    OptionsConsidered: ["OPTIONS", "OPTIONS_CONSIDERED"],
    QualitativeAssessment: ["QUALITATIVE_ASSESSMENT", "ASSESSMENT"],
    IntentDecision: ["INTENT", "INTENT_DECISION"],
    Phase: ["PHASE"],
    PhaseExtractionPlan: ["PHASE_EXTRACTION_PLAN"],
    RefineCheck: ["REFINE_CHECK"],
    SplitOption: ["SPLIT_OPTION"],
    SplitPlan: ["SPLIT_PLAN", "PLAN"],
}


def _extract_marker_block(output: str, name: str) -> Optional[str]:
    if not output:
        return None
    pattern = re.compile(
        rf"{re.escape(name)}_BEGIN\s*(.*?)\s*{re.escape(name)}_END",
        re.DOTALL | re.IGNORECASE,
    )
    m = pattern.search(output)
    if not m:
        return None
    return m.group(1).strip()


def _strip_code_fence(text: str) -> str:
    s = text.strip()
    if s.startswith("```"):
        s = re.sub(r"^```[a-zA-Z0-9_]*\n?", "", s)
        s = re.sub(r"```\s*$", "", s)
    return s.strip()


def _try_parse_json(s: str) -> Optional[Any]:
    s = _strip_code_fence(s)
    if not s:
        return None
    try:
        return json.loads(s)
    except Exception:
        return None


def _find_json_candidates(text: str) -> List[str]:
    """Find balanced ``{...}`` and ``[...]`` blocks in *text*. String-aware."""
    out: List[str] = []
    n = len(text)
    i = 0
    while i < n:
        c = text[i]
        if c not in "{[":
            i += 1
            continue
        opener = c
        closer = "}" if opener == "{" else "]"
        depth = 0
        in_str = False
        esc = False
        j = i
        found = False
        while j < n:
            ch = text[j]
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif in_str:
                if ch == '"':
                    in_str = False
            elif ch == '"':
                in_str = True
            elif ch == opener:
                depth += 1
            elif ch == closer:
                depth -= 1
                if depth == 0:
                    out.append(text[i : j + 1])
                    found = True
                    break
            j += 1
        if found:
            i = j + 1
        else:
            i += 1
    return out


def _dict_to_dataclass(cls: type, data: Any) -> Any:
    """Recursively build a dataclass instance from a dict.

    - Non-dict values are returned unchanged (so callers can pass primitives).
    - Extra keys not in the dataclass are silently dropped.
    - Nested fields with known dataclass types are recursed:
        SplitOption.plan -> SplitPlan
        OptionsConsidered.options -> List[SplitOption]
        PhaseExtractionPlan.phases -> List[Phase]
    """
    if not isinstance(data, dict):
        return data

    if cls is OptionsConsidered:
        opts_raw = data.get("options", []) or []
        opts: List[Any] = []
        for o in opts_raw:
            if isinstance(o, dict):
                opts.append(_dict_to_dataclass(SplitOption, o))
            else:
                opts.append(o)
        return OptionsConsidered(options=opts)

    if cls is SplitOption:
        kw: Dict[str, Any] = {}
        allowed = {f.name for f in dc_fields(cls)}
        for k, v in data.items():
            if k not in allowed:
                continue
            if k == "plan":
                kw[k] = _dict_to_dataclass(SplitPlan, v) if isinstance(v, dict) else v
            else:
                kw[k] = v
        return SplitOption(**kw)

    if cls is SplitPlan:
        allowed = {f.name for f in dc_fields(cls)}
        kw = {k: v for k, v in data.items() if k in allowed}
        return SplitPlan(**kw)

    if cls is PhaseExtractionPlan:
        phases_raw = data.get("phases", []) or []
        phases: List[Phase] = []
        for p in phases_raw:
            if isinstance(p, dict):
                phases.append(_dict_to_dataclass(Phase, p))
            else:
                phases.append(p)
        allowed = {f.name for f in dc_fields(cls)}
        kw = {k: v for k, v in data.items() if k in allowed and k != "phases"}
        kw["phases"] = phases
        return PhaseExtractionPlan(**kw)

    # Generic flat case
    try:
        allowed = {f.name for f in dc_fields(cls)}
    except TypeError:
        return data
    kw = {k: v for k, v in data.items() if k in allowed}
    try:
        return cls(**kw)
    except Exception:
        return None


def _parse_step_output(output: str, dataclass_cls: type) -> Optional[Any]:
    """Parse an LLM step's output text into a dataclass instance.

    Strategy:
      1. Look for any ``<NAME>_BEGIN ... <NAME>_END`` marker block matching
         this dataclass. If found, attempt JSON parse on the inner block
         (stripping markdown code fences).
      2. Otherwise, scan the output for balanced ``{...}`` / ``[...]`` blocks,
         try to JSON-parse each, and pick the largest valid one that
         produces a non-None dataclass instance.

    Returns the dataclass instance or ``None``.
    """
    if not output:
        return None

    aliases = _DATACLASS_MARKERS.get(dataclass_cls, [dataclass_cls.__name__.upper()])
    for name in aliases:
        block = _extract_marker_block(output, name)
        if block is None:
            continue
        data = _try_parse_json(block)
        if data is None:
            continue
        if dataclass_cls is OptionsConsidered and isinstance(data, list):
            data = {"options": data}
        if isinstance(data, dict):
            inst = _dict_to_dataclass(dataclass_cls, data)
            if inst is not None:
                return inst

    # Fallback: scan inline JSON candidates and pick the largest valid one.
    candidates = _find_json_candidates(output)
    best: Optional[Tuple[int, Any]] = None
    for cand in candidates:
        data = _try_parse_json(cand)
        if data is None:
            continue
        if dataclass_cls is OptionsConsidered and isinstance(data, list):
            data = {"options": data}
        if not isinstance(data, dict):
            continue
        inst = _dict_to_dataclass(dataclass_cls, data)
        if inst is None:
            continue
        size = len(cand)
        if best is None or size > best[0]:
            best = (size, inst)
    return best[1] if best else None


_FILE_MARKER_RE = re.compile(
    r"^FILES_(CREATED|MODIFIED):\s*(.*?)(?=^[A-Z_]+:|\n\s*\n|\Z)",
    re.MULTILINE | re.DOTALL,
)


def _parse_file_markers(output: str) -> Tuple[List[str], List[str]]:
    """Parse ``FILES_CREATED:`` and ``FILES_MODIFIED:`` markers from agent output."""
    if not output:
        return [], []
    created: List[str] = []
    modified: List[str] = []
    for m in _FILE_MARKER_RE.finditer(output):
        kind = m.group(1)
        body = m.group(2) or ""
        items: List[str] = []
        for line in body.splitlines():
            if line.strip() == "":
                continue
            for piece in line.split(","):
                p = piece.strip().strip(",").strip("`").strip()
                if p:
                    items.append(p)
        if kind == "CREATED":
            created.extend(items)
        else:
            modified.extend(items)

    def _dedup(xs: List[str]) -> List[str]:
        seen = set()
        out: List[str] = []
        for x in xs:
            if x not in seen:
                seen.add(x)
                out.append(x)
        return out

    return _dedup(created), _dedup(modified)


def _verdict_strength(verdict: str) -> str:
    v = (verdict or "").strip().lower()
    if v == "clear_improvement":
        return "strong"
    if v in ("marginal", "moderate"):
        return "moderate"
    return "weak"


def _apply_improvement_gate(
    quant_metrics: Dict[str, Any],
    qual_assess: Optional[QualitativeAssessment],
) -> str:
    """Decide what to do based on quantitative metrics and qualitative verdict.

    See spec's "Improvement Gate Decision Matrix" section.
    """
    qa = qual_assess or QualitativeAssessment(overall_verdict="moderate")
    strength = _verdict_strength(qa.overall_verdict)

    has_any = bool(quant_metrics)
    improves = 0
    regresses = 0
    if has_any:
        for v in quant_metrics.values():
            try:
                num = float(v)
            except (TypeError, ValueError):
                continue
            if num > 0:
                improves += 1
            elif num < 0:
                regresses += 1

    if not has_any:
        if strength == "strong":
            return "HUMAN_REVIEW_REQUIRED"
        if strength == "moderate":
            return "HUMAN_REVIEW_REQUIRED_MARGINAL"
        return "ABORT_NO_IMPROVEMENT"

    if regresses > 0:
        if strength == "strong":
            return "HUMAN_REVIEW_REQUIRED"
        return "ABORT_REGRESSION"

    if improves >= 1:
        if strength in ("strong", "moderate"):
            return "AUTO_SHIP"
        return "AUTO_SHIP_WARNING"

    # flat
    if strength == "strong":
        return "HUMAN_REVIEW_REQUIRED"
    return "ABORT_NO_IMPROVEMENT"


def _safe_lines(p: Path) -> int:
    try:
        return len(p.read_text(encoding="utf-8", errors="ignore").splitlines())
    except Exception:
        return 0


def _post_split_lines(work_dir: Path, target_file: str) -> int:
    candidates: List[Path] = []
    candidates.append(work_dir / target_file)
    base = Path(target_file)
    no_suffix = base.with_suffix("")
    candidates.append(work_dir / no_suffix / "__init__.py")
    candidates.append(work_dir / base.name)
    for c in candidates:
        if c.exists() and c.is_file():
            n = _safe_lines(c)
            if n:
                return n
    return 0


def _is_missing_module_stderr(stderr: str) -> bool:
    s = stderr or ""
    return (
        "ImportError" in s
        or "ModuleNotFoundError" in s
        or "No module named" in s
    )


def _run_subprocess(cmd: List[str], cwd: Path, timeout: float = 600.0) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def _state_dir_for(cwd: Path) -> Path:
    git_root = get_git_root(cwd) or cwd
    return git_root / ".pdd" / "split-state"


def _coerce_int(v: Any) -> int:
    if isinstance(v, bool):
        return int(v)
    if isinstance(v, int):
        return v
    if isinstance(v, list):
        return len(v)
    try:
        return int(v)
    except Exception:
        return 0


def _splitplan_field(plan: Any, name: str, default: Any) -> Any:
    """Get a field from a SplitPlan or dict-like plan."""
    if isinstance(plan, SplitPlan):
        return getattr(plan, name, default)
    if isinstance(plan, dict):
        return plan.get(name, default)
    return default


def _to_splitplan(plan_like: Any) -> SplitPlan:
    if isinstance(plan_like, SplitPlan):
        return plan_like
    if isinstance(plan_like, dict):
        return _dict_to_dataclass(SplitPlan, plan_like)
    return SplitPlan()


# ----------------------------- Main Orchestrator -----------------------------


def run_agentic_split_orchestrator(
    target_file: str,
    *,
    cwd: Path,
    verbose: bool = False,
    quiet: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
    diagnose_only: bool = False,
    propose_only: bool = False,
    delete_dead: bool = False,
    force_split: bool = False,
    no_verify: bool = False,
    skip_regen_gate: bool = False,
    experimental_language: bool = False,
    intent: Optional[str] = None,
    no_phase_extraction: bool = False,
) -> Tuple[bool, str, float, str, List[str]]:
    """Orchestrate the agentic split workflow.

    Returns a 5-tuple: ``(success, final_message, total_cost, model_used,
    changed_files)``.
    """

    # ---------- Language tier gate ----------
    language = _detect_language(target_file)
    if language not in SUPPORTED_LANGUAGES and not experimental_language:
        msg = f"Language not supported: {language}. Use --experimental-language."
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    if not quiet:
        console.print(f"[bold]Splitting {target_file}...[/bold]")

    # ---------- Identity / state ----------
    git_root = get_git_root(cwd)
    repo_root = git_root or cwd
    try:
        rel_target = str(Path(target_file).resolve().relative_to(repo_root.resolve()))
    except Exception:
        rel_target = target_file
    split_id = _stable_split_id(rel_target)
    state_dir = _state_dir_for(cwd)
    try:
        state_dir.mkdir(parents=True, exist_ok=True)
    except Exception:
        pass

    # repo owner / name (best-effort)
    repo_owner = ""
    repo_name = ""
    try:
        r = subprocess.run(
            ["git", "remote", "get-url", "origin"],
            cwd=str(repo_root),
            capture_output=True,
            text=True,
            timeout=15,
        )
        url = r.stdout.strip()
        m = re.search(r"[:/]([^/:]+)/([^/]+?)(?:\.git)?/?$", url)
        if m:
            repo_owner = m.group(1)
            repo_name = m.group(2)
    except Exception:
        pass

    # ---------- Load prior state ----------
    state, gh_comment_id = load_workflow_state(
        cwd=cwd,
        issue_number=split_id,
        workflow_type="split",
        state_dir=state_dir,
        repo_owner=repo_owner,
        repo_name=repo_name,
        use_github_state=use_github_state,
    )
    if state is None:
        state = {
            "step_outputs": {},
            "last_completed_step": None,
            "total_cost": 0.0,
            "model_used": "",
            "changed_files": [],
            "children_extracted": 0,
            "phase_plans": [],
            "verify_failures": [],
            "quant_metrics": {},
            "worktree_path": "",
            "intent": "",
            "iteration_count": 0,
            "_pending_refine": None,
        }
    else:
        state.setdefault("step_outputs", {})
        state.setdefault("last_completed_step", None)
        state.setdefault("total_cost", 0.0)
        state.setdefault("model_used", "")
        state.setdefault("changed_files", [])
        state.setdefault("children_extracted", 0)
        state.setdefault("phase_plans", [])
        state.setdefault("verify_failures", [])
        state.setdefault("quant_metrics", {})
        state.setdefault("worktree_path", "")
        state.setdefault("intent", "")
        state.setdefault("iteration_count", 0)
        state.setdefault("_pending_refine", None)
        if not quiet:
            console.print(
                f"[cyan]Resuming split workflow at step {state.get('last_completed_step')}[/cyan]"
            )

    total_cost: float = float(state.get("total_cost", 0.0) or 0.0)
    model_used: str = state.get("model_used", "") or ""
    changed_files: List[str] = list(state.get("changed_files", []) or [])

    # ---------- Architecture excerpt ----------
    arch_path = _find_architecture_json(target_file, cwd)
    arch_excerpt = ""
    if arch_path:
        try:
            arch_excerpt = arch_path.read_text(encoding="utf-8", errors="ignore")[:4000]
        except Exception:
            arch_excerpt = ""

    # ---------- Original line count ----------
    try:
        original_line_count = _safe_lines(cwd / target_file)
    except Exception:
        original_line_count = 0

    # ---------- Intent precedence ----------
    user_intent_hint = intent or ""
    cli_intent = _normalize_intent(intent)
    resolved_intent = cli_intent or _normalize_intent(state.get("intent")) or ""

    # ---------- Context ----------
    context: Dict[str, Any] = {
        "target_file": target_file,
        "language": language,
        "cwd": str(cwd),
        "verbose": verbose,
        "quiet": quiet,
        "diagnose_only": diagnose_only,
        "propose_only": propose_only,
        "delete_dead": delete_dead,
        "force_split": force_split,
        "no_verify": no_verify,
        "skip_regen_gate": skip_regen_gate,
        "experimental_language": experimental_language,
        "no_phase_extraction": no_phase_extraction,
        "original_line_count": original_line_count,
        "user_intent_hint": user_intent_hint,
        "intent": resolved_intent or "",
        "iteration_count": int(state.get("iteration_count", 0) or 0),
        "architecture_json_present": bool(arch_path),
        "architecture_json_excerpt": arch_excerpt,
        "phase_plan": "",
        "changed_files": list(changed_files),
    }

    # Restore step outputs into context
    for k, v in (state.get("step_outputs") or {}).items():
        context[f"step{k}_output"] = v

    # ---------- Step list ----------
    ordered_steps: List[Tuple[str, Optional[str]]] = [
        ("0_intent", "agentic_split_step0_intent_LLM"),
        ("1_survey", "agentic_split_step1_survey_LLM"),
        ("2_diagnose", "agentic_split_step2_diagnose_LLM"),
        ("3_investigate", "agentic_split_step3_investigate_LLM"),
        ("4_propose_options", "agentic_split_step4_propose_options_LLM"),
        ("5_setup_worktree", None),
        ("6a_phase_extract", "agentic_split_step6a_phase_extract_LLM"),
        ("6_extract", "agentic_split_step6_extract_LLM"),
        ("7a_verify_local", None),
        ("7b_regen_gate", None),
        ("7c_arch_sync", None),
        ("7_assess", "agentic_split_step7_assess_LLM"),
        ("8_repair", "agentic_split_step8_repair_LLM"),
        ("9_refine_check", "agentic_split_step9_refine_check_LLM"),
    ]
    total_steps = len(ordered_steps)
    step_index_map = {name: i + 1 for i, (name, _) in enumerate(ordered_steps)}

    # ---------- Signal handlers ----------
    _prev_sigint = signal.getsignal(signal.SIGINT)
    _prev_sigterm = signal.getsignal(signal.SIGTERM)

    def _signal_handler(signum: int, frame: Any) -> None:  # pragma: no cover
        try:
            state["total_cost"] = total_cost
            state["model_used"] = model_used
            state["changed_files"] = changed_files
            save_workflow_state(
                cwd, split_id, "split", state,
                state_dir=state_dir,
                repo_owner=repo_owner,
                repo_name=repo_name,
                use_github_state=use_github_state,
                github_comment_id=gh_comment_id,
            )
        except Exception:
            pass
        try:
            clear_agentic_progress()
        except Exception:
            pass
        sys.exit(130)

    def _restore_signals() -> None:
        try:
            signal.signal(signal.SIGINT, _prev_sigint)
            signal.signal(signal.SIGTERM, _prev_sigterm)
        except Exception:
            pass

    try:
        signal.signal(signal.SIGINT, _signal_handler)
        signal.signal(signal.SIGTERM, _signal_handler)
    except Exception:
        pass

    # ---------- Helpers bound to closure ----------
    def _persist_state() -> None:
        nonlocal gh_comment_id
        state["total_cost"] = total_cost
        state["model_used"] = model_used
        state["changed_files"] = changed_files
        try:
            new_id = save_workflow_state(
                cwd, split_id, "split", state,
                state_dir=state_dir,
                repo_owner=repo_owner,
                repo_name=repo_name,
                use_github_state=use_github_state,
                github_comment_id=gh_comment_id,
            )
            if new_id is not None:
                gh_comment_id = new_id
        except Exception:
            pass

    def _record_step(step_key: str, output: str) -> None:
        pref = step_key.split("_", 1)[0]
        state["step_outputs"][pref] = output
        context[f"step{pref}_output"] = output
        state["last_completed_step"] = step_key

    def _run_llm_step(
        step_key: str,
        template_name: str,
        extra_context: Optional[Dict[str, Any]] = None,
        label_override: Optional[str] = None,
        appendix: str = "",
        work_dir: Optional[Path] = None,
    ) -> Tuple[bool, str]:
        nonlocal total_cost, model_used
        template = load_prompt_template(template_name)
        if not template:
            return False, f"Missing template: {template_name}"
        merged_ctx = dict(context)
        if extra_context:
            merged_ctx.update(extra_context)
        try:
            processed = preprocess(
                template,
                recursive=True,
                double_curly_brackets=True,
                exclude_keys=list(merged_ctx.keys()),
            )
        except Exception as e:
            return False, f"Preprocess failed: {e}"
        try:
            formatted = substitute_template_variables(processed, merged_ctx)
        except Exception as e:
            return False, f"Template substitution failed: {e}"
        if appendix:
            formatted = formatted + "\n\n" + appendix

        wd = work_dir if work_dir is not None else cwd
        timeout = SPLIT_STEP_TIMEOUTS.get(step_key, 600.0) + timeout_adder
        ok, out, cost, provider = run_agentic_task(
            instruction=formatted,
            cwd=wd,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout,
            label=label_override or f"split-{step_key}",
            max_retries=DEFAULT_MAX_RETRIES,
        )
        total_cost += float(cost or 0.0)
        if provider:
            model_used = provider
        return ok, out

    def _early_return(success: bool, msg: str) -> Tuple[bool, str, float, str, List[str]]:
        _persist_state()
        try:
            clear_agentic_progress()
        except Exception:
            pass
        if not quiet and not success:
            console.print(
                f"[yellow]State preserved at {state_dir} — rerun pdd split to resume...[/yellow]"
            )
        _restore_signals()
        return success, msg, total_cost, model_used, changed_files

    def _started_or_done(step_key: str) -> str:
        last = state.get("last_completed_step")
        if not last:
            return "run"
        last_idx = step_index_map.get(last, 0)
        cur_idx = step_index_map.get(step_key, 0)
        if cur_idx <= last_idx:
            return "skip"
        return "run"

    # =============== STEP 0: INTENT ===============
    step_key = "0_intent"
    if _started_or_done(step_key) != "skip":
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)
        if resolved_intent:
            out = f"Skipped — intent already set: {resolved_intent}"
            _record_step(step_key, out)
            state["intent"] = resolved_intent
            context["intent"] = resolved_intent
        else:
            ok, out = _run_llm_step(step_key, "agentic_split_step0_intent_LLM")
            if not ok:
                resolved_intent = "REDUCE_MONOLITH"
                if not quiet:
                    console.print(
                        "[yellow]Step 0 failed; defaulting intent to REDUCE_MONOLITH[/yellow]"
                    )
                state["intent"] = resolved_intent
                context["intent"] = resolved_intent
                _record_step(step_key, "Default intent applied: REDUCE_MONOLITH")
            else:
                decision = _parse_step_output(out, IntentDecision) or IntentDecision()
                norm = _normalize_intent(decision.intent) or "REDUCE_MONOLITH"
                resolved_intent = norm
                state["intent"] = resolved_intent
                context["intent"] = resolved_intent
                if not quiet:
                    console.print(
                        f"[green]Intent: {decision.intent} (conf={float(decision.confidence or 0.0):.2f})[/green]"
                    )
                _record_step(step_key, out)
        _persist_state()

    if not resolved_intent:
        resolved_intent = _normalize_intent(state.get("intent")) or "REDUCE_MONOLITH"
        state["intent"] = resolved_intent
        context["intent"] = resolved_intent

    # =============== STEP 1: SURVEY ===============
    step_key = "1_survey"
    if _started_or_done(step_key) != "skip":
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)
        ok, out = _run_llm_step(step_key, "agentic_split_step1_survey_LLM")
        if not ok:
            return _early_return(False, f"Step 1 failed: {out[:200]}")
        marker = _check_hard_stop(step_key, out, force_split)
        if marker:
            _record_step(step_key, out)
            return _early_return(False, f"Stopped: {marker}")
        _record_step(step_key, out)
        _persist_state()

    # =============== STEP 2: DIAGNOSE ===============
    step_key = "2_diagnose"
    diagnosis: Optional[Diagnosis] = None
    if _started_or_done(step_key) != "skip":
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)
        ok, out = _run_llm_step(step_key, "agentic_split_step2_diagnose_LLM")
        if not ok:
            return _early_return(False, f"Step 2 failed: {out[:200]}")
        diagnosis = _parse_step_output(out, Diagnosis) or Diagnosis()
        if not quiet and (diagnosis.type or diagnosis.recommended_action):
            console.print(
                f"[green]Diagnosis: {diagnosis.type or diagnosis.recommended_action} — {diagnosis.rationale}[/green]"
            )
        marker = _check_hard_stop(step_key, out, force_split)
        leave_alone = (
            (diagnosis.recommended_action or "").upper() == "LEAVE_ALONE"
            or (diagnosis.type or "").upper() == "LEAVE_ALONE"
        )
        if marker or (leave_alone and not force_split):
            _record_step(step_key, out)
            return _early_return(
                False,
                f"Stopped: LEAVE_ALONE — {diagnosis.leave_alone_rationale or diagnosis.rationale}",
            )
        _record_step(step_key, out)
        _persist_state()

        if diagnose_only:
            return _early_return(
                False,
                f"Diagnosis: {diagnosis.type or diagnosis.recommended_action} — {diagnosis.rationale}",
            )

    # =============== STEP 3: INVESTIGATE ===============
    step_key = "3_investigate"
    investigation: Optional[ModuleInvestigation] = None
    if _started_or_done(step_key) != "skip":
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)
        ok, out = _run_llm_step(step_key, "agentic_split_step3_investigate_LLM")
        if not ok:
            return _early_return(False, f"Step 3 failed: {out[:200]}")
        marker = _check_hard_stop(step_key, out, force_split)
        if marker:
            _record_step(step_key, out)
            return _early_return(False, f"Stopped: {marker}")
        investigation = _parse_step_output(out, ModuleInvestigation) or ModuleInvestigation()
        _record_step(step_key, out)
        _persist_state()
    else:
        prev = state["step_outputs"].get("3", "")
        investigation = _parse_step_output(prev, ModuleInvestigation) or ModuleInvestigation()

    shared_layer_candidates = list(getattr(investigation, "shared_layer_candidates", []) or [])

    # =============== STEP 4: PROPOSE OPTIONS ===============
    step_key = "4_propose_options"
    selected_option: Optional[SplitOption] = None
    options_obj: Optional[OptionsConsidered] = None
    if _started_or_done(step_key) != "skip":
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)

        appendix = ""
        attempts = 0
        max_attempts = 3
        last_out = ""
        while attempts < max_attempts:
            attempts += 1
            ok, out = _run_llm_step(
                step_key,
                "agentic_split_step4_propose_options_LLM",
                extra_context={"intent": resolved_intent},
                appendix=appendix,
            )
            last_out = out
            if not ok:
                return _early_return(False, f"Step 4 failed: {out[:200]}")
            marker = _check_hard_stop(step_key, out, force_split)
            if marker:
                _record_step(step_key, out)
                return _early_return(False, f"Stopped: {marker}")
            options_obj = _parse_step_output(out, OptionsConsidered) or OptionsConsidered()
            options_list: List[SplitOption] = [o for o in (options_obj.options or []) if isinstance(o, SplitOption)]
            if not options_list:
                appendix = "% RETRY NOTICE — no parseable options"
                continue
            options_list.sort(key=lambda o: o.numeric_score, reverse=True)
            selected_option = options_list[0]

            # Shared-layer hard gate
            if shared_layer_candidates:
                pc = selected_option.parent_changes or {}
                slc = pc.get("shared_layer_children", []) or _splitplan_field(
                    selected_option.plan, "shared_layer_children", []
                ) or []
                if not slc:
                    if attempts < max_attempts:
                        appendix = (
                            "% RETRY NOTICE — shared_layer_children required\n"
                            f"Investigation surfaced shared_layer_candidates: "
                            f"{json.dumps(shared_layer_candidates)}. The selected option "
                            "MUST populate parent_changes.shared_layer_children."
                        )
                        continue
                    else:
                        state["verify_failures"].append(
                            {
                                "check": "shared_layer_gate",
                                "message": "Selected option missing shared_layer_children after retries",
                                "severity": "warning",
                            }
                        )
            break

        # Render options table
        if not quiet and options_obj and options_obj.options:
            table = Table(title="Proposed Split Options")
            table.add_column("Option")
            table.add_column("Score")
            for opt in options_obj.options:
                if isinstance(opt, SplitOption):
                    nm = opt.name
                    sc_raw = opt.score
                else:
                    nm = (opt.get("name", "") if isinstance(opt, dict) else str(opt))
                    sc_raw = (opt.get("score", 0.0) if isinstance(opt, dict) else 0.0)
                if isinstance(sc_raw, dict):
                    sc = sc_raw.get("total", "")
                else:
                    sc = sc_raw
                table.add_row(str(nm), str(sc))
            console.print(table)

        _record_step(step_key, last_out)
        if selected_option is not None:
            state["selected_option"] = {
                "name": selected_option.name,
                "description": selected_option.description,
                "score": selected_option.score,
                "plan": asdict(_to_splitplan(selected_option.plan)),
                "parent_changes": selected_option.parent_changes,
            }
        _persist_state()
    else:
        # Restore selection: prefer state["selected_option"], then re-parse step_outputs["4"]
        sel = state.get("selected_option")
        if sel:
            selected_option = SplitOption(
                name=sel.get("name", ""),
                description=sel.get("description", ""),
                score=sel.get("score", 0.0),
                plan=_to_splitplan(sel.get("plan")),
                parent_changes=sel.get("parent_changes", {}) or {},
            )
        else:
            prev = state["step_outputs"].get("4", "")
            opts = _parse_step_output(prev, OptionsConsidered)
            if opts and opts.options:
                cand = [o for o in opts.options if isinstance(o, SplitOption)]
                if cand:
                    cand.sort(key=lambda o: o.numeric_score, reverse=True)
                    selected_option = cand[0]

    if propose_only:
        return _early_return(False, "Propose only complete")

    if selected_option is None:
        return _early_return(False, "No selected option — step 4 may have failed")

    # Build SplitPlan from selected option
    split_plan = _to_splitplan(selected_option.plan)
    # Merge in parent_changes from option-level field if SplitPlan didn't already have them
    if not split_plan.parent_changes and selected_option.parent_changes:
        split_plan.parent_changes = dict(selected_option.parent_changes)
    if not split_plan.shared_layer_children:
        slc = (selected_option.parent_changes or {}).get("shared_layer_children", [])
        if slc:
            split_plan.shared_layer_children = list(slc)

    # =============== STEP 5: SETUP WORKTREE ===============
    step_key = "5_setup_worktree"
    work_dir: Path = cwd
    if _started_or_done(step_key) != "skip":
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)
        if not git_root:
            return _early_return(False, "Not a git repository")
        wt_path, err = setup_worktree(
            cwd=cwd,
            issue_number=split_id,
            quiet=quiet,
            branch_prefix="split",
            worktree_prefix="split",
            base_ref="HEAD",
        )
        if not wt_path:
            return _early_return(False, f"Worktree setup failed: {err}")
        work_dir = wt_path
        state["worktree_path"] = str(wt_path)
        _record_step(step_key, f"Worktree at {wt_path}")
        _persist_state()
    else:
        wp = state.get("worktree_path")
        if wp and Path(wp).is_dir():
            work_dir = Path(wp)
        else:
            work_dir = cwd

    children = list(split_plan.children or [])
    num_children = len(children)

    # =============== STEP 6a: PHASE EXTRACT (per child) ===============
    step_key = "6a_phase_extract"
    phase_plans: List[Optional[Dict[str, Any]]] = list(state.get("phase_plans") or [])
    while len(phase_plans) < num_children:
        phase_plans.append(None)

    if no_phase_extraction:
        for i in range(num_children):
            phase_plans[i] = None
        state["phase_plans"] = phase_plans
        if _started_or_done(step_key) != "skip":
            _record_step(step_key, "Skipped (no_phase_extraction)")
            _persist_state()
    elif _started_or_done(step_key) != "skip":
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)
        for i, child in enumerate(children):
            if phase_plans[i] is not None:
                continue
            if not quiet:
                console.print(f"[cyan]Phase-extract analysis {i+1}/{num_children}: {child}[/cyan]")
            sel_dict = {
                "name": selected_option.name,
                "description": selected_option.description,
                "score": selected_option.score,
                "plan": asdict(_to_splitplan(selected_option.plan)),
                "parent_changes": selected_option.parent_changes,
            }
            extra = {
                "current_child_index": i,
                "current_child": json.dumps(child) if not isinstance(child, str) else child,
                "selected_option": json.dumps(sel_dict),
                "children_extracted": _coerce_int(state.get("children_extracted", 0)),
            }
            ok, out = _run_llm_step(
                step_key,
                "agentic_split_step6a_phase_extract_LLM",
                extra_context=extra,
                label_override=f"split-6a_phase_extract-child{i+1}",
                work_dir=work_dir,
            )
            if not ok:
                phase_plans[i] = {"should_extract": False, "reason": "agent failed"}
            else:
                pp = _parse_step_output(out, PhaseExtractionPlan)
                if pp is None:
                    phase_plans[i] = {"should_extract": False, "reason": "output unparseable"}
                else:
                    try:
                        phase_plans[i] = asdict(pp)
                    except Exception:
                        phase_plans[i] = {"should_extract": False, "reason": "asdict failed"}
            state["phase_plans"] = phase_plans
            _persist_state()
        _record_step(step_key, f"Phase plans for {num_children} children")
        _persist_state()

    # =============== STEP 6: EXTRACT (per child) ===============
    step_key = "6_extract"
    children_extracted: int = _coerce_int(state.get("children_extracted", 0))
    if _started_or_done(step_key) != "skip" or children_extracted < num_children:
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)

        for i in range(children_extracted, num_children):
            child = children[i]
            if not quiet:
                console.print(f"[cyan]Extracting child {i+1}/{num_children}: {child}[/cyan]")
            phase_plan_val = phase_plans[i] if i < len(phase_plans) else None
            phase_plan_str = json.dumps(phase_plan_val) if phase_plan_val else ""

            sel_dict = {
                "name": selected_option.name,
                "description": selected_option.description,
                "score": selected_option.score,
                "plan": asdict(_to_splitplan(selected_option.plan)),
                "parent_changes": selected_option.parent_changes,
            }
            extra = {
                "current_child_index": i,
                "current_child": json.dumps(child) if not isinstance(child, str) else child,
                "selected_option": json.dumps(sel_dict),
                "children_extracted": children_extracted,
                "phase_plan": phase_plan_str,
                "allow_dead_symbol_deletion": delete_dead and (i == num_children - 1),
            }
            context["phase_plan"] = phase_plan_str

            attempts = 0
            max_attempts = 3
            appendix = ""
            success_for_child = False
            last_out = ""
            while attempts < max_attempts:
                attempts += 1
                ok, out = _run_llm_step(
                    step_key,
                    "agentic_split_step6_extract_LLM",
                    extra_context=extra,
                    label_override=f"split-6_extract-child{i+1}",
                    appendix=appendix,
                    work_dir=work_dir,
                )
                last_out = out
                if not ok:
                    appendix = "% RETRY NOTICE — previous attempt failed"
                    continue
                marker = _check_hard_stop(step_key, out, force_split)
                if marker:
                    _record_step(step_key, out)
                    return _early_return(False, f"Stopped: {marker}")
                claimed_created, claimed_modified = _parse_file_markers(out)
                missing = [p for p in claimed_created if not (work_dir / p).exists()]
                if missing:
                    if attempts < max_attempts:
                        appendix = (
                            "% RETRY NOTICE — MUST CREATE MISSING FILES\n"
                            f"The following claimed FILES_CREATED do not exist: {missing}"
                        )
                        continue
                    else:
                        state["verify_failures"].append(
                            {
                                "check": "files_created_missing",
                                "message": f"Child {i+1} missing files after retries: {missing}",
                                "severity": "error",
                            }
                        )
                        _persist_state()
                        return _early_return(
                            False,
                            f"Stopped: extraction missing files for child {i+1}: {missing}",
                        )
                # Vacuously true if no FILES_CREATED marker present
                for p in claimed_created:
                    if (work_dir / p).exists() and p not in changed_files:
                        changed_files.append(p)
                for p in claimed_modified:
                    if p not in changed_files:
                        changed_files.append(p)
                success_for_child = True
                break

            if success_for_child:
                children_extracted = i + 1
                state["children_extracted"] = children_extracted
                _record_step(step_key, last_out)
                context["changed_files"] = list(changed_files)
                _persist_state()
            else:
                _persist_state()
                return _early_return(False, f"Extraction failed for child {i+1}")

        _record_step(step_key, f"Extracted {children_extracted}/{num_children}")
        _persist_state()

    # =============== STEP 7a: VERIFY LOCAL ===============
    step_key = "7a_verify_local"
    quant_metrics: Dict[str, Any] = dict(state.get("quant_metrics") or {})
    verify_failures: List[Dict[str, Any]] = list(state.get("verify_failures") or [])

    if _started_or_done(step_key) != "skip":
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)

        post_lines = _post_split_lines(work_dir, target_file)
        if original_line_count and post_lines:
            quant_metrics["parent_line_reduction"] = original_line_count - post_lines
        if num_children > 1:
            quant_metrics["children_created"] = num_children - 1

        if no_verify:
            if not quiet:
                console.print(
                    "[bold yellow]!! VERIFICATION SKIPPED (--no-verify) — split will not auto-ship[/bold yellow]"
                )
            quant_metrics["verification_skipped"] = 0
            quant_metrics["validation_pass"] = 0
        else:
            try:
                vres = validate_extraction(split_plan, work_dir)
                err_failures = [
                    f for f in (vres.failures or [])
                    if getattr(f, "severity", "error") == "error"
                ]
                warn_failures = [
                    f for f in (vres.failures or [])
                    if getattr(f, "severity", "error") == "warning"
                ]
                if not quiet and (err_failures or warn_failures):
                    console.print(
                        f"[red]Validation: {len(err_failures)} errors, {len(warn_failures)} warnings[/red]"
                    )
                for f in err_failures:
                    verify_failures.append(
                        {
                            "check": getattr(f, "check", ""),
                            "message": getattr(f, "message", ""),
                            "severity": "error",
                        }
                    )
                quant_metrics["validation_pass"] = 1 if not err_failures else -1
            except Exception as e:
                quant_metrics["validation_pass"] = -1
                verify_failures.append(
                    {"check": "validate_extraction", "message": str(e), "severity": "error"}
                )

            try:
                tcmd = get_test_command(Path(target_file))
                if tcmd:
                    cmd = getattr(tcmd, "command", None) or getattr(tcmd, "argv", None)
                    cmd_list = cmd.split() if isinstance(cmd, str) else list(cmd or [])
                    if cmd_list:
                        try:
                            res = _run_subprocess(cmd_list, work_dir, timeout=600.0)
                            if res.returncode != 0:
                                if _is_missing_module_stderr((res.stderr or "") + (res.stdout or "")):
                                    pass  # skip — missing deps
                                else:
                                    quant_metrics["tests_pass"] = -1
                                    verify_failures.append(
                                        {
                                            "check": "tests",
                                            "message": (res.stderr or res.stdout or "")[:500],
                                            "severity": "error",
                                        }
                                    )
                            else:
                                quant_metrics["tests_pass"] = 1
                        except Exception as e:
                            quant_metrics["tests_pass"] = -1
                            verify_failures.append(
                                {"check": "tests", "message": str(e)[:500], "severity": "error"}
                            )
            except Exception:
                pass

            try:
                lints = get_lint_commands(Path(target_file)) or []
                for lc in lints:
                    cmd = getattr(lc, "command", None) or getattr(lc, "argv", None)
                    cmd_list = cmd.split() if isinstance(cmd, str) else list(cmd or [])
                    if not cmd_list:
                        continue
                    try:
                        res = _run_subprocess(cmd_list, work_dir, timeout=300.0)
                        if res.returncode != 0:
                            verify_failures.append(
                                {
                                    "check": "lint",
                                    "message": (res.stderr or res.stdout or "")[:500],
                                    "severity": "error",
                                }
                            )
                    except Exception as e:
                        verify_failures.append(
                            {"check": "lint", "message": str(e)[:500], "severity": "error"}
                        )
            except Exception:
                pass

        state["quant_metrics"] = quant_metrics
        state["verify_failures"] = verify_failures
        _record_step(step_key, json.dumps({"quant_metrics": quant_metrics, "failures": len(verify_failures)}))
        _persist_state()

    # =============== STEP 7b: REGEN GATE ===============
    step_key = "7b_regen_gate"
    if _started_or_done(step_key) != "skip":
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)

        if skip_regen_gate:
            _record_step(step_key, "Skipped (skip_regen_gate)")
        else:
            prompt_files = [f for f in changed_files if f.endswith(".prompt")]
            for pf in prompt_files:
                basename = Path(pf).stem
                try:
                    res = _run_subprocess(
                        ["pdd", "sync", basename, "--max-attempts", "1", "--budget", "5.0"],
                        work_dir,
                        timeout=1800.0,
                    )
                    combined = (res.stdout or "") + "\n" + (res.stderr or "")
                    marker = _check_hard_stop(step_key, combined, force_split)
                    if marker or res.returncode != 0:
                        verify_failures.append(
                            {
                                "check": "regen_gate",
                                "message": f"sync failed for {basename}: "
                                f"{(res.stderr or res.stdout or '')[:500]}",
                                "severity": "error",
                            }
                        )
                except Exception as e:
                    verify_failures.append(
                        {"check": "regen_gate", "message": str(e)[:500], "severity": "error"}
                    )
            state["verify_failures"] = verify_failures
            _record_step(step_key, f"Regen gate processed {len(prompt_files)} prompts")
        _persist_state()

    # =============== STEP 7c: ARCH SYNC ===============
    step_key = "7c_arch_sync"
    if _started_or_done(step_key) != "skip":
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)
        prompts_dir, arch_p = _find_arch_dirs(target_file, work_dir)
        if not prompts_dir or not arch_p:
            if not quiet:
                console.print(
                    "[yellow]Skipping arch sync — prompts dir or architecture.json not found[/yellow]"
                )
            _record_step(step_key, "Skipped (missing prompts/architecture)")
        else:
            try:
                result = sync_all_prompts_to_architecture(
                    prompts_dir=prompts_dir,
                    architecture_path=arch_p,
                    dry_run=False,
                )
                changed_stems = {Path(f).stem for f in changed_files}
                for err in (result.get("errors", []) if isinstance(result, dict) else []) or []:
                    if any(stem and stem in err for stem in changed_stems):
                        verify_failures.append(
                            {"check": "arch_sync", "message": err[:500], "severity": "error"}
                        )
                state["verify_failures"] = verify_failures
                _record_step(step_key, "Arch sync complete")
            except Exception as e:
                if not quiet:
                    console.print(f"[yellow]Arch sync error: {e}[/yellow]")
                _record_step(step_key, f"Arch sync error: {e}")
        _persist_state()

    # =============== STEP 7: ASSESS ===============
    step_key = "7_assess"
    qual_assess: Optional[QualitativeAssessment] = None
    if _started_or_done(step_key) != "skip":
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)
        post_state = {
            "children_extracted": children_extracted,
            "changed_files": changed_files,
            "verify_failures_count": len(verify_failures),
        }
        ok, out = _run_llm_step(
            step_key,
            "agentic_split_step7_assess_LLM",
            extra_context={
                "quantitative_metrics": json.dumps(quant_metrics),
                "post_split_state": json.dumps(post_state),
            },
        )
        if not ok:
            qual_assess = QualitativeAssessment(
                overall_verdict="moderate",
                rationale="Defaulted: step 7 failed",
            )
        else:
            qual_assess = _parse_step_output(out, QualitativeAssessment)
            if qual_assess is None:
                qual_assess = QualitativeAssessment(
                    overall_verdict="moderate",
                    rationale="Defaulted: step 7 output unparseable",
                )
        _record_step(step_key, out if ok else "fallback moderate")
        try:
            state["assessment"] = asdict(qual_assess)
        except Exception:
            state["assessment"] = {"overall_verdict": qual_assess.overall_verdict}
        _persist_state()
    else:
        a = state.get("assessment")
        if a:
            allowed = {f.name for f in dc_fields(QualitativeAssessment)}
            qual_assess = QualitativeAssessment(**{k: v for k, v in a.items() if k in allowed})

    # =============== STEP 8: REPAIR (if needed) ===============
    step_key = "8_repair"
    if verify_failures and _started_or_done(step_key) != "skip":
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)

        prev_count = len([f for f in verify_failures if f.get("severity") == "error"])
        for iteration in range(1, 6):
            err_count_before = len([f for f in verify_failures if f.get("severity") == "error"])
            ok, out = _run_llm_step(
                step_key,
                "agentic_split_step8_repair_LLM",
                extra_context={
                    "verify_failures": json.dumps(verify_failures),
                    "iteration": iteration,
                },
                label_override=f"split-8_repair-iter{iteration}",
                work_dir=work_dir,
            )
            if ok:
                marker = _check_hard_stop(step_key, out, force_split)
                if marker:
                    if not quiet:
                        console.print(f"[red]Repair: {marker}[/red]")
                    break
                created, modified = _parse_file_markers(out)
                for p in created + modified:
                    if (work_dir / p).exists() and p not in changed_files:
                        changed_files.append(p)

            new_failures: List[Dict[str, Any]] = []
            try:
                vres = validate_extraction(split_plan, work_dir)
                for f in vres.failures or []:
                    if getattr(f, "severity", "error") == "error":
                        new_failures.append(
                            {
                                "check": getattr(f, "check", ""),
                                "message": getattr(f, "message", ""),
                                "severity": "error",
                            }
                        )
            except Exception as e:
                new_failures.append(
                    {"check": "validate_extraction", "message": str(e), "severity": "error"}
                )
            try:
                tcmd = get_test_command(Path(target_file))
                if tcmd:
                    cmd = getattr(tcmd, "command", None) or getattr(tcmd, "argv", None)
                    cmd_list = cmd.split() if isinstance(cmd, str) else list(cmd or [])
                    if cmd_list:
                        res = _run_subprocess(cmd_list, work_dir, timeout=600.0)
                        if res.returncode != 0:
                            if not _is_missing_module_stderr((res.stderr or "") + (res.stdout or "")):
                                new_failures.append(
                                    {
                                        "check": "tests",
                                        "message": (res.stderr or res.stdout or "")[:500],
                                        "severity": "error",
                                    }
                                )
            except Exception:
                pass
            try:
                for lc in get_lint_commands(Path(target_file)) or []:
                    cmd = getattr(lc, "command", None) or getattr(lc, "argv", None)
                    cmd_list = cmd.split() if isinstance(cmd, str) else list(cmd or [])
                    if not cmd_list:
                        continue
                    res = _run_subprocess(cmd_list, work_dir, timeout=300.0)
                    if res.returncode != 0:
                        new_failures.append(
                            {
                                "check": "lint",
                                "message": (res.stderr or res.stdout or "")[:500],
                                "severity": "error",
                            }
                        )
            except Exception:
                pass

            verify_failures = new_failures
            quant_metrics["validation_pass"] = 1 if not new_failures else -1
            err_count_after = len(new_failures)
            if not quiet:
                console.print(
                    f"[cyan]Repair iter {iteration}: {err_count_before} -> {err_count_after} error-severity failures[/cyan]"
                )
            state["verify_failures"] = verify_failures
            state["quant_metrics"] = quant_metrics
            _persist_state()
            if err_count_after == 0:
                break
            if iteration > 1 and err_count_after >= prev_count:
                if not quiet:
                    console.print("[yellow]Repair: failure count not decreasing — stopping[/yellow]")
                break
            prev_count = err_count_after
        _record_step(step_key, f"Repair finished with {len(verify_failures)} failures")
        _persist_state()

    # =============== Improvement Gate ===============
    decision = _apply_improvement_gate(quant_metrics, qual_assess)
    if not quiet:
        console.print(f"[bold]Decision: {decision}[/bold]")
    if "ABORT" in decision:
        return _early_return(False, f"Improvement gate: {decision}")

    # =============== STEP 9: REFINE CHECK ===============
    step_key = "9_refine_check"
    refine: Optional[RefineCheck] = None
    iter_count = int(state.get("iteration_count", 0) or 0)
    if _started_or_done(step_key) != "skip":
        idx = step_index_map[step_key]
        if not quiet:
            console.print(f"[bold cyan][Step {idx}/{total_steps}] {step_key}...[/bold cyan]")
        set_agentic_progress("split", idx, total_steps, step_key)
        context["changed_files"] = list(changed_files)
        ok, out = _run_llm_step(
            step_key,
            "agentic_split_step9_refine_check_LLM",
            extra_context={
                "quantitative_metrics": json.dumps(quant_metrics),
                "changed_files": json.dumps(changed_files),
                "iteration_count": iter_count,
            },
        )
        if ok:
            refine = _parse_step_output(out, RefineCheck) or RefineCheck()
            if refine.should_refine:
                if not quiet:
                    console.print(
                        f"[yellow]Refine suggested on {refine.target_child_file}: {refine.reason}[/yellow]"
                    )
                state["_pending_refine"] = {
                    "target_child_file": refine.target_child_file,
                    "reason": refine.reason,
                    "suggested_intent": refine.suggested_intent,
                }
            else:
                if not quiet:
                    console.print(f"[green]Refine check: ship as-is ({refine.reason})[/green]")
                state["_pending_refine"] = None
        _record_step(step_key, out if ok else "")
        _persist_state()

    # =============== Refinement Pass ===============
    pending = state.get("_pending_refine")
    if pending and iter_count < MAX_REFINEMENT_ITERATIONS and not no_phase_extraction:
        target_child = pending.get("target_child_file", "")
        target_path = work_dir / target_child if target_child else None
        if target_path and target_path.exists():
            iter_count += 1
            state["iteration_count"] = iter_count
            state["_pending_refine"] = None
            context["iteration_count"] = iter_count
            if not quiet:
                console.print(f"[cyan]Running refinement pass on {target_child}[/cyan]")
            synth_child = {"name": Path(target_child).stem, "code_file": target_child}
            extra6a = {
                "current_child_index": 0,
                "current_child": json.dumps(synth_child),
                "selected_option": json.dumps(
                    {"name": "refinement", "description": pending.get("reason", "")}
                ),
                "children_extracted": 0,
            }
            ok, out = _run_llm_step(
                "6a_phase_extract",
                "agentic_split_step6a_phase_extract_LLM",
                extra_context=extra6a,
                label_override="split-refine-6a_phase_extract",
                work_dir=work_dir,
            )
            pp = None
            if ok:
                pp = _parse_step_output(out, PhaseExtractionPlan)
            if pp and pp.should_extract:
                phase_str = json.dumps(asdict(pp))
                extra6 = dict(extra6a)
                extra6["phase_plan"] = phase_str
                context["phase_plan"] = phase_str
                ok2, out2 = _run_llm_step(
                    "6_extract",
                    "agentic_split_step6_extract_LLM",
                    extra_context=extra6,
                    label_override="split-refine-6_extract",
                    work_dir=work_dir,
                )
                if ok2:
                    created, modified = _parse_file_markers(out2)
                    for p in created + modified:
                        if (work_dir / p).exists() and p not in changed_files:
                            changed_files.append(p)
                try:
                    vres = validate_extraction(split_plan, work_dir)
                    new_fails = []
                    for f in vres.failures or []:
                        if getattr(f, "severity", "error") == "error":
                            new_fails.append(
                                {
                                    "check": getattr(f, "check", ""),
                                    "message": getattr(f, "message", ""),
                                    "severity": "error",
                                }
                            )
                    verify_failures = new_fails
                    quant_metrics["validation_pass"] = 1 if not new_fails else -1
                    state["verify_failures"] = verify_failures
                    state["quant_metrics"] = quant_metrics
                except Exception:
                    pass
            _persist_state()
        else:
            if not quiet and target_child:
                console.print(f"[yellow]Refine target missing on disk: {target_child}[/yellow]")
            state["_pending_refine"] = None
            _persist_state()

    # =============== Cleanup / Final ===============
    final_msg = f"Split complete ({decision})"
    if not quiet:
        console.print("[bold green]Split complete[/bold green]")
        console.print(f"Total cost: ${total_cost:.4f}")
        console.print(f"Files changed: {changed_files}")
        console.print(f"Decision: {decision}")

    if decision == "AUTO_SHIP":
        try:
            clear_workflow_state(
                cwd=cwd,
                issue_number=split_id,
                workflow_type="split",
                state_dir=state_dir,
                repo_owner=repo_owner,
                repo_name=repo_name,
                use_github_state=use_github_state,
            )
        except Exception:
            pass
        wp = state.get("worktree_path")
        if wp and git_root:
            try:
                subprocess.run(
                    ["git", "worktree", "remove", "--force", str(wp)],
                    cwd=str(git_root),
                    capture_output=True,
                    text=True,
                    timeout=60,
                )
            except Exception:
                pass

    try:
        clear_agentic_progress()
    except Exception:
        pass
    _restore_signals()
    return True, final_msg, total_cost, model_used, changed_files
