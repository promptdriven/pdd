from __future__ import annotations

import json
import re
import signal
import shlex
import subprocess
import shutil
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union

from rich.console import Console
from rich.table import Table

from .agentic_common import (
    DEFAULT_MAX_RETRIES,
    clear_workflow_state,
    load_workflow_state,
    run_agentic_task,
    save_workflow_state,
    set_agentic_progress,
    substitute_template_variables,
    clear_agentic_progress,
)
from .agentic_common_worktree import get_git_root, setup_worktree
from .architecture_sync import sync_all_prompts_to_architecture
from .get_language import get_language
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .split_validation import get_lint_commands, get_test_command, validate_extraction

console = Console()

# Per-Step Timeouts
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

# Max refinement passes after the main pipeline (U6).
# The pipeline runs once, step 9 asks "should we refine?", and if yes we
# run a focused phase-extraction pass (step 6a + step 6) on one flagged
# child. That's it — we do NOT loop back to step 9 for another refine
# check, because that would require re-running assess/repair and the
# marginal gain after iteration 1 was not worth the cost on our oracle
# (pdd_executor: iter 1 added $30 to iter 0's $45, iter 2 would've
# added more). A re-run of `pdd split` on the output always gives the
# user another refinement pass if they want one.
MAX_REFINEMENT_ITERATIONS = 1

# Valid intent values (U5).
VALID_INTENTS = {
    "REDUCE_MONOLITH",
    "ENABLE_PARALLEL_WORK",
    "EXTRACT_REUSABLE_LAYER",
    "REDUCE_TEST_TIME",
}

# Map CLI short form to canonical intent.
INTENT_ALIAS = {
    "reduce": "REDUCE_MONOLITH",
    "parallel": "ENABLE_PARALLEL_WORK",
    "reuse": "EXTRACT_REUSABLE_LAYER",
    "tests": "REDUCE_TEST_TIME",
}

SUPPORTED_LANGUAGES = ["python"]


# ---------------------------------------------------------------------------
# Data Models
# ---------------------------------------------------------------------------

@dataclass
class Diagnosis:
    """Parsed diagnosis from step 2.

    Fields align with the step 2 prompt output contract:
    ``DIAGNOSIS_BEGIN { recommended_action, leave_alone_rationale,
    reasoning, confidence, target_file_lines, ... } DIAGNOSIS_END``.

    Legacy ``type`` / ``rationale`` aliases are kept for backward compat
    and populated from ``recommended_action`` / ``reasoning`` via __post_init__.
    """
    recommended_action: str = ""
    leave_alone_rationale: str = ""
    reasoning: str = ""
    confidence: float = 0.0
    target_file_lines: int = 0
    type: str = ""  # backward-compat alias
    rationale: str = ""  # backward-compat alias

    def __post_init__(self):
        # Populate legacy fields from new ones
        if not self.type and self.recommended_action:
            self.type = self.recommended_action
        if not self.rationale:
            self.rationale = self.reasoning or self.leave_alone_rationale


@dataclass
class ModuleInvestigation:
    test_seams: List[str] = field(default_factory=list)
    test_ownership: Dict[str, str] = field(default_factory=dict)


@dataclass
class SplitPlan:
    """Parsed SplitPlan from step 4.

    Fields align with prompt: children (list), parent_changes (dict),
    reference_updates (list), test_ownership (dict),
    surfaced_dead_candidates (list).
    """
    children: List[Dict[str, Any]] = field(default_factory=list)
    parent_changes: Dict[str, Any] = field(default_factory=dict)
    reference_updates: List[Dict[str, Any]] = field(default_factory=list)
    test_ownership: Dict[str, Any] = field(default_factory=dict)
    surfaced_dead_candidates: List[str] = field(default_factory=list)


@dataclass
class QualitativeAssessment:
    """Parsed qualitative assessment from step 7.

    Fields align with the step 7 prompt output contract:
    ``QUALITATIVE_ASSESSMENT_BEGIN { cohesion, boundary_clarity,
    change_decorrelation, overall_verdict, projection_vs_reality }``.

    ``cohesion``, ``boundary_clarity``, ``change_decorrelation`` are dicts
    with ``rating`` and ``evidence`` fields. ``overall_verdict`` drives
    the improvement gate.
    """
    overall_verdict: str = "unknown"
    cohesion: Dict[str, str] = field(default_factory=dict)
    boundary_clarity: Dict[str, str] = field(default_factory=dict)
    change_decorrelation: Dict[str, str] = field(default_factory=dict)
    projection_vs_reality: str = ""
    score: int = 0  # legacy — not produced by LLM, kept for back-compat
    rationale: str = ""  # legacy


@dataclass
class SplitOption:
    """Parsed SplitOption from step 4.

    Fields align with the step 4 prompt output:
    { name, plan, expected_improvements, qualitative_projection,
      risk, blast_radius, rationale, score }

    ``score`` may be a float OR a dict with a ``total`` key (the LLM
    sometimes returns the full scoring breakdown). ``numeric_score``
    property normalizes to a float.
    """
    plan: SplitPlan = field(default_factory=SplitPlan)
    score: Any = 0.0
    name: str = ""
    expected_improvements: Dict[str, Any] = field(default_factory=dict)
    qualitative_projection: Dict[str, Any] = field(default_factory=dict)
    risk: str = ""
    blast_radius: Any = 0
    rationale: str = ""

    @property
    def numeric_score(self) -> float:
        """Extract numeric score regardless of format."""
        if isinstance(self.score, (int, float)):
            return float(self.score)
        if isinstance(self.score, dict):
            return float(self.score.get("total", 0))
        try:
            return float(self.score)
        except (ValueError, TypeError):
            return 0.0


@dataclass
class OptionsConsidered:
    options: List[Dict[str, Any]] = field(default_factory=list)


@dataclass
class IntentDecision:
    """Parsed intent decision from step 0 (U5).

    Emitted inside INTENT_BEGIN/END markers by the step 0 LLM prompt.
    Maps to one of VALID_INTENTS; downstream step 4 uses this to
    re-weight its rubric.
    """
    intent: str = "REDUCE_MONOLITH"
    confidence: float = 0.0
    rationale: str = ""


@dataclass
class Phase:
    """One phase inside a PhaseExtractionPlan (U1)."""
    name: str = ""
    description: str = ""
    line_range: List[int] = field(default_factory=list)
    inputs: List[str] = field(default_factory=list)
    outputs: str = ""
    side_effects: List[str] = field(default_factory=list)


@dataclass
class PhaseExtractionPlan:
    """Parsed phase extraction plan from step 6a (U1).

    Emitted inside PHASE_EXTRACTION_BEGIN/END markers per child.
    When ``should_extract`` is False, the other fields are empty and
    ``reason`` is populated with a one-sentence justification.
    """
    should_extract: bool = False
    target_symbol: str = ""
    target_file: str = ""
    phases: List[Phase] = field(default_factory=list)
    parent_shell: str = ""
    rationale: str = ""
    reason: str = ""


@dataclass
class RefineCheck:
    """Parsed refine-check decision from step 9 (U6)."""
    should_refine: bool = False
    target_child_file: str = ""
    reason: str = ""
    suggested_intent: str = ""


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _get_state_dir(cwd: Path) -> Path:
    root = get_git_root(cwd) or cwd
    return root / ".pdd" / "split-state"


def _stable_split_id(target_path: str) -> int:
    """Deterministic ID from repo-relative target path (stable across Python runs)."""
    h = 0
    for ch in target_path:
        h = (h * 31 + ord(ch)) & 0xFFFFFFFF
    return h % 100000


_MARKER_BLOCK_RE = re.compile(
    r"(?P<name>[A-Z_]+)_BEGIN\s*\n?(?P<body>.*?)\n?\s*(?P=name)_END",
    re.DOTALL,
)


def _extract_json_candidates(output: str) -> List[str]:
    """Extract all top-level JSON values (objects and arrays) from a string."""
    candidates: List[str] = []
    depth = 0
    start = -1
    open_char = None
    close_char = None
    in_string = False
    escape = False
    for i, ch in enumerate(output):
        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"' and depth > 0:
            in_string = True
            continue
        if depth == 0 and ch in "{[":
            open_char = ch
            close_char = "}" if ch == "{" else "]"
            start = i
            depth = 1
        elif depth > 0:
            if ch == open_char:
                depth += 1
            elif ch == close_char:
                depth -= 1
                if depth == 0 and start >= 0:
                    candidates.append(output[start:i + 1])
                    start = -1
                    open_char = None
                    close_char = None
    return candidates


def _parse_step_output(output: str, dataclass_type: type) -> Any:
    """Parse agent output JSON into a dataclass. Returns None on failure.

    Strategy:
    1. If the output contains ``NAME_BEGIN ... NAME_END`` marker blocks,
       parse JSON from within those blocks first (per the prompt contracts).
    2. Otherwise, collect all top-level ``{...}`` and ``[...]`` blocks and
       try the largest first.

    ``OptionsConsidered`` is a special case: the prompt emits a JSON *array*
    (``OPTIONS_BEGIN [...] OPTIONS_END``), which this function wraps as
    ``{"options": [...]}`` before dataclass conversion.
    """
    candidates: List[str] = []
    # Prefer marker-block JSON
    for match in _MARKER_BLOCK_RE.finditer(output):
        body = match.group("body").strip()
        # Strip markdown code fences if present
        if body.startswith("```"):
            lines = body.splitlines()
            if lines and lines[0].startswith("```"):
                lines = lines[1:]
            if lines and lines[-1].startswith("```"):
                lines = lines[:-1]
            body = "\n".join(lines).strip()
        candidates.append(body)

    # Also collect top-level JSON objects/arrays as fallback
    candidates.extend(_extract_json_candidates(output))

    # Try candidates from largest to smallest
    for candidate in sorted(candidates, key=len, reverse=True):
        try:
            data = json.loads(candidate)
        except json.JSONDecodeError:
            continue
        try:
            # Special case: OptionsConsidered from a bare JSON array
            if dataclass_type is OptionsConsidered and isinstance(data, list):
                data = {"options": data}
            result = _dict_to_dataclass(dataclass_type, data)
            if result is not None:
                return result
        except (TypeError, KeyError):
            continue
    return None


_NESTED_FIELD_TYPES: Dict[Tuple[type, str], type] = {
    (SplitOption, "plan"): SplitPlan,
}

_NESTED_LIST_TYPES: Dict[Tuple[type, str], type] = {
    (OptionsConsidered, "options"): SplitOption,
    (PhaseExtractionPlan, "phases"): Phase,
}


def _dict_to_dataclass(cls: type, data: Any) -> Any:
    """Recursively convert a dict to a dataclass, handling nested types."""
    if not isinstance(data, dict):
        return data
    valid_fields = {f.name for f in cls.__dataclass_fields__.values()}
    filtered = {}
    for k, v in data.items():
        if k not in valid_fields:
            continue
        nested_cls = _NESTED_FIELD_TYPES.get((cls, k))
        if nested_cls and isinstance(v, dict):
            filtered[k] = _dict_to_dataclass(nested_cls, v)
            continue
        list_cls = _NESTED_LIST_TYPES.get((cls, k))
        if list_cls and isinstance(v, list):
            filtered[k] = [
                _dict_to_dataclass(list_cls, item) if isinstance(item, dict) else item
                for item in v
            ]
            continue
        filtered[k] = v
    return cls(**filtered)


def _check_hard_stop(step: str, output: str, force_split: bool) -> Optional[str]:
    """Check for hard stop markers in agent output.

    Markers must appear at the start of a trimmed line to avoid false
    positives from the agent mentioning a marker in prose (e.g.
    "I checked for ARCHITECTURE_STALE but it was fine").
    """
    markers = {
        "1_survey": ["ARCHITECTURE_STALE"],
        "2_diagnose": [] if force_split else ["DIAGNOSIS: LEAVE_ALONE"],
        "3_investigate": ["ARCHITECTURE_STALE", "NO_TEST_FILE"],
        "4_propose_options": ["NO_IMPROVEMENT_POSSIBLE"],
        "6_extract": ["EXTRACTION_BLOCKED"],
        "7a_verify_local": ["ARCHITECTURAL_REGRESSION"],
        "7b_regen_gate": ["REGEN_FAILED"],
        "8_repair": ["REPAIR_EXHAUSTED"],
    }
    for marker in markers.get(step, []):
        for line in output.splitlines():
            # Strip markdown formatting (**, *, `, #) before checking
            cleaned = line.strip().strip("*`#").strip()
            if cleaned.upper().startswith(marker.upper()):
                return marker
    return None


def _verdict_strength(verdict: str) -> str:
    """Map LLM overall_verdict to strength category."""
    v = verdict.lower().strip()
    if v == "clear_improvement":
        return "strong"
    if v in ("marginal", "moderate"):
        return "moderate"
    return "weak"


def _apply_improvement_gate(
    quant_metrics: Dict[str, float],
    qual_assess: QualitativeAssessment,
) -> str:
    """Apply the quantitative + qualitative decision matrix.

    Uses ``qual_assess.overall_verdict`` (the string produced by the step 7
    assess LLM prompt) instead of a numeric score.  The verdict maps to
    strength categories: ``"clear_improvement"`` → strong,
    ``"marginal"`` → moderate, everything else → weak.
    """
    strength = _verdict_strength(qual_assess.overall_verdict)
    is_strong = strength == "strong"
    is_moderate = strength == "moderate"

    if not quant_metrics:
        # No quantitative data — defer to qualitative
        if is_strong:
            return "HUMAN_REVIEW_REQUIRED"
        if is_moderate:
            return "HUMAN_REVIEW_REQUIRED_MARGINAL"
        return "ABORT_NO_IMPROVEMENT"

    improves = sum(1 for v in quant_metrics.values() if v > 0)
    regresses = sum(1 for v in quant_metrics.values() if v < 0)

    if improves >= 1 and regresses == 0:
        return "AUTO_SHIP" if (is_strong or is_moderate) else "AUTO_SHIP_WARNING"
    if regresses > 0:
        return "HUMAN_REVIEW_REQUIRED" if is_strong else "ABORT_REGRESSION"
    # Flat metrics
    if is_strong:
        return "HUMAN_REVIEW_REQUIRED"
    return "ABORT_NO_IMPROVEMENT"


def _detect_language(target_file: str) -> str:
    """Detect language from file extension using pdd's get_language."""
    ext = Path(target_file).suffix
    lang = get_language(ext) if ext else ""
    return lang.lower() if lang else ""


def _find_architecture_json(target_file: str, cwd: Path) -> Optional[Path]:
    """Walk up from target file's directory looking for architecture.json.

    OPTIONAL signal only. Returns None when not found — step 1's prompt
    treats absence as "zero information", so this helper never raises.
    """
    target_abs = (
        Path(target_file)
        if Path(target_file).is_absolute()
        else cwd / target_file
    )
    candidate = target_abs.parent
    for _ in range(8):
        maybe = candidate / "architecture.json"
        if maybe.is_file():
            return maybe
        if candidate.parent == candidate:
            break
        candidate = candidate.parent
    return None


def _normalize_intent(raw: Optional[str]) -> Optional[str]:
    """Map CLI short forms or free text to a canonical intent.

    Returns None if the input is empty/unparseable — step 0 then runs
    to infer the intent from the target file.
    """
    if not raw:
        return None
    v = raw.strip()
    # Short form
    if v.lower() in INTENT_ALIAS:
        return INTENT_ALIAS[v.lower()]
    # Canonical form
    v_upper = v.upper().replace(" ", "_")
    if v_upper in VALID_INTENTS:
        return v_upper
    return None


# ---------------------------------------------------------------------------
# Main orchestrator
# ---------------------------------------------------------------------------

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
    if not quiet:
        console.print(f"Splitting {target_file}...")

    # Language detection
    lang = _detect_language(target_file)
    if lang not in SUPPORTED_LANGUAGES and not experimental_language:
        return (
            False,
            f"Language not supported: {lang or 'unknown'}. Use --experimental-language.",
            0.0, "", [],
        )

    # Load persisted state. Use a stable ID derived from the repo-relative
    # path so files with the same basename in different directories don't
    # collide on the same state file or worktree/branch name.
    state_dir = _get_state_dir(cwd)
    _git_root_for_id = get_git_root(cwd)
    _target_resolved = Path(target_file).resolve()
    try:
        _id_path = (
            str(_target_resolved.relative_to(_git_root_for_id))
            if _git_root_for_id
            else target_file
        )
    except ValueError:
        _id_path = target_file
    split_id = _stable_split_id(_id_path)
    state, github_comment_id = load_workflow_state(
        cwd, split_id, "split", state_dir, "", "", use_github_state
    )
    if state is None:
        state = {
            "step_outputs": {},
            "last_completed_step": None,
            "total_cost": 0.0,
            "model_used": "",
            "changed_files": [],
            "children_extracted": [],
            "phase_plans": [],
            "intent": _normalize_intent(intent) or "",
            "iteration_count": 0,
        }
        github_comment_id = None

    last_completed = state.get("last_completed_step")
    total_cost = state.get("total_cost", 0.0)
    model_used = state.get("model_used", "")
    changed_files: List[str] = state.get("changed_files", [])
    verify_failures: List[str] = state.get("verify_failures", [])
    quant_metrics: Dict[str, float] = state.get("quant_metrics", {})
    phase_plans: List[Dict[str, Any]] = state.get("phase_plans", [])
    # Intent may arrive from CLI (user flag) or get inferred by step 0.
    # Precedence: user_intent_hint (CLI) > step 0 inference > default.
    current_intent: str = state.get("intent", "") or (_normalize_intent(intent) or "")
    iteration_count: int = int(state.get("iteration_count", 0))

    # Graceful shutdown: save state on Ctrl-C / SIGTERM so users don't
    # lose progress. Installed AFTER all variables are defined (a signal
    # between install and definition would crash with NameError).
    def _handle_interrupt(signum: int, frame: Any) -> None:
        if not quiet:
            cur_step = state.get("last_completed_step", last_completed)
            console.print(
                "\n[yellow]Interrupted — saving progress. "
                f"Spent ${total_cost:.2f} so far. "
                f"Re-run to resume from step after '{cur_step}'.[/yellow]"
            )
        state["total_cost"] = total_cost
        state["model_used"] = model_used
        state["changed_files"] = changed_files
        save_workflow_state(
            cwd, split_id, "split", state, state_dir,
            "", "", use_github_state, github_comment_id,
        )
        clear_agentic_progress()
        raise SystemExit(130)  # standard exit code for SIGINT

    prev_sigint = signal.signal(signal.SIGINT, _handle_interrupt)
    prev_sigterm = signal.signal(signal.SIGTERM, _handle_interrupt)

    # Tell users when resuming so they know they aren't paying twice.
    if last_completed is not None and not quiet:
        console.print(
            f"[cyan]Resuming from saved state — "
            f"last completed: {last_completed}, "
            f"cost so far: ${total_cost:.2f}[/cyan]"
        )

    # Restore signal handlers on any exit path. Called explicitly before
    # every early return and in the final return. This avoids re-indenting
    # 1,400 lines of pipeline code into a try/finally block.
    def _restore_signals() -> None:
        signal.signal(signal.SIGINT, prev_sigint)
        signal.signal(signal.SIGTERM, prev_sigterm)

    # Capture original line count for quantitative metrics
    original_line_count = 0
    try:
        original_line_count = len(Path(target_file).read_text().splitlines())
    except OSError:
        pass

    # Optional architecture.json lookup — used by step 1 as a boost signal.
    arch_json_path = _find_architecture_json(target_file, cwd)
    architecture_json_excerpt = ""
    if arch_json_path is not None:
        try:
            text = arch_json_path.read_text(encoding="utf-8")
            # Truncate to a sane size — the agent re-reads the full file
            # if it wants more; this is just a hint.
            architecture_json_excerpt = text[:4000]
        except OSError:
            architecture_json_excerpt = ""

    context: Dict[str, Any] = {
        "target_file": target_file,
        "language": lang,
        "cwd": str(cwd),
        "delete_dead": delete_dead,
        "force_split": force_split,
        "no_verify": no_verify,
        "skip_regen_gate": skip_regen_gate,
        "original_line_count": original_line_count,
        "user_intent_hint": _normalize_intent(intent) or "",
        "intent": current_intent,
        "no_phase_extraction": no_phase_extraction,
        "iteration_count": iteration_count,
        "architecture_json_present": arch_json_path is not None,
        "architecture_json_excerpt": architecture_json_excerpt,
        "phase_plan": "",  # Filled per-child during step 6.
        "changed_files": "",  # Filled just before step 9.
    }
    # Restore context from prior step outputs
    for key, value in state.get("step_outputs", {}).items():
        context[f"step{key}_output"] = value

    ordered_steps = [
        "0_intent",
        "1_survey", "2_diagnose", "3_investigate", "4_propose_options",
        "5_setup_worktree",
        "6a_phase_extract",
        "6_extract",
        "7a_verify_local", "7b_regen_gate", "7c_arch_sync", "7_assess",
        "8_repair",
        "9_refine_check",
    ]

    # Resume from last completed step
    start_idx = 0
    if last_completed is not None:
        try:
            start_idx = ordered_steps.index(last_completed) + 1
        except ValueError:
            # Step name in saved state doesn't match current pipeline
            # (likely renamed in a code update). Warn — this causes a
            # full pipeline rerun ($30-80).
            if not quiet:
                console.print(
                    f"[yellow]Warning: saved last_completed_step "
                    f"'{last_completed}' not in current pipeline — "
                    f"restarting from step 1[/yellow]"
                )
            start_idx = 0

    current_work_dir = cwd
    worktree_path_str = state.get("worktree_path")
    if worktree_path_str:
        wt = Path(worktree_path_str)
        if wt.is_dir():
            current_work_dir = wt
        elif not quiet:
            console.print(f"[yellow]Warning: saved worktree {wt} no longer exists, using cwd[/yellow]")

    # Parsed objects — reconstructed from saved step outputs on resume
    selected_option: Optional[SplitOption] = None
    qual_assess: Optional[QualitativeAssessment] = None

    if start_idx > 0:
        step4_raw = state.get("step_outputs", {}).get("4", "")
        if step4_raw:
            parsed_opts = _parse_step_output(step4_raw, OptionsConsidered)
            if isinstance(parsed_opts, OptionsConsidered) and parsed_opts.options:
                rebuilt = []
                for o in parsed_opts.options:
                    if isinstance(o, SplitOption):
                        rebuilt.append(o)
                    elif isinstance(o, dict):
                        rebuilt.append(_dict_to_dataclass(SplitOption, o))
                if rebuilt:
                    selected_option = max(rebuilt, key=lambda o: o.numeric_score)

        step7_raw = state.get("step_outputs", {}).get("7", "")
        if step7_raw:
            parsed_qa = _parse_step_output(step7_raw, QualitativeAssessment)
            if isinstance(parsed_qa, QualitativeAssessment):
                qual_assess = parsed_qa

    for step in ordered_steps[start_idx:]:
        # Skip step 0 when intent is already set (CLI flag or previous
        # run). Saves ~$0.20 + 200s of LLM time.
        if step == "0_intent" and current_intent:
            state["step_outputs"]["0"] = f"Skipped — intent already set: {current_intent}"
            context["step0_output"] = state["step_outputs"]["0"]
            continue

        step_num = step.split("_")[0]
        step_index = ordered_steps.index(step) + 1
        if not quiet:
            console.print(f"[bold][Step {step_index}/{len(ordered_steps)}][/bold] {step}...")
        set_agentic_progress("split", step_index, len(ordered_steps), step)

        # ── LLM steps ──────────────────────────────────────────────
        if step in (
            "0_intent", "1_survey", "2_diagnose", "3_investigate",
            "4_propose_options", "7_assess", "9_refine_check",
        ):
            # Pre-step context enrichment
            if step == "7_assess":
                context["quantitative_metrics"] = str(quant_metrics)
                context["post_split_state"] = (
                    f"verify_failures={len(verify_failures)}, "
                    f"changed_files={len(changed_files)}"
                )
            if step == "9_refine_check":
                context["quantitative_metrics"] = str(quant_metrics)
                context["changed_files"] = ", ".join(changed_files)
                context["iteration_count"] = iteration_count
            if step == "4_propose_options":
                # Make intent available to step 4's rubric.
                context["intent"] = current_intent or "REDUCE_MONOLITH"

            name = "_".join(step.split("_")[1:])
            template_name = f"agentic_split_step{step_num}_{name}_LLM"
            prompt_template = load_prompt_template(template_name)
            if not prompt_template:
                clear_agentic_progress()
                _restore_signals()
                return False, f"Missing template: {template_name}", total_cost, model_used, changed_files

            processed = preprocess(
                prompt_template, recursive=True,
                double_curly_brackets=True, exclude_keys=list(context.keys()),
            )
            formatted_prompt = substitute_template_variables(processed, context)

            timeout = SPLIT_STEP_TIMEOUTS.get(step, 340.0) + timeout_adder
            success, output, step_cost, step_model = run_agentic_task(
                instruction=formatted_prompt,
                cwd=current_work_dir,
                verbose=verbose, quiet=quiet,
                timeout=timeout, label=step,
                max_retries=DEFAULT_MAX_RETRIES,
            )
            total_cost += step_cost
            model_used = step_model

            if not success:
                if not quiet:
                    console.print(f"[yellow]Warning: step {step} agent task failed[/yellow]")
                # Still check for hard stops in partial output, then abort
                stop_reason = _check_hard_stop(step, output, force_split)
                state["total_cost"] = total_cost
                github_comment_id = save_workflow_state(
                    cwd, split_id, "split", state, state_dir, "", "", use_github_state, github_comment_id
                )
                clear_agentic_progress()
                _restore_signals()
                reason = stop_reason or f"Step {step} failed"
                return False, f"Stopped: {reason}", total_cost, model_used, changed_files

            stop_reason = _check_hard_stop(step, output, force_split)
            if stop_reason:
                state["total_cost"] = total_cost
                github_comment_id = save_workflow_state(
                    cwd, split_id, "split", state, state_dir, "", "", use_github_state, github_comment_id
                )
                clear_agentic_progress()
                _restore_signals()
                return False, f"Stopped: {stop_reason}", total_cost, model_used, changed_files

            state["step_outputs"][step_num] = output
            context[f"step{step_num}_output"] = output

            # Step-specific parsing
            if step == "0_intent":
                parsed_intent = _parse_step_output(output, IntentDecision)
                if isinstance(parsed_intent, IntentDecision):
                    # CLI intent wins; step 0 only fills in the blank.
                    if not current_intent:
                        normalized = _normalize_intent(parsed_intent.intent)
                        current_intent = normalized or "REDUCE_MONOLITH"
                    state["intent"] = current_intent
                    context["intent"] = current_intent
                    if not quiet:
                        console.print(
                            f"Intent: {current_intent} "
                            f"(conf={parsed_intent.confidence:.2f})"
                        )
                else:
                    # Parsing failed — default to REDUCE_MONOLITH.
                    if not current_intent:
                        current_intent = "REDUCE_MONOLITH"
                        state["intent"] = current_intent
                        context["intent"] = current_intent
                    if not quiet:
                        console.print(
                            "[yellow]Warning: could not parse intent — "
                            "defaulting to REDUCE_MONOLITH[/yellow]"
                        )
            elif step == "2_diagnose":
                parsed = _parse_step_output(output, Diagnosis)
                if isinstance(parsed, Diagnosis):
                    if not quiet:
                        console.print(f"Diagnosis: {parsed.type} — {parsed.rationale}")
                    # Check LEAVE_ALONE from parsed JSON (the text-marker
                    # check in _check_hard_stop may miss JSON-only output)
                    is_leave_alone = (
                        parsed.recommended_action.upper().replace(" ", "_") == "LEAVE_ALONE"
                        or parsed.type.upper().replace(" ", "_") == "LEAVE_ALONE"
                    )
                    if is_leave_alone and not force_split:
                        state["last_completed_step"] = step
                        state["total_cost"] = total_cost
                        state["model_used"] = model_used
                        github_comment_id = save_workflow_state(
                            cwd, split_id, "split", state, state_dir,
                            "", "", use_github_state, github_comment_id,
                        )
                        clear_agentic_progress()
                        _restore_signals()
                        return False, f"Stopped: LEAVE_ALONE — {parsed.rationale}", total_cost, model_used, []
                    if diagnose_only:
                        state["last_completed_step"] = step
                        state["total_cost"] = total_cost
                        state["model_used"] = model_used
                        github_comment_id = save_workflow_state(
                            cwd, split_id, "split", state, state_dir,
                            "", "", use_github_state, github_comment_id,
                        )
                        clear_agentic_progress()
                        _restore_signals()
                        return False, f"Diagnosis: {parsed.type} — {parsed.rationale}", total_cost, model_used, []
                else:
                    if not quiet:
                        console.print("[yellow]Warning: could not parse diagnosis from agent output[/yellow]")
                    if diagnose_only:
                        state["last_completed_step"] = step
                        state["total_cost"] = total_cost
                        state["model_used"] = model_used
                        github_comment_id = save_workflow_state(
                            cwd, split_id, "split", state, state_dir,
                            "", "", use_github_state, github_comment_id,
                        )
                        clear_agentic_progress()
                        _restore_signals()
                        return False, f"Diagnosis (raw): {output[:200]}", total_cost, model_used, []

            elif step == "4_propose_options":
                # Helper: locate shared_layer_children in a parsed option.
                def _shared_layer_children_of(
                    opt: "SplitOption",
                    raw_opt: Any,
                ) -> list:
                    slc = []
                    pc = opt.plan.parent_changes
                    if isinstance(pc, dict):
                        slc = pc.get("shared_layer_children", []) or []
                    if not slc:
                        slc = getattr(
                            opt.plan, "shared_layer_children", []
                        ) or []
                    if not slc and isinstance(raw_opt, dict):
                        plan_d = raw_opt.get("plan", {})
                        if isinstance(plan_d, dict):
                            slc = plan_d.get("shared_layer_children", []) or []
                    return slc

                # Does step 3 demand a shared layer?
                step3_raw = state.get("step_outputs", {}).get("3", "")
                shared_layer_required = (
                    step3_raw
                    and "shared_layer_candidates" in step3_raw
                    and '"shared_layer_candidates": []' not in step3_raw
                )

                # Retry loop: if shared-layer is required but dropped,
                # re-invoke step 4 with a corrective instruction. This
                # converts the prior "soft warning" into a HARD gate.
                step4_retry = 0
                max_step4_retries = 2
                while True:
                    parsed_options = _parse_step_output(output, OptionsConsidered)
                    if (
                        not isinstance(parsed_options, OptionsConsidered)
                        or not parsed_options.options
                    ):
                        if not quiet:
                            console.print(
                                "[yellow]Warning: could not parse options "
                                "from agent output[/yellow]"
                            )
                        break

                    # Build SplitOption objects from dicts
                    options = []
                    for o in parsed_options.options:
                        if isinstance(o, SplitOption):
                            options.append(o)
                        elif isinstance(o, dict):
                            options.append(_dict_to_dataclass(SplitOption, o))
                    if not options:
                        if not quiet:
                            console.print(
                                "[yellow]Warning: no valid options parsed[/yellow]"
                            )
                        break

                    selected_option = max(options, key=lambda o: o.numeric_score)
                    selected_idx = options.index(selected_option)
                    raw_option = (
                        parsed_options.options[selected_idx]
                        if selected_idx < len(parsed_options.options)
                        else {}
                    )

                    # Shared-layer hard gate
                    if shared_layer_required:
                        slc = _shared_layer_children_of(selected_option, raw_option)
                        if not slc and step4_retry < max_step4_retries:
                            step4_retry += 1
                            if not quiet:
                                console.print(
                                    f"[yellow]Step 4 retry {step4_retry}/"
                                    f"{max_step4_retries}: selected option has no "
                                    f"shared_layer_children despite step 3 "
                                    f"surfacing candidates. Re-invoking step 4 "
                                    f"with corrective instruction.[/yellow]"
                                )
                            # Augment the context with a retry reason, then
                            # re-run step 4 with the same prompt template.
                            context["step4_retry_reason"] = (
                                "Your previous output's selected option had "
                                "no shared_layer_children, but step 3 "
                                "surfaced non-empty shared_layer_candidates. "
                                "Every valid option MUST include a "
                                "shared_layer_children list that extracts the "
                                "cross-worker duplication step 3 identified. "
                                "Produce a corrected options set."
                            )
                            retry_prompt = substitute_template_variables(
                                preprocess(
                                    prompt_template, recursive=True,
                                    double_curly_brackets=True,
                                    exclude_keys=list(context.keys()),
                                ),
                                context,
                            )
                            retry_prompt += (
                                "\n\n% RETRY NOTICE — shared_layer_children required\n"
                                f"{context['step4_retry_reason']}"
                            )
                            r_success, r_output, r_cost, r_model = run_agentic_task(
                                instruction=retry_prompt,
                                cwd=current_work_dir,
                                verbose=verbose, quiet=quiet,
                                timeout=SPLIT_STEP_TIMEOUTS.get(
                                    "4_propose_options", 900.0
                                ) + timeout_adder,
                                label=f"4_propose_options_retry_{step4_retry}",
                                max_retries=DEFAULT_MAX_RETRIES,
                            )
                            total_cost += r_cost
                            model_used = r_model
                            if r_success:
                                output = r_output
                                state["step_outputs"]["4"] = output
                                context["step4_output"] = output
                                continue  # reparse with new output
                            # Retry failed — loop again so the retry counter
                            # check at line top triggers the next attempt or
                            # the >= max_step4_retries branch records failure.
                            continue
                        elif not slc and step4_retry >= max_step4_retries:
                            # After retries, still missing. Record as a hard
                            # verify_failure so the improvement gate sees it.
                            verify_failures.append(
                                "shared_layer_candidates_dropped: step 4 did "
                                "not include shared_layer_children after "
                                f"{max_step4_retries} retries. Step 3 "
                                "surfaced cross-worker duplication that "
                                "should have been extracted."
                            )

                    # All good — render table, commit selection, exit loop
                    table = Table(title="Split Options")
                    table.add_column("Option")
                    table.add_column("Score")
                    for i, opt in enumerate(options, 1):
                        table.add_row(str(i), str(opt.numeric_score))
                    if not quiet:
                        console.print(table)
                    break
                if propose_only:
                    # Persist step 4 output so a subsequent full run resumes
                    # from step 5 without re-running propose.
                    state["last_completed_step"] = step
                    state["total_cost"] = total_cost
                    state["model_used"] = model_used
                    github_comment_id = save_workflow_state(
                        cwd, split_id, "split", state, state_dir,
                        "", "", use_github_state, github_comment_id,
                    )
                    clear_agentic_progress()
                    _restore_signals()
                    return False, "Propose only complete", total_cost, model_used, []

            elif step == "7_assess":
                parsed_qa = _parse_step_output(output, QualitativeAssessment)
                if isinstance(parsed_qa, QualitativeAssessment):
                    qual_assess = parsed_qa
                else:
                    # Fallback: if the pipeline got through extraction and
                    # verification (steps 1-7a) but the assess LLM didn't
                    # produce parseable output, default to moderate rather
                    # than unknown. Reaching this point means the split was
                    # structurally valid — aborting due to a parse failure
                    # in the assessment step would discard good work.
                    if not quiet:
                        console.print(
                            "[yellow]Warning: could not parse qualitative "
                            "assessment — defaulting to moderate[/yellow]"
                        )
                    qual_assess = QualitativeAssessment(
                        overall_verdict="moderate",
                        rationale="Defaulted: assessment output unparseable but split passed verification",
                    )

            elif step == "9_refine_check":
                parsed_refine = _parse_step_output(output, RefineCheck)
                if isinstance(parsed_refine, RefineCheck):
                    # Guard against runaway: enforce the iteration cap
                    # in Python even if the agent missed it.
                    if (parsed_refine.should_refine
                            and iteration_count < MAX_REFINEMENT_ITERATIONS):
                        state["_pending_refine"] = {
                            "target_child_file": parsed_refine.target_child_file,
                            "reason": parsed_refine.reason,
                            "suggested_intent": parsed_refine.suggested_intent,
                        }
                        if not quiet:
                            console.print(
                                f"[cyan]Refine suggested on "
                                f"{parsed_refine.target_child_file}: "
                                f"{parsed_refine.reason}[/cyan]"
                            )
                    else:
                        state["_pending_refine"] = None
                        if not quiet:
                            console.print(
                                f"Refine check: ship as-is "
                                f"({parsed_refine.reason})"
                            )

        # ── Phase extraction (per-child, fan-out) ──────────────────
        elif step == "6a_phase_extract":
            if selected_option is None:
                # Can't run phase extraction without a plan.
                state["step_outputs"]["6a"] = "Skipped — no selected_option"
                context["step6a_output"] = state["step_outputs"]["6a"]
                # Persist and continue to next step.
            elif no_phase_extraction:
                if not quiet:
                    console.print(
                        "[yellow]Skipping phase extraction (flag)[/yellow]"
                    )
                state["step_outputs"]["6a"] = "Skipped — no_phase_extraction flag"
                context["step6a_output"] = state["step_outputs"]["6a"]
                phase_plans = [None] * len(selected_option.plan.children)
                state["phase_plans"] = phase_plans
            else:
                total_children = len(selected_option.plan.children)
                if len(phase_plans) < total_children:
                    # Pad with None — these are children we haven't
                    # analyzed yet.
                    phase_plans = (
                        phase_plans
                        + [None] * (total_children - len(phase_plans))
                    )
                for i in range(total_children):
                    if phase_plans[i] is not None:
                        continue  # already analyzed, resume
                    child = selected_option.plan.children[i]
                    child_name = (
                        child.get("name", f"child_{i+1}")
                        if isinstance(child, dict) else str(child)
                    )
                    if not quiet:
                        console.print(
                            f"Phase-extract analysis {i+1}/{total_children}: "
                            f"{child_name}..."
                        )
                    context["current_child_index"] = i + 1
                    context["current_child"] = json.dumps(
                        child, default=str
                    ) if isinstance(child, dict) else str(child)
                    context["selected_option"] = json.dumps({
                        "name": selected_option.name,
                        "plan": {
                            "children": selected_option.plan.children,
                        },
                    }, default=str)
                    context["children_extracted"] = "[]"  # Not yet extracted

                    template_name = "agentic_split_step6a_phase_extract_LLM"
                    p_template = load_prompt_template(template_name)
                    if not p_template:
                        if not quiet:
                            console.print(
                                f"[yellow]Missing template: {template_name}, "
                                "skipping phase extraction[/yellow]"
                            )
                        phase_plans[i] = {"should_extract": False,
                                          "reason": "template missing"}
                        continue
                    processed = preprocess(
                        p_template, recursive=True,
                        double_curly_brackets=True,
                        exclude_keys=list(context.keys()),
                    )
                    formatted_prompt = substitute_template_variables(
                        processed, context
                    )
                    pe_success, pe_output, pe_cost, pe_model = run_agentic_task(
                        instruction=formatted_prompt,
                        cwd=current_work_dir,
                        verbose=verbose, quiet=quiet,
                        timeout=SPLIT_STEP_TIMEOUTS["6a_phase_extract"] + timeout_adder,
                        label=f"6a_phase_extract_child_{i+1}",
                        max_retries=DEFAULT_MAX_RETRIES,
                    )
                    total_cost += pe_cost
                    model_used = pe_model
                    parsed_pe = _parse_step_output(pe_output, PhaseExtractionPlan)
                    if isinstance(parsed_pe, PhaseExtractionPlan):
                        # Serialize as dict for state persistence (JSON-safe).
                        phase_plans[i] = {
                            "should_extract": parsed_pe.should_extract,
                            "target_symbol": parsed_pe.target_symbol,
                            "target_file": parsed_pe.target_file,
                            "phases": [
                                {
                                    "name": p.name,
                                    "description": p.description,
                                    "line_range": p.line_range,
                                    "inputs": p.inputs,
                                    "outputs": p.outputs,
                                    "side_effects": p.side_effects,
                                }
                                for p in parsed_pe.phases
                            ],
                            "parent_shell": parsed_pe.parent_shell,
                            "rationale": parsed_pe.rationale,
                            "reason": parsed_pe.reason,
                        }
                    else:
                        # Parse failed — treat as no-extract
                        phase_plans[i] = {
                            "should_extract": False,
                            "reason": "output unparseable",
                        }
                    state["phase_plans"] = phase_plans
                    state["total_cost"] = total_cost
                    github_comment_id = save_workflow_state(
                        cwd, split_id, "split", state, state_dir,
                        "", "", use_github_state, github_comment_id,
                    )
                state["step_outputs"]["6a"] = (
                    f"Phase plans: "
                    f"{sum(1 for p in phase_plans if p and p.get('should_extract'))}"
                    f"/{total_children} children flagged for extraction"
                )
                context["step6a_output"] = state["step_outputs"]["6a"]

        # ── Extraction (fan-out) ───────────────────────────────────
        elif step == "6_extract":
            if selected_option is None:
                clear_agentic_progress()
                _restore_signals()
                return False, "No selected option — step 4 may have failed", total_cost, model_used, changed_files
            total_children = len(selected_option.plan.children)
            children_extracted = state.get("children_extracted", [])
            for i in range(len(children_extracted), total_children):
                child = selected_option.plan.children[i]
                child_name = child.get("name", f"child_{i+1}") if isinstance(child, dict) else str(child)
                if not quiet:
                    console.print(f"Extracting child {i+1}/{total_children}: {child_name}...")
                context["current_child_index"] = i + 1
                context["current_child"] = child
                context["delete_dead_this_child"] = (i + 1 == total_children and delete_dead)
                # Expose the full selected_option and children_extracted lists
                # so the step 6 prompt's template placeholders resolve.
                context["selected_option"] = json.dumps({
                    "name": selected_option.name,
                    "plan": {
                        "children": selected_option.plan.children,
                        "parent_changes": selected_option.plan.parent_changes,
                        "reference_updates": selected_option.plan.reference_updates,
                        "test_ownership": selected_option.plan.test_ownership,
                    },
                    "score": selected_option.numeric_score,
                    "risk": selected_option.risk,
                    "rationale": selected_option.rationale,
                }, default=str)
                context["children_extracted"] = json.dumps(children_extracted, default=str)

                # Attach per-child phase plan (from step 6a). Empty string
                # when no plan / no-extract — the step 6 prompt treats
                # empty as "skip phase extraction".
                if i < len(phase_plans) and phase_plans[i]:
                    context["phase_plan"] = json.dumps(phase_plans[i], default=str)
                else:
                    context["phase_plan"] = ""

                template_name = "agentic_split_step6_extract_LLM"
                prompt_template = load_prompt_template(template_name)
                if not prompt_template:
                    clear_agentic_progress()
                    _restore_signals()
                    return False, f"Missing template: {template_name}", total_cost, model_used, changed_files
                processed = preprocess(
                    prompt_template, recursive=True,
                    double_curly_brackets=True, exclude_keys=list(context.keys()),
                )
                formatted_prompt = substitute_template_variables(processed, context)
                success, output, step_cost, step_model = run_agentic_task(
                    instruction=formatted_prompt,
                    cwd=current_work_dir,
                    verbose=verbose, quiet=quiet,
                    timeout=SPLIT_STEP_TIMEOUTS["6_extract"] + timeout_adder,
                    label=f"6_extract_child_{i+1}",
                    max_retries=DEFAULT_MAX_RETRIES,
                )
                total_cost += step_cost
                model_used = step_model

                # Always check for hard-stop markers (agent may return success=True
                # with EXTRACTION_BLOCKED embedded in output).
                stop_reason = _check_hard_stop("6_extract", output, force_split)
                if stop_reason:
                    if not quiet:
                        console.print(f"[red]Extraction blocked for child {i+1}: {stop_reason}[/red]")
                    state["children_extracted"] = children_extracted
                    state["changed_files"] = changed_files
                    state["total_cost"] = total_cost
                    github_comment_id = save_workflow_state(
                        cwd, split_id, "split", state, state_dir, "", "", use_github_state, github_comment_id,
                    )
                    clear_agentic_progress()
                    _restore_signals()
                    return False, f"Stopped: {stop_reason}", total_cost, model_used, changed_files

                if not success:
                    if not quiet:
                        console.print(f"[yellow]Warning: extraction failed for child {i+1}[/yellow]")

                # Parse FILES_CREATED / FILES_MODIFIED markers from agent output.
                # Do NOT add to changed_files yet — wait until we verify the
                # files actually exist on disk (Bug #4: phantom files).
                claimed_created: List[str] = []
                claimed_modified: List[str] = []
                for marker, bucket in (("FILES_CREATED:", claimed_created),
                                        ("FILES_MODIFIED:", claimed_modified)):
                    match = re.search(
                        rf"{marker}\s*([\s\S]+?)(?:\n\s*\n|\n[A-Z_]+:|$)",
                        output,
                    )
                    if match:
                        files_list = [
                            f.strip().strip(",").strip("`").strip()
                            for f in match.group(1).split(",")
                        ]
                        for f in files_list:
                            if f:
                                bucket.append(f)

                # VERIFY: agent often claims file creation via FILES_CREATED
                # marker without actually using Write/Edit tools. Check the
                # filesystem and retry if any claimed-created file is missing.
                missing = [
                    f for f in claimed_created
                    if not (current_work_dir / f).exists()
                ]
                retry_count = 0
                max_extract_retries = 2
                while missing and retry_count < max_extract_retries:
                    retry_count += 1
                    if not quiet:
                        console.print(
                            f"[yellow]Child {i+1} claimed {len(claimed_created)} files "
                            f"but {len(missing)} missing. Retry {retry_count}/{max_extract_retries}...[/yellow]"
                        )
                    context["missing_files"] = ", ".join(missing)
                    context["retry_reason"] = (
                        f"The agent claimed FILES_CREATED but these files "
                        f"do not exist on disk: {missing}. "
                        f"The agent MUST actually write every file using the Write tool."
                    )
                    retry_prompt_template = load_prompt_template(template_name)
                    if retry_prompt_template is None:
                        if not quiet:
                            console.print(
                                f"[red]Retry: could not load template "
                                f"{template_name}[/red]"
                            )
                        break
                    processed_retry = preprocess(
                        retry_prompt_template, recursive=True,
                        double_curly_brackets=True, exclude_keys=list(context.keys()),
                    )
                    retry_prompt = substitute_template_variables(processed_retry, context)
                    retry_prompt += (
                        "\n\n% RETRY NOTICE — MUST CREATE MISSING FILES\n"
                        f"A prior extraction attempt claimed FILES_CREATED "
                        f"but these are missing on disk: {missing}.\n"
                        "You MUST use the Write tool to actually create each of "
                        "these files with the correct content. Do not just emit "
                        "markers — the orchestrator verifies files exist."
                    )
                    r_success, r_output, r_cost, r_model = run_agentic_task(
                        instruction=retry_prompt,
                        cwd=current_work_dir,
                        verbose=verbose, quiet=quiet,
                        timeout=SPLIT_STEP_TIMEOUTS["6_extract"] + timeout_adder,
                        label=f"6_extract_child_{i+1}_retry_{retry_count}",
                        max_retries=DEFAULT_MAX_RETRIES,
                    )
                    total_cost += r_cost
                    model_used = r_model
                    output += f"\n---RETRY {retry_count}---\n{r_output}"
                    missing = [
                        f for f in claimed_created
                        if not (current_work_dir / f).exists()
                    ]
                if missing and not quiet:
                    console.print(
                        f"[red]Child {i+1}: {len(missing)} files still missing "
                        f"after {retry_count} retries[/red]"
                    )

                # NOW add verified files to changed_files (Bug #4 fix:
                # only track files that actually exist on disk).
                for f in claimed_created + claimed_modified:
                    if f and f not in changed_files and (current_work_dir / f).exists():
                        changed_files.append(f)

                # Only count as extracted if the agent succeeded and all
                # claimed files exist. Otherwise on resume we'd skip this
                # child (the loop starts at len(children_extracted)).
                if success and not missing:
                    children_extracted.append(output)
                elif not missing:
                    # Agent reported failure but files were created — count it
                    children_extracted.append(output)
                else:
                    if not quiet:
                        console.print(
                            f"[yellow]Child {i+1} extraction incomplete — "
                            f"will retry on next run[/yellow]"
                        )
                state["children_extracted"] = children_extracted
                state["changed_files"] = changed_files
                state["total_cost"] = total_cost
                github_comment_id = save_workflow_state(
                    cwd, split_id, "split", state, state_dir, "", "", use_github_state, github_comment_id
                )
            extracted_count = len(state.get("children_extracted", []))
            extract_msg = (
                f"{extracted_count}/{total_children} children extracted"
                if extracted_count < total_children
                else "All children extracted"
            )
            state["step_outputs"]["6"] = extract_msg
            context["step6_output"] = extract_msg
            # If some children failed, DON'T mark step 6 as complete so
            # resume re-enters this step and retries the failed children.
            if extracted_count < total_children:
                step6_idx = ordered_steps.index("6_extract")
                if step6_idx > 0:
                    state["last_completed_step"] = ordered_steps[step6_idx - 1]
                else:
                    state["last_completed_step"] = None
                github_comment_id = save_workflow_state(
                    cwd, split_id, "split", state, state_dir, "", "", use_github_state, github_comment_id
                )
                verify_failures.append(
                    f"Partial extraction: {extracted_count}/{total_children} children"
                )
                continue

        # ── Repair loop ────────────────────────────────────────────
        elif step == "8_repair":
            if not verify_failures:
                state["step_outputs"]["8"] = "No repairs needed"
                context["step8_output"] = "No repairs needed"
                continue
            if selected_option is None:
                state["step_outputs"]["8"] = "No selected option for repair"
                continue
            max_iterations = 5
            previous_fixes: List[str] = []
            for iteration in range(1, max_iterations + 1):
                if not verify_failures:
                    break
                context["child_name"] = "all_children"
                context["verify_failures"] = "\n".join(verify_failures)
                context["previous_fixes"] = "\n---\n".join(previous_fixes[-3:])
                context["repair_iteration"] = iteration
                context["max_repair_iterations"] = max_iterations

                template_name = "agentic_split_step8_repair_LLM"
                prompt_template = load_prompt_template(template_name)
                if not prompt_template:
                    break
                processed = preprocess(
                    prompt_template, recursive=True,
                    double_curly_brackets=True, exclude_keys=list(context.keys()),
                )
                formatted_prompt = substitute_template_variables(processed, context)
                success, output, step_cost, step_model = run_agentic_task(
                    instruction=formatted_prompt,
                    cwd=current_work_dir,
                    verbose=verbose, quiet=quiet,
                    timeout=SPLIT_STEP_TIMEOUTS["8_repair"] + timeout_adder,
                    label=f"8_repair_iter_{iteration}",
                    max_retries=DEFAULT_MAX_RETRIES,
                )
                total_cost += step_cost
                model_used = step_model
                previous_fixes.append(output)

                # Parse FILES_CREATED / FILES_MODIFIED from repair output.
                # Only track files that actually exist on disk (same guard
                # as step 6 extraction — prevents phantom entries).
                for marker in ("FILES_CREATED:", "FILES_MODIFIED:"):
                    match = re.search(
                        rf"{marker}\s*([\s\S]+?)(?:\n\s*\n|\n[A-Z_]+:|$)",
                        output,
                    )
                    if match:
                        files_list = [
                            f.strip().strip(",").strip("`").strip()
                            for f in match.group(1).split(",")
                        ]
                        for f in files_list:
                            if f and f not in changed_files and (current_work_dir / f).exists():
                                changed_files.append(f)

                # If repair agent emits REPAIR_EXHAUSTED, stop trying.
                # Use _check_hard_stop (line-start matching) instead of
                # raw substring to avoid false positives from prose.
                if _check_hard_stop("8_repair", output, force_split):
                    if not quiet:
                        console.print(
                            f"[yellow]Repair iteration {iteration}: "
                            f"REPAIR_EXHAUSTED — stopping[/yellow]"
                        )
                    break

                # Re-run validation + tests + lint after repair (same as
                # step 7a) so we detect whether the repair actually fixed
                # the functional failures, not just structural ones.
                plan = selected_option.plan if isinstance(selected_option, SplitOption) else None
                new_failures: List[str] = []
                if plan is not None:
                    vr = validate_extraction(plan, current_work_dir)
                    if not vr.passed:
                        new_failures = [f.message for f in vr.failures if f.severity == "error"]
                    # Re-run tests (same logic as step 7a)
                    target_path = Path(target_file)
                    test_cmd_obj = get_test_command(target_path)
                    if test_cmd_obj is not None:
                        try:
                            subprocess.run(
                                shlex.split(test_cmd_obj.command),
                                cwd=str(test_cmd_obj.cwd or current_work_dir),
                                check=True, capture_output=True, text=True,
                                timeout=300,
                            )
                        except subprocess.CalledProcessError as e:
                            stderr = (e.stderr or '')[:500]
                            if not ("ImportError" in stderr or "ModuleNotFoundError" in stderr
                                    or "No module named" in stderr):
                                new_failures.append(f"Tests failed: {stderr}")
                        except subprocess.TimeoutExpired:
                            new_failures.append("Tests timed out after 300s")
                    # Re-run lint
                    for lint_cmd_obj in get_lint_commands(target_path):
                        try:
                            subprocess.run(
                                shlex.split(lint_cmd_obj.command),
                                cwd=str(lint_cmd_obj.cwd or current_work_dir),
                                check=True, capture_output=True, text=True,
                                timeout=120,
                            )
                        except subprocess.CalledProcessError as e:
                            new_failures.append(f"Lint failed: {(e.stderr or '')[:500]}")
                        except subprocess.TimeoutExpired:
                            new_failures.append("Lint timed out after 120s")

                if not quiet:
                    console.print(
                        f"[blue]Repair iter {iteration}: {len(verify_failures)} -> "
                        f"{len(new_failures)} error-severity failures[/blue]"
                    )

                # If no progress, stop
                if len(new_failures) >= len(verify_failures) and iteration > 1:
                    if not quiet:
                        console.print(
                            "[yellow]Repair not making progress — stopping[/yellow]"
                        )
                    break
                verify_failures = new_failures

                # Update quant_metrics to reflect post-repair state. Without
                # this, validation_pass stays at -1 from step 7a even after
                # repair fixes all failures, and the improvement gate aborts
                # a successful split as ABORT_REGRESSION.
                quant_metrics["validation_pass"] = 1 if not verify_failures else -1

                # Persist state after each iteration
                state["verify_failures"] = verify_failures
                state["changed_files"] = changed_files
                state["quant_metrics"] = quant_metrics
                state["total_cost"] = total_cost
                github_comment_id = save_workflow_state(
                    cwd, split_id, "split", state, state_dir, "", "", use_github_state, github_comment_id,
                )
            state["step_outputs"]["8"] = f"Repair complete ({len(verify_failures)} remaining)"
            context["step8_output"] = state["step_outputs"]["8"]

        # ── Python (deterministic) steps ───────────────────────────
        else:
            if step == "5_setup_worktree":
                git_root = get_git_root(cwd)
                if not git_root:
                    clear_agentic_progress()
                    _restore_signals()
                    return False, "Not a git repository", total_cost, model_used, changed_files
                wt_path, err = setup_worktree(
                    git_root, split_id, quiet,
                    branch_prefix="split", worktree_prefix="split",
                    base_ref="HEAD",
                )
                if err:
                    clear_agentic_progress()
                    _restore_signals()
                    return False, f"Worktree setup failed: {err}", total_cost, model_used, changed_files
                current_work_dir = wt_path
                context["worktree_path"] = str(wt_path)
                state["worktree_path"] = str(wt_path)
                worktree_path_str = str(wt_path)

            elif step == "7a_verify_local":
                if no_verify:
                    if not quiet:
                        console.print("[yellow]Skipping verification (no_verify flag)[/yellow]")
                    # Even with no_verify, record that verification was skipped
                    # so the improvement gate has something to work with
                    # Use 0 (neutral), not 1 — otherwise the improvement
                    # gate counts this as a "positive metric" and auto-ships
                    # unverified splits (Bug #3 from review).
                    quant_metrics["verification_skipped"] = 0
                    # Also set validation_pass to 0 (neutral) so the
                    # improvement gate doesn't see a missing metric and
                    # produce ABORT_NO_IMPROVEMENT on valid splits.
                    quant_metrics["validation_pass"] = 0
                else:
                    # Structural validation
                    plan = selected_option.plan if isinstance(selected_option, SplitOption) else None
                    if plan is not None:
                        validation_result = validate_extraction(plan, current_work_dir)
                        if not validation_result.passed:
                            # Only route error-severity failures to repair.
                            # Warnings are cosmetic and repair wastes time
                            # trying to "fix" them.
                            for f in validation_result.failures:
                                if f.severity == "error":
                                    verify_failures.append(f.message)
                            if not quiet:
                                err_ct = sum(1 for f in validation_result.failures if f.severity == "error")
                                warn_ct = len(validation_result.failures) - err_ct
                                console.print(f"[red]Validation: {err_ct} errors, {warn_ct} warnings[/red]")

                    # Compute quantitative metrics from the split result.
                    # These feed into the improvement gate alongside the
                    # qualitative assessment from step 7 (assess).
                    # The parent may have been replaced by a package dir
                    # (e.g. pdd_executor.py -> pdd_executor/__init__.py),
                    # so check both locations.
                    target_path_obj = Path(target_file)
                    target_rel = target_path_obj
                    try:
                        target_rel = target_path_obj.relative_to(cwd)
                    except ValueError:
                        pass
                    # Candidates: original file path, or __init__.py of a
                    # package that replaced it.
                    parent_candidates = [
                        current_work_dir / target_rel,
                        current_work_dir / target_rel.with_suffix("") / "__init__.py",
                        current_work_dir / target_path_obj.name,
                    ]
                    post_lines = 0
                    for cand in parent_candidates:
                        if cand.is_file():
                            try:
                                post_lines = len(cand.read_text().splitlines())
                                break
                            except OSError:
                                continue
                    if post_lines > 0:
                        try:
                            original_lines = int(context.get("original_line_count", 0))
                            if original_lines > 0:
                                # Positive delta = reduction = improvement
                                quant_metrics["parent_line_reduction"] = original_lines - post_lines
                        except (ValueError, TypeError):
                            pass
                    num_children = len(selected_option.plan.children) if selected_option else 0
                    if num_children > 1:
                        # Count children as improvement only if >1 (a real split)
                        quant_metrics["children_created"] = num_children - 1
                    # validation_pass is driven by whether any error-severity
                    # failures exist. Previously used keyword matching on
                    # messages which missed structural failures like
                    # "Expected 5 children but found 2".
                    quant_metrics["validation_pass"] = 1 if not verify_failures else -1

                    # Run tests
                    target_path = Path(target_file)
                    test_cmd_obj = get_test_command(target_path)
                    tests_ran = False
                    tests_passed = True
                    if test_cmd_obj is not None:
                        tests_ran = True
                        try:
                            subprocess.run(
                                shlex.split(test_cmd_obj.command),
                                cwd=str(test_cmd_obj.cwd or current_work_dir),
                                check=True, capture_output=True, text=True,
                                timeout=300,
                            )
                        except subprocess.CalledProcessError as e:
                            stderr = (e.stderr or '')[:500]
                            # ImportError / ModuleNotFoundError = missing deps,
                            # not a real test failure from the split
                            if ("ImportError" in stderr or "ModuleNotFoundError" in stderr
                                    or "No module named" in stderr):
                                if not quiet:
                                    console.print(
                                        "[yellow]Tests skipped — missing deps "
                                        "(not a split regression)[/yellow]"
                                    )
                                tests_ran = False  # treat as unable-to-run
                            else:
                                verify_failures.append(f"Tests failed: {stderr}")
                                tests_passed = False
                        except subprocess.TimeoutExpired:
                            verify_failures.append("Tests timed out after 300s")
                            tests_passed = False
                    # Only record tests_pass if we could actually run them
                    if tests_ran:
                        quant_metrics["tests_pass"] = 1 if tests_passed else -1

                    # Run lint
                    for lint_cmd_obj in get_lint_commands(target_path):
                        try:
                            subprocess.run(
                                shlex.split(lint_cmd_obj.command),
                                cwd=str(lint_cmd_obj.cwd or current_work_dir),
                                check=True, capture_output=True, text=True,
                                timeout=120,
                            )
                        except subprocess.CalledProcessError as e:
                            verify_failures.append(f"Lint failed: {(e.stderr or '')[:500]}")
                        except subprocess.TimeoutExpired:
                            verify_failures.append("Lint timed out after 120s")

            elif step == "7b_regen_gate":
                if skip_regen_gate:
                    if not quiet:
                        console.print("[yellow]Skipping regen gate (skip_regen_gate flag)[/yellow]")
                else:
                    for file in changed_files:
                        file_path = Path(file)
                        if file_path.suffix != ".prompt":
                            continue
                        basename = file_path.stem.replace("_python", "").replace("_typescript", "")
                        try:
                            snapshot_src = current_work_dir / file
                            if snapshot_src.exists():
                                shutil.copy(str(snapshot_src), f"{snapshot_src}.snapshot")
                            subprocess.run(
                                ["pdd", "sync", basename, "--max-attempts", "1", "--budget", "5.0"],
                                cwd=str(current_work_dir), check=True,
                                capture_output=True, text=True, timeout=600,
                            )
                        except subprocess.CalledProcessError as e:
                            verify_failures.append(
                                f"Regen gate failed for {basename}: {(e.stderr or '')[:500]}"
                            )
                        except subprocess.TimeoutExpired:
                            verify_failures.append(f"Regen gate timed out for {basename}")

            elif step == "7c_arch_sync":
                # Scope arch sync to the target file's directory tree. The
                # sync_all_prompts_to_architecture function scans the entire
                # prompts_dir recursively; if run on the project root it will
                # also try to sync unrelated prompts (e.g. CRM, frontend) that
                # aren't part of this split and may have broken references.
                # Find the prompts dir closest to the target file.
                target_abs = (Path(target_file)
                              if Path(target_file).is_absolute()
                              else cwd / target_file)
                prompts_dir: Optional[Path] = None
                # Walk up from target file's dir looking for a sibling prompts/
                candidate = target_abs.parent
                for _ in range(8):
                    for p_name in ("prompts", "prompts/src"):
                        maybe = candidate / p_name
                        if maybe.is_dir():
                            prompts_dir = maybe
                            break
                    if prompts_dir is not None:
                        break
                    if candidate.parent == candidate:
                        break
                    candidate = candidate.parent
                # Similarly find an architecture.json near the target
                architecture_path: Optional[Path] = None
                candidate = target_abs.parent
                for _ in range(8):
                    maybe = candidate / "architecture.json"
                    if maybe.is_file():
                        architecture_path = maybe
                        break
                    if candidate.parent == candidate:
                        break
                    candidate = candidate.parent
                if prompts_dir is None or architecture_path is None:
                    if not quiet:
                        console.print(
                            "[yellow]Skipping arch sync — no prompts/ or "
                            "architecture.json found near target[/yellow]"
                        )
                else:
                    try:
                        sync_result = sync_all_prompts_to_architecture(
                            prompts_dir, architecture_path, dry_run=False
                        )
                        if not sync_result.get("success", False):
                            errors = sync_result.get("errors", [])
                            # Filter out errors for unrelated prompts that
                            # existed before this split (we only care about
                            # prompts we created/modified).
                            # changed_files has source paths (e.g. pdd/foo.py)
                            # while errors reference .prompt paths — match on
                            # basenames (stems) so e.g. "foo" matches both
                            # "pdd/foo.py" and "prompts/foo.prompt".
                            own_stems = {
                                Path(f).stem for f in changed_files
                            }
                            relevant_errors = [
                                e for e in errors
                                if any(stem in str(e) for stem in own_stems)
                            ]
                            if relevant_errors:
                                verify_failures.append(
                                    f"Arch sync failed: {relevant_errors}"
                                )
                    except Exception as exc:
                        if not quiet:
                            console.print(
                                f"[yellow]Arch sync errored (non-fatal): {exc}[/yellow]"
                            )

        # Persist state after every step
        state["last_completed_step"] = step
        state["total_cost"] = total_cost
        state["model_used"] = model_used
        state["changed_files"] = changed_files
        state["verify_failures"] = verify_failures
        state["quant_metrics"] = quant_metrics
        state["phase_plans"] = phase_plans
        state["intent"] = current_intent
        state["iteration_count"] = iteration_count
        github_comment_id = save_workflow_state(
            cwd, split_id, "split", state, state_dir, "", "", use_github_state, github_comment_id
        )

    # ── Refinement iteration (U6) — FOCUSED ────────────────────────
    # If step 9 flagged a specific child as still too monolithic, run
    # FOCUSED phase extraction on just that file: step 6a + step 6
    # scoped to the one target. We do NOT re-run steps 0-4 because
    # those produce a fresh decomposition of the target as if it were
    # a new split problem, which roughly doubles cost and often
    # produces the same 7-child plan (we saw this on pdd_executor).
    pending_refine = state.get("_pending_refine")
    if (
        pending_refine
        and iteration_count < MAX_REFINEMENT_ITERATIONS
        and not no_phase_extraction
    ):
        iteration_count += 1
        state["iteration_count"] = iteration_count
        refined_target = pending_refine.get("target_child_file") or target_file
        state["_pending_refine"] = None
        if not quiet:
            console.print(
                f"[cyan]Focused refinement pass — "
                f"phase extraction on {refined_target}[/cyan]"
            )

        # Treat the refined target as a single-child plan for step 6a.
        refined_target_path = current_work_dir / refined_target
        if not refined_target_path.is_file():
            # File doesn't exist — skip refinement gracefully.
            if not quiet:
                console.print(
                    f"[yellow]Refinement target not found: "
                    f"{refined_target} — skipping iteration[/yellow]"
                )
        else:
            # Build a minimal per-child context for step 6a.
            refine_child = {
                "name": Path(refined_target).stem,
                "new_source": refined_target,
                "new_prompt": "",
                "new_example": "",
                "new_test": "",
                "symbols": [],
                "rationale": pending_refine.get("reason", ""),
            }
            context["current_child_index"] = 1
            context["current_child"] = json.dumps(refine_child, default=str)
            context["selected_option"] = json.dumps({
                "name": "refinement_mode",
                "plan": {"children": [refine_child]},
            }, default=str)
            context["children_extracted"] = "[]"

            # Step 6a on the refined target.
            template_name = "agentic_split_step6a_phase_extract_LLM"
            p_template = load_prompt_template(template_name)
            refine_phase_plan: Optional[Dict[str, Any]] = None
            if p_template:
                processed = preprocess(
                    p_template, recursive=True,
                    double_curly_brackets=True,
                    exclude_keys=list(context.keys()),
                )
                formatted_prompt = substitute_template_variables(
                    processed, context
                )
                pe_success, pe_output, pe_cost, pe_model = run_agentic_task(
                    instruction=formatted_prompt,
                    cwd=current_work_dir,
                    verbose=verbose, quiet=quiet,
                    timeout=SPLIT_STEP_TIMEOUTS["6a_phase_extract"] + timeout_adder,
                    label=f"6a_refine_iter_{iteration_count}",
                    max_retries=DEFAULT_MAX_RETRIES,
                )
                total_cost += pe_cost
                model_used = pe_model
                parsed_pe = _parse_step_output(pe_output, PhaseExtractionPlan)
                if isinstance(parsed_pe, PhaseExtractionPlan) and parsed_pe.should_extract:
                    refine_phase_plan = {
                        "should_extract": True,
                        "target_symbol": parsed_pe.target_symbol,
                        "target_file": parsed_pe.target_file or refined_target,
                        "phases": [
                            {
                                "name": p.name, "description": p.description,
                                "line_range": p.line_range, "inputs": p.inputs,
                                "outputs": p.outputs, "side_effects": p.side_effects,
                            }
                            for p in parsed_pe.phases
                        ],
                        "parent_shell": parsed_pe.parent_shell,
                        "rationale": parsed_pe.rationale,
                        "reason": "",
                    }

            # Step 6 extract the phase plan (only if one was produced).
            if refine_phase_plan:
                context["phase_plan"] = json.dumps(refine_phase_plan, default=str)
                template_name = "agentic_split_step6_extract_LLM"
                p_template = load_prompt_template(template_name)
                if p_template:
                    processed = preprocess(
                        p_template, recursive=True,
                        double_curly_brackets=True,
                        exclude_keys=list(context.keys()),
                    )
                    formatted_prompt = substitute_template_variables(
                        processed, context
                    )
                    ex_success, ex_output, ex_cost, ex_model = run_agentic_task(
                        instruction=formatted_prompt,
                        cwd=current_work_dir,
                        verbose=verbose, quiet=quiet,
                        timeout=SPLIT_STEP_TIMEOUTS["6_extract"] + timeout_adder,
                        label=f"6_refine_iter_{iteration_count}",
                        max_retries=DEFAULT_MAX_RETRIES,
                    )
                    total_cost += ex_cost
                    model_used = ex_model
                    # Parse FILES_CREATED/FILES_MODIFIED markers.
                    # Only track files that actually exist on disk (same
                    # guard as step 6 extraction — prevents phantom entries).
                    for marker in ("FILES_CREATED:", "FILES_MODIFIED:"):
                        match = re.search(
                            rf"{marker}\s*([\s\S]+?)(?:\n\s*\n|\n[A-Z_]+:|$)",
                            ex_output,
                        )
                        if match:
                            for f in match.group(1).split(","):
                                f = f.strip().strip(",").strip("`").strip()
                                if f and f not in changed_files and (current_work_dir / f).exists():
                                    changed_files.append(f)
                    if not quiet:
                        console.print(
                            f"[cyan]Refinement iter {iteration_count}: "
                            f"phase extraction applied on {refined_target}[/cyan]"
                        )
            else:
                if not quiet:
                    console.print(
                        f"[cyan]Refinement iter {iteration_count}: "
                        f"step 6a said no extraction warranted on "
                        f"{refined_target} — skipping[/cyan]"
                    )

        # Re-run verification after refinement.
        if selected_option is not None:
            plan = selected_option.plan
            vr = validate_extraction(plan, current_work_dir)
            verify_failures = [f.message for f in vr.failures if f.severity == "error"]
            quant_metrics["validation_pass"] = 1 if not verify_failures else -1
            state["verify_failures"] = verify_failures
            state["quant_metrics"] = quant_metrics
            state["changed_files"] = changed_files
            state["total_cost"] = total_cost
            github_comment_id = save_workflow_state(
                cwd, split_id, "split", state, state_dir,
                "", "", use_github_state, github_comment_id,
            )

    # ── Improvement gate ───────────────────────────────────────────
    if qual_assess is None:
        # If we reached here, the pipeline completed all steps. Default to
        # moderate so a successful split isn't aborted by a missing assessment.
        qual_assess = QualitativeAssessment(
            overall_verdict="moderate",
            rationale="Defaulted: pipeline completed but no assessment parsed",
        )
    decision = _apply_improvement_gate(quant_metrics, qual_assess)
    if "ABORT" in decision:
        clear_agentic_progress()
        _restore_signals()
        return False, f"Improvement gate: {decision}", total_cost, model_used, changed_files

    # Final summary
    if not quiet:
        console.print("\n[green]Split complete[/green]")
        console.print(f"   Total cost: ${total_cost:.4f}")
        console.print(f"   Files changed: {', '.join(changed_files)}")
        console.print(f"   Decision: {decision}")

    # Only clear state on a clean AUTO_SHIP. HUMAN_REVIEW_REQUIRED and
    # AUTO_SHIP_WARNING preserve state so the user can resume / re-run
    # without losing the $30-80 of accumulated context. AUTO_SHIP clears
    # because the run is fully done and needs no human follow-up.
    if decision == "AUTO_SHIP":
        clear_workflow_state(cwd, split_id, "split", state_dir, "", "", use_github_state)
        # Clean up the git worktree on AUTO_SHIP (the only fully-clean
        # terminal state). For HUMAN_REVIEW_REQUIRED the worktree stays
        # so the reviewer can inspect the split result.
        if worktree_path_str and Path(worktree_path_str).is_dir():
            try:
                git_root = get_git_root(cwd)
                if git_root:
                    subprocess.run(
                        ["git", "worktree", "remove", "--force", worktree_path_str],
                        cwd=str(git_root), capture_output=True, text=True,
                    )
            except Exception:
                pass  # best-effort cleanup
    elif not quiet:
        console.print(
            f"[dim]State preserved at {state_dir} — rerun `pdd split` "
            f"to resume, or `rm -rf {state_dir}` to discard.[/dim]"
        )
    clear_agentic_progress()
    _restore_signals()
    return True, f"Split complete ({decision})", total_cost, model_used, changed_files
