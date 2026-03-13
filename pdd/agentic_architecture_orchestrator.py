"""
Orchestrator for the agentic architecture workflow.
Runs each step as a separate agentic task, accumulates context between steps,
tracks overall progress and cost, and supports resuming from saved state.

Step 1:   Analyze PRD
Step 1b:  Complexity Assessment (may exit with sub-issues if PRD too complex)
Steps 2-5: Analysis and design
Step 5b:  Completeness Gate (hard stop if incomplete after 3 retries)
Steps 6-7: Research dependencies and generate architecture.json
Step 7b:  Architecture Self-Review (naming, deps, priority consistency)
Step 8:   Generate .pddrc
Step 8.5: Generate shared context documents (data dictionary, API contracts)
Step 9:   Prompt generation
Step 9b:  Cross-File Consistency Audit (identifier consistency across prompts)
Steps 10-12: Validation with in-place fixing (completeness, sync, dependencies)
Step 13:  Fix validation errors

Each validation step (10-12) retries up to 3 times with fixes before moving to next.
Once a step passes, we don't re-validate it (prevents fix loops).
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Union, Any

from rich.console import Console
from rich.markup import escape

from pdd.agentic_common import (
    run_agentic_task,
    load_workflow_state,
    save_workflow_state,
    clear_workflow_state,
    validate_cached_state,
    DEFAULT_MAX_RETRIES,
)
from pdd.architecture_registry import merge_architecture, record_generation
from pdd.architecture_sync import normalize_architecture_filenames
from pdd.load_prompt_template import load_prompt_template
from pdd.preprocess import preprocess
# Import render_mermaid dynamically or assume it's available in the package
try:
    from pdd.render_mermaid import generate_mermaid_code, generate_html
    HAS_MERMAID = True
except ImportError:
    HAS_MERMAID = False

# Initialize console for rich output
console = Console(width=120)

# Per-Step Timeouts (Workflow specific)
ARCH_STEP_TIMEOUTS: Dict[Union[int, float], float] = {
    1: 340.0,    # Analyze PRD
    1.5: 340.0,  # Complexity assessment
    2: 340.0,    # Deep Analysis
    2.5: 340.0,  # Codebase Scan
    3: 600.0,    # Research
    4: 600.0,    # Data Model Design
    5: 600.0,    # Design
    5.5: 600.0,  # Early completeness gate (module design)
    6: 600.0,    # Research Dependencies
    7: 1000.0,   # Generate (architecture.json + scaffolding)
    7.5: 340.0,  # Architecture self-review
    8: 600.0,    # Generate and validate .pddrc
    8.5: 600.0,  # Generate context documents (data dictionary, API contracts)
    9: 900.0,    # Generate prompts
    9.5: 600.0,  # Cross-file consistency audit
    9.7: 600.0,  # Cross-sub-issue reconciliation
    10: 340.0,   # Validate completeness (prompt-level)
    11: 600.0,   # Validate sync (pdd sync --dry-run for each module)
    12: 600.0,   # Validate dependencies (preprocess)
    13: 900.0,   # Fix all validation errors
}

MAX_VALIDATION_ITERATIONS = 5


def _check_hard_stop(step_num: int, output: str) -> Optional[str]:
    """Check output for hard stop conditions."""
    if step_num == 1 and "PRD Content Insufficient" in output:
        return "PRD insufficient"
    if step_num == 2 and "Tech Stack Ambiguous" in output:
        return "Tech stack ambiguous"
    if step_num == 5 and "Clarification Needed" in output:
        return "Clarification needed"
    return None


def _check_step4_output(output: str) -> bool:
    """Check if step 4 output contains data model content instead of module design.

    Returns True if the output looks like a valid data model design.
    Returns False if the output looks like module design (wrong step).
    """
    output_lower = output.lower()

    # Expected data model markers (need at least 2)
    data_model_markers = [
        "core entities",
        "relationships",
        "storage decision",
        "schema/orm",
        "cardinality",
        "foreign key",
    ]
    data_model_hits = sum(1 for m in data_model_markers if m in output_lower)

    # Wrong-step markers that indicate module design instead of data model
    wrong_step_markers = [
        "module list",
        "dependency graph",
        "module design",
        "## step 4: module design",
        "## step 5: module design",
    ]
    wrong_step_hits = sum(1 for m in wrong_step_markers if m in output_lower)

    # Fail if wrong-step markers are present and data model markers are scarce
    if wrong_step_hits > 0 and data_model_hits < 2:
        return False

    return True


def _get_state_dir(cwd: Path) -> Path:
    """Get the state directory relative to git root or cwd."""
    return cwd / ".pdd" / "arch-state"


def _ensure_pddrc_contexts_preserved(
    pddrc_file: Path,
    existing_pddrc: str,
    quiet: bool = False,
) -> None:
    """Restore any contexts the LLM dropped from .pddrc during Step 8.

    Parses the original existing_pddrc and the newly written file.
    If any context names from the original are missing in the new file,
    merges them back in and rewrites the file.
    """
    if not existing_pddrc or not existing_pddrc.strip():
        return

    import yaml

    try:
        old_config = yaml.safe_load(existing_pddrc)
    except Exception:
        return
    if not isinstance(old_config, dict):
        return
    old_contexts = old_config.get("contexts", {})
    if not isinstance(old_contexts, dict) or not old_contexts:
        return

    try:
        new_content = pddrc_file.read_text(encoding="utf-8")
        new_config = yaml.safe_load(new_content)
    except Exception:
        return
    if not isinstance(new_config, dict):
        return
    new_contexts = new_config.get("contexts", {})
    if not isinstance(new_contexts, dict):
        new_contexts = {}

    missing = set(old_contexts.keys()) - set(new_contexts.keys())
    if not missing:
        return

    if not quiet:
        console.print(
            f"[yellow]Warning: LLM dropped {len(missing)} existing "
            f"context(s) from .pddrc: {sorted(missing)}. Restoring...[/yellow]"
        )

    for name in missing:
        new_contexts[name] = old_contexts[name]
    new_config["contexts"] = new_contexts
    pddrc_file.write_text(
        yaml.dump(new_config, default_flow_style=False, sort_keys=False),
        encoding="utf-8",
    )

    if not quiet:
        console.print(f"   → Restored {len(missing)} missing context(s)")


def _parse_files_marker(output: str, marker: str = "FILES_CREATED:") -> List[str]:
    """
    Parse FILES_CREATED: or FILES_MODIFIED: markers from step output.
    Returns list of file paths mentioned in the marker.
    """
    files = []
    for line in output.splitlines():
        line = line.strip()
        if line.startswith(marker):
            file_list = line.split(":", 1)[1].strip()
            files = [f.strip() for f in file_list.split(",") if f.strip()]
            break
    return files


def _verify_files_exist(cwd: Path, files: List[str], quiet: bool = False) -> List[str]:
    """
    Verify that reported files actually exist on disk.
    Returns list of files that exist.
    """
    verified = []
    for filepath in files:
        full_path = cwd / filepath
        if full_path.exists():
            verified.append(filepath)
        elif not quiet:
            console.print(f"[yellow]Warning: Reported file not found: {filepath}[/yellow]")
    return verified


def _save_architecture_files(
    cwd: Path,
    architecture_json_content: str,
    issue_title: str
) -> List[str]:
    """
    Validates architecture.json (already on disk) and generates the Mermaid HTML diagram.
    """
    output_files = []
    json_path = cwd / "architecture.json"

    try:
        if json_path.exists():
            with open(json_path, "r", encoding="utf-8") as f:
                file_content = f.read()
        else:
            file_content = architecture_json_content

        # Clean up any markdown fencing
        clean_content = file_content.strip()
        if clean_content.startswith("```json"):
            clean_content = clean_content[7:]
        if clean_content.startswith("```"):
            clean_content = clean_content[3:]
        if clean_content.endswith("```"):
            clean_content = clean_content[:-3]
        clean_content = clean_content.strip()

        arch_data = json.loads(clean_content)
        # Issue #617: ensure filename mirrors filepath; handle list or object wrappers safely
        arch_list = None
        if isinstance(arch_data, list):
            normalize_architecture_filenames(arch_data)
            arch_list = arch_data
        elif isinstance(arch_data, dict):
            for key in ("architecture", "files"):
                if key in arch_data and isinstance(arch_data[key], list):
                    normalize_architecture_filenames(arch_data[key])
                    arch_list = arch_data[key]
                    break
            else:
                console.print(
                    "[yellow]Warning: architecture JSON is an object and does not "
                    "contain a list under known keys ('architecture', 'files'); "
                    "skipping filename normalization.[/yellow]"
                )
        else:
            console.print(
                "[yellow]Warning: Unexpected architecture JSON type "
                f"({type(arch_data).__name__}); skipping filename normalization.[/yellow]"
            )

        with open(json_path, "w", encoding="utf-8") as f:
            json.dump(arch_data, f, indent=2)
        output_files.append(str(json_path))

        if HAS_MERMAID and arch_list is not None:
            mermaid_code = generate_mermaid_code(arch_list, issue_title)
            html_content = generate_html(mermaid_code, arch_list, issue_title)

            html_path = cwd / "architecture_diagram.html"
            with open(html_path, "w", encoding="utf-8") as f:
                f.write(html_content)
            output_files.append(str(html_path))
        else:
            console.print("[yellow]Warning: pdd.render_mermaid not found. Skipping diagram generation.[/yellow]")

    except json.JSONDecodeError:
        console.print("[red]Error: Failed to parse architecture.json as JSON. File may be corrupted.[/red]")
        output_files.append(str(json_path))
    except Exception as e:
        console.print(f"[red]Error processing architecture files: {e}[/red]")

    return output_files


def _check_validation_result(output: str) -> bool:
    """Check if validation output indicates VALID."""
    return "VALIDATION_RESULT: VALID" in output


def _validate_generated_test_syntax(cwd: Path) -> List[str]:
    """Scan prompt files for embedded code blocks and validate their syntax.

    Checks Python blocks with ast.parse() and TypeScript/JS blocks with basic
    brace/bracket matching.  Returns a list of human-readable error strings.
    Non-blocking — callers should log warnings, not fail the workflow.
    """
    import ast as _ast
    import re as _re

    errors: List[str] = []
    prompts_dir = cwd / "prompts"
    if not prompts_dir.exists():
        return errors

    # Match fenced code blocks: ```python ... ``` or ```typescript ... ```
    block_pattern = _re.compile(
        r"```(python|typescript|ts|javascript|js)\s*\n(.*?)```",
        _re.DOTALL | _re.IGNORECASE,
    )

    for prompt_file in sorted(prompts_dir.glob("*.prompt")):
        try:
            content = prompt_file.read_text(encoding="utf-8")
        except Exception:
            continue

        for match in block_pattern.finditer(content):
            lang = match.group(1).lower()
            code = match.group(2)

            if lang == "python":
                try:
                    _ast.parse(code)
                except SyntaxError as exc:
                    errors.append(
                        f"{prompt_file.name}: Python syntax error at line {exc.lineno}: {exc.msg}"
                    )
            elif lang in ("typescript", "ts", "javascript", "js"):
                # Lightweight brace/bracket balance check
                stack: List[str] = []
                openers = {"(": ")", "[": "]", "{": "}"}
                closers = {")", "]", "}"}
                in_string = False
                string_char = ""
                for ch in code:
                    if in_string:
                        if ch == string_char:
                            in_string = False
                        continue
                    if ch in ("'", '"', '`'):
                        in_string = True
                        string_char = ch
                        continue
                    if ch in openers:
                        stack.append(openers[ch])
                    elif ch in closers:
                        if not stack or stack[-1] != ch:
                            errors.append(
                                f"{prompt_file.name}: TypeScript/JS unmatched '{ch}'"
                            )
                            break
                        stack.pop()
                if stack and not any(
                    e.startswith(prompt_file.name) for e in errors
                ):
                    errors.append(
                        f"{prompt_file.name}: TypeScript/JS unclosed bracket(s): "
                        f"{''.join(stack)}"
                    )

    return errors


def run_agentic_architecture_orchestrator(
    issue_url: str,
    issue_content: str,
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    issue_author: str,
    issue_title: str,
    *,
    cwd: Path,
    verbose: bool = False,
    quiet: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
    skip_prompts: bool = False,
    target_dir: Optional[str] = None,
    force_single: bool = False,
    sibling_architectures: str = "",
    existing_pddrc: str = "",
    existing_architecture: str = "",
    related_issues: Optional[List[int]] = None,
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Orchestrates the agentic architecture workflow.

    Step 1:   Analyze PRD
    Step 1b:  Complexity Assessment (may exit with sub-issues)
    Steps 2-5: Analysis and design
    Step 5b:  Completeness Gate (hard stop if incomplete after 3 retries)
    Steps 6-7: Research dependencies and generate architecture.json
    Step 7b:  Architecture Self-Review (naming, deps, priority consistency)
    Step 8:   Generate .pddrc
    Step 8.5: Generate shared context documents (data dictionary, API contracts)
    Step 9:   Prompt generation
    Step 9b:  Cross-File Consistency Audit (identifier consistency across prompts)
    Steps 10-12: Validation with in-place fixing (completeness, sync, dependencies)

    Each validation step retries up to 3 times with fixes before moving to next step.
    Once a step passes, we don't re-validate it (prevents fix loops).

    Args:
        skip_prompts: If True, skip Step 9 and validation steps 10-12.
        force_single: If True, skip complexity check and force single-project generation.

    Returns:
        (success, final_message, total_cost, model_used, output_files)
    """

    if not quiet:
        console.print(f"Generating architecture for issue #{issue_number}: \"{issue_title}\"")

    # Derive base_dir: subproject directory or repo root
    base_dir = cwd / target_dir if target_dir else cwd
    if target_dir:
        base_dir.mkdir(parents=True, exist_ok=True)

    state_dir = _get_state_dir(cwd)

    # Load state
    state, loaded_gh_id = load_workflow_state(
        cwd, issue_number, "architecture", state_dir, repo_owner, repo_name, use_github_state
    )

    # Initialize variables from state or defaults
    if state is not None:
        last_completed_step = state.get("last_completed_step", 0)
        step_outputs = state.get("step_outputs", {})
        total_cost = state.get("total_cost", 0.0)
        model_used = state.get("model_used", "unknown")
        github_comment_id = loaded_gh_id

        # Issue #467: Validate cached state — correct last_completed_step
        # if any cached step outputs have "FAILED:" prefix.
        last_completed_step = validate_cached_state(
            last_completed_step, step_outputs, quiet=quiet
        )
    else:
        state = {"step_outputs": {}, "last_completed_step": 0}
        last_completed_step = 0
        step_outputs = state["step_outputs"]
        total_cost = 0.0
        model_used = "unknown"
        github_comment_id = None

    context = {
        "issue_url": issue_url,
        "issue_content": issue_content,
        "repo_owner": repo_owner,
        "repo_name": repo_name,
        "issue_number": issue_number,
        "issue_author": issue_author,
        "issue_title": issue_title,
        "target_dir": target_dir or ".",
        "target_dir_note": (
            f"Create all files under `{target_dir}/` (NOT the repo root)."
            if target_dir else
            "Create files in the repository root."
        ),
        "sibling_architectures": sibling_architectures or "No existing sibling architectures found.",
        "existing_pddrc": existing_pddrc or "No existing .pddrc found.",
        "existing_architecture": existing_architecture or "No existing architecture.json found.",
        "related_issues": ", ".join(f"#{n}" for n in related_issues) if related_issues else "None",
        "step2b_output": "No codebase scan performed.",
    }

    # Populate context with previous step outputs
    for s_key, s_out in step_outputs.items():
        context[f"step{s_key}_output"] = s_out

    # Track scaffolding files created during generation
    scaffolding_files: List[str] = state.get("scaffolding_files", [])
    prompt_files: List[str] = state.get("prompt_files", [])

    # Determine start step
    start_step = last_completed_step + 1

    # Handle resume logic for fractional steps
    if last_completed_step == 9.5:
        # Step 9b (cross-audit) passed, start at step 10
        start_step = 10
    elif last_completed_step == 7.5:
        # Step 7b (architecture review) passed, start at step 8
        start_step = 8
    elif last_completed_step == 5.5:
        # Step 5b (completeness gate) passed, start at step 6
        start_step = 6
    elif last_completed_step == 2.5:
        # Step 2b (codebase scan) passed, start at step 3
        start_step = 3
    elif last_completed_step == 1.5:
        # Step 1b (complexity) passed, start at step 2
        start_step = 2
    elif 9 < last_completed_step < 10:
        start_step = 10
    elif 8 < last_completed_step < 9:
        start_step = 9
    elif 7 < last_completed_step < 8:
        start_step = 8
    elif 5 < last_completed_step < 6:
        start_step = 6
    elif 2 < last_completed_step < 3:
        start_step = 3
    elif 1 < last_completed_step < 2:
        start_step = 2

    if last_completed_step >= 9.5:
        # If we finished step 9b or later, start at validation loop (step 10)
        start_step = 10
        if not quiet:
            console.print(f"Resuming architecture generation for issue #{issue_number}")
            console.print(f"   Steps 1-9b already complete (cached)")
            console.print(f"   Starting Validation Loop (Step 10)")
    elif last_completed_step >= 9:
        # If we finished step 9, start at step 9b (cross-audit)
        start_step = 10  # 9b is handled specially after step 9
        if not quiet:
            console.print(f"Resuming architecture generation for issue #{issue_number}")
            console.print(f"   Steps 1-9 already complete (cached)")
            console.print(f"   Starting Validation Loop (Step 10)")
    elif last_completed_step >= 8.5:
        # If we finished step 8.5, start at step 9 (prompt generation)
        start_step = 9
        if not quiet:
            console.print(f"Resuming architecture generation for issue #{issue_number}")
            console.print(f"   Steps 1-8.5 already complete (cached)")
            console.print(f"   Starting Step 9 (Prompt Generation)")
    elif last_completed_step >= 8:
        # If we finished step 8, start at step 8.5 (context documents)
        start_step = 9  # Step 8.5 is handled specially after step 8
        if not quiet:
            console.print(f"Resuming architecture generation for issue #{issue_number}")
            console.print(f"   Steps 1-8 already complete (cached)")
            console.print(f"   Starting Step 8.5 (Context Documents)")
    elif last_completed_step >= 7.5:
        # If we finished step 7b, start at step 8 (.pddrc generation)
        start_step = 8
        if not quiet:
            console.print(f"Resuming architecture generation for issue #{issue_number}")
            console.print(f"   Steps 1-7b already complete (cached)")
            console.print(f"   Starting Step 8 (.pddrc Generation)")
    elif last_completed_step >= 7:
        # If we finished step 7, start at step 8 (7b is handled specially)
        start_step = 8
        if not quiet:
            console.print(f"Resuming architecture generation for issue #{issue_number}")
            console.print(f"   Steps 1-7 already complete (cached)")
            console.print(f"   Starting Step 8 (.pddrc Generation)")
    elif last_completed_step > 0:
        if not quiet:
            console.print(f"Resuming architecture generation for issue #{issue_number}")
            console.print(f"   Steps 1-{last_completed_step} already complete (cached)")
            console.print(f"   Starting from Step {start_step}")

    # Total step count for display (1, 1b, 2, 2b, 3-5, 5b, 6-7, 7b, 8, 8.5, 9, 9b, 10-13)
    TOTAL_STEPS = 19

    # --- Steps 1-5: Analysis and Design ---
    steps_1_5 = [
        (1, "analyze_prd", "Extract features, tech stack, requirements from PRD"),
        (2, "analyze", "Deep analysis: module boundaries, shared concerns"),
        (3, "research", "Web research for tech stack docs and conventions"),
        (4, "data_model", "Data model design: entities, relationships, storage"),
        (5, "design", "Design module breakdown with dependency graph"),
    ]

    # --- Steps 6-8: Dependencies, Generation, and .pddrc ---
    steps_6_8 = [
        (6, "research_deps", "Find API docs and code examples per module"),
        (7, "generate", "Generate architecture.json and scaffolding"),
        (8, "pddrc", "Generate and validate .pddrc configuration"),
    ]

    # --- Run Steps 1-5: Analysis and Design ---
    for step_num, name, description in steps_1_5:
        if step_num < start_step:
            continue

        if not quiet:
            console.print(f"[bold][Step {step_num}/{TOTAL_STEPS}][/bold] {description}...")

        template_name = f"agentic_arch_step{step_num}_{name}_LLM"
        prompt_template = load_prompt_template(template_name)
        if not prompt_template:
            return False, f"Missing prompt template: {template_name}", total_cost, model_used, []

        exclude_keys = list(context.keys())
        prompt_template = preprocess(prompt_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys)
        prompt_template = prompt_template.replace("{{", "{").replace("}}", "}")
        formatted_prompt = prompt_template
        for key, value in context.items():
            formatted_prompt = formatted_prompt.replace(f'{{{key}}}', str(value))

        timeout = ARCH_STEP_TIMEOUTS.get(step_num, 340.0) + timeout_adder

        step_success, step_output, step_cost, step_model = run_agentic_task(
            instruction=formatted_prompt,
            cwd=cwd,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout,
            label=f"step{step_num}",
            max_retries=DEFAULT_MAX_RETRIES,
        )

        total_cost += step_cost
        model_used = step_model
        state["total_cost"] = total_cost
        state["model_used"] = model_used

        # Check hard stops
        stop_reason = _check_hard_stop(step_num, step_output)
        if stop_reason:
            if not quiet:
                console.print(f"[yellow]⏹️  Stopped at Step {step_num}: {stop_reason}[/yellow]")
            state["last_completed_step"] = step_num
            state["step_outputs"][str(step_num)] = step_output
            save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
            return False, f"Stopped at step {step_num}: {stop_reason}", total_cost, model_used, []

        if not step_success and not quiet:
            console.print(f"[yellow]Warning: Step {step_num} reported failure but continuing...[/yellow]")

        # Special handling for Step 4 (data model): validate output content
        if step_num == 4 and step_success and not _check_step4_output(step_output):
            console.print(
                "[yellow]Warning: Step 4 produced module design instead of data model. "
                "Retrying...[/yellow]"
            )
            step_success = False
            step_output = (
                "FAILED: Output contains module design instead of data model. "
                "Re-read the prompt — this step is about data entities, "
                "relationships, and storage decisions."
            )

        context[f"step{step_num}_output"] = step_output

        if step_success:
            state["step_outputs"][str(step_num)] = step_output
            state["last_completed_step"] = step_num
        else:
            state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"

        save_result = save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
        if save_result:
            github_comment_id = save_result
            state["github_comment_id"] = github_comment_id

        if not quiet:
            lines = step_output.strip().split('\n')
            brief = lines[-1] if lines else "Done"
            if len(brief) > 80: brief = brief[:77] + "..."
            console.print(f"   → {escape(brief)}")
            if step_success:
                console.print(f"  → Step {step_num} complete.")

        # --- Step 1b: Complexity Assessment (after Step 1) ---
        if step_num == 1 and step_success and start_step <= 1.5:
            if not force_single:
                if not quiet:
                    console.print(f"[bold][Step 1b/{TOTAL_STEPS}][/bold] Assessing PRD complexity...")

                complexity_template_name = "agentic_arch_step1b_complexity_LLM"
                complexity_template = load_prompt_template(complexity_template_name)
                if complexity_template:
                    exclude_keys_1b = list(context.keys())
                    complexity_template = preprocess(complexity_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys_1b)
                    complexity_template = complexity_template.replace("{{", "{").replace("}}", "}")
                    formatted_complexity = complexity_template
                    for key, value in context.items():
                        formatted_complexity = formatted_complexity.replace(f'{{{key}}}', str(value))

                    timeout_1b = ARCH_STEP_TIMEOUTS.get(1.5, 340.0) + timeout_adder
                    c_success, c_output, c_cost, c_model = run_agentic_task(
                        instruction=formatted_complexity,
                        cwd=cwd,
                        verbose=verbose,
                        quiet=quiet,
                        timeout=timeout_1b,
                        label="step1b",
                        max_retries=DEFAULT_MAX_RETRIES,
                    )

                    total_cost += c_cost
                    model_used = c_model
                    state["total_cost"] = total_cost

                    context["step1b_output"] = c_output
                    state["step_outputs"]["1b"] = c_output

                    if "COMPLEXITY_RESULT: COMPLEX" in c_output:
                        if not quiet:
                            console.print("[yellow]⏹️  PRD is too complex for single-project generation.[/yellow]")
                            console.print("   Sub-issues have been created. Run pdd generate on each sub-issue.")
                            console.print("   Use --force-single to override this check.")
                        state["last_completed_step"] = 1.5
                        save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
                        return False, "PRD too complex - sub-issues created, run pdd generate on each", total_cost, model_used, []

                    state["last_completed_step"] = 1.5
                    save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)

                    if not quiet:
                        console.print("   → PRD complexity: manageable, continuing...")

        # --- Step 2b: Codebase Scan (after Step 2) ---
        if step_num == 2 and step_success and start_step <= 2.5:
            if not quiet:
                console.print(f"[bold][Step 2b/{TOTAL_STEPS}][/bold] Scanning existing codebase...")

            scan_template_name = "agentic_arch_step2b_codebase_scan_LLM"
            scan_template = load_prompt_template(scan_template_name)
            if scan_template:
                exclude_keys_2b = list(context.keys())
                scan_template = preprocess(scan_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys_2b)
                scan_template = scan_template.replace("{{", "{").replace("}}", "}")
                formatted_scan = scan_template
                for key, value in context.items():
                    formatted_scan = formatted_scan.replace(f'{{{key}}}', str(value))

                timeout_2b = ARCH_STEP_TIMEOUTS.get(2.5, 340.0) + timeout_adder
                scan_success, scan_output, scan_cost, scan_model = run_agentic_task(
                    instruction=formatted_scan,
                    cwd=cwd,
                    verbose=verbose,
                    quiet=quiet,
                    timeout=timeout_2b,
                    label="step2b",
                    max_retries=DEFAULT_MAX_RETRIES,
                )

                total_cost += scan_cost
                model_used = scan_model
                state["total_cost"] = total_cost

                context["step2b_output"] = scan_output
                state["step_outputs"]["2b"] = scan_output
                state["last_completed_step"] = 2.5

                save_result = save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
                if save_result:
                    github_comment_id = save_result
                    state["github_comment_id"] = github_comment_id

                if not quiet:
                    console.print("   → Codebase scan complete")
            else:
                if not quiet:
                    console.print(f"[yellow]Warning: Missing template {scan_template_name}, skipping 2b[/yellow]")
                context["step2b_output"] = "No codebase scan performed (template missing)."

    # --- Step 5b: Early Completeness Gate (after Step 5, before Step 6) ---
    MAX_STEP5B_RETRIES = 3

    if state.get("last_completed_step", 0) >= 5 and start_step <= 6 and state.get("last_completed_step", 0) < 5.5:
        for attempt_5b in range(1, MAX_STEP5B_RETRIES + 1):
            if not quiet:
                attempt_str = f" (attempt {attempt_5b}/{MAX_STEP5B_RETRIES})" if attempt_5b > 1 else ""
                console.print(f"[bold][Step 5b/{TOTAL_STEPS}][/bold] Validating module design completeness{attempt_str}...")

            gate_template_name = "agentic_arch_step5b_completeness_gate_LLM"
            gate_template = load_prompt_template(gate_template_name)
            if not gate_template:
                if not quiet:
                    console.print(f"[yellow]Warning: Missing template {gate_template_name}, skipping 5b[/yellow]")
                break

            exclude_keys_5b = list(context.keys())
            gate_template = preprocess(gate_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys_5b)
            gate_template = gate_template.replace("{{", "{").replace("}}", "}")
            formatted_gate = gate_template
            for key, value in context.items():
                formatted_gate = formatted_gate.replace(f'{{{key}}}', str(value))

            timeout_5b = ARCH_STEP_TIMEOUTS.get(5.5, 600.0) + timeout_adder
            gate_success, gate_output, gate_cost, gate_model = run_agentic_task(
                instruction=formatted_gate,
                cwd=cwd,
                verbose=verbose,
                quiet=quiet,
                timeout=timeout_5b,
                label=f"step5b_attempt{attempt_5b}",
                max_retries=DEFAULT_MAX_RETRIES,
            )

            total_cost += gate_cost
            model_used = gate_model
            state["total_cost"] = total_cost

            if _check_validation_result(gate_output):
                if not quiet:
                    console.print("   → Module design completeness validated ✓")
                state["last_completed_step"] = 5.5
                save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
                break

            # Validation failed - try to fix if not last attempt
            if attempt_5b < MAX_STEP5B_RETRIES:
                if not quiet:
                    console.print("   → Module design gaps found, fixing...")

                fix_template_name = "agentic_arch_step5b_fix_LLM"
                fix_template = load_prompt_template(fix_template_name)
                if fix_template:
                    context["step5b_validation_output"] = gate_output
                    exclude_keys_fix = list(context.keys())
                    fix_template = preprocess(fix_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys_fix)
                    fix_template = fix_template.replace("{{", "{").replace("}}", "}")
                    formatted_fix = fix_template
                    for key, value in context.items():
                        formatted_fix = formatted_fix.replace(f'{{{key}}}', str(value))

                    fix_timeout = ARCH_STEP_TIMEOUTS.get(5.5, 600.0) + timeout_adder
                    fix_success, fix_output, fix_cost, fix_model = run_agentic_task(
                        instruction=formatted_fix,
                        cwd=cwd,
                        verbose=verbose,
                        quiet=quiet,
                        timeout=fix_timeout,
                        label=f"step5b_fix{attempt_5b}",
                        max_retries=DEFAULT_MAX_RETRIES,
                    )

                    total_cost += fix_cost
                    model_used = fix_model
                    state["total_cost"] = total_cost

                    # Replace step5_output with corrected design
                    context["step5_output"] = fix_output
                    state["step_outputs"]["5"] = fix_output

                    if not quiet:
                        console.print("   → Module design updated with missing modules")
            else:
                # Exhausted retries - hard stop
                if not quiet:
                    console.print(f"[red]⏹️  Module design incomplete after {MAX_STEP5B_RETRIES} attempts. Stopping.[/red]")
                save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
                return False, "Module design incomplete - completeness gate failed after max retries", total_cost, model_used, []

    # --- Run Steps 6-8: Dependencies, Generation, and .pddrc ---
    for step_num, name, description in steps_6_8:
        if step_num < start_step:
            continue

        if not quiet:
            console.print(f"[bold][Step {step_num}/{TOTAL_STEPS}][/bold] {description}...")

        template_name = f"agentic_arch_step{step_num}_{name}_LLM"
        prompt_template = load_prompt_template(template_name)
        if not prompt_template:
            return False, f"Missing prompt template: {template_name}", total_cost, model_used, []

        exclude_keys = list(context.keys())
        prompt_template = preprocess(prompt_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys)
        prompt_template = prompt_template.replace("{{", "{").replace("}}", "}")
        formatted_prompt = prompt_template
        for key, value in context.items():
            formatted_prompt = formatted_prompt.replace(f'{{{key}}}', str(value))

        timeout = ARCH_STEP_TIMEOUTS.get(step_num, 340.0) + timeout_adder

        # Capture pre-hash for Step 7 to detect no-op (agent failed to create/modify arch)
        arch_file_step7 = base_dir / "architecture.json"
        pre_hash_step7 = (
            hashlib.md5(arch_file_step7.read_bytes()).hexdigest()
            if step_num == 7 and arch_file_step7.exists()
            else None
        )

        # Snapshot existing architecture before Step 7 for post-merge
        existing_arch_snapshot: Optional[List[dict]] = None
        if step_num == 7 and arch_file_step7.exists():
            try:
                existing_arch_snapshot = json.loads(
                    arch_file_step7.read_text(encoding="utf-8")
                )
                if not isinstance(existing_arch_snapshot, list):
                    existing_arch_snapshot = None
            except (json.JSONDecodeError, OSError):
                existing_arch_snapshot = None

        step_success, step_output, step_cost, step_model = run_agentic_task(
            instruction=formatted_prompt,
            cwd=cwd,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout,
            label=f"step{step_num}",
            max_retries=DEFAULT_MAX_RETRIES,
        )

        total_cost += step_cost
        model_used = step_model
        state["total_cost"] = total_cost
        state["model_used"] = model_used

        if not step_success and not quiet:
            console.print(f"[yellow]Warning: Step {step_num} reported failure but continuing...[/yellow]")

        # Special handling for Step 7 (generate)
        if step_num == 7:
            created_files = _parse_files_marker(step_output, "FILES_CREATED:")
            if created_files:
                verified_files = _verify_files_exist(cwd, created_files, quiet)
                for vf in verified_files:
                    if vf not in scaffolding_files:
                        scaffolding_files.append(vf)
                state["scaffolding_files"] = scaffolding_files
                if not quiet and verified_files:
                    scaffold_count = len([f for f in verified_files if f != "architecture.json"])
                    if scaffold_count > 0:
                        console.print(f"   → Scaffolding files created: {scaffold_count}")

            # Validate architecture.json (use base_dir so subproject arch is checked)
            arch_file = base_dir / "architecture.json"

            # Hash check: detect no-op (agent reformatted existing arch or failed to create)
            post_hash_step7 = (
                hashlib.md5(arch_file.read_bytes()).hexdigest()
                if arch_file.exists()
                else None
            )
            if pre_hash_step7 is not None and pre_hash_step7 == post_hash_step7:
                step_success = False
                step_output = "FAILED: Step 7 agent did not modify architecture.json (content unchanged)"
                if not quiet:
                    console.print(f"[red]Error: Step 7 produced no change to architecture.json — agent likely reformatted existing file[/red]")
            elif pre_hash_step7 is None and not arch_file.exists():
                step_success = False
                step_output = "FAILED: Step 7 agent did not create architecture.json"
                if not quiet:
                    console.print(f"[red]Error: Step 7 did not create architecture.json[/red]")
            elif arch_file.exists():
                try:
                    with open(arch_file, "r", encoding="utf-8") as f:
                        arch_content = f.read()
                    arch_data = json.loads(arch_content)
                    if not isinstance(arch_data, list):
                        raise ValueError("Architecture must be a JSON array")

                    # Post-Step-7 merge: merge new arch with snapshot
                    if existing_arch_snapshot is not None:
                        # Normalize before merge so merge_report added/updated match post-normalization filenames
                        normalize_architecture_filenames(existing_arch_snapshot)
                        normalize_architecture_filenames(arch_data)
                        merged_arch, merge_report = merge_architecture(
                            existing_arch=existing_arch_snapshot,
                            new_arch=arch_data,
                            issue_number=issue_number,
                            issue_url=issue_url,
                        )
                        # Issue #617: ensure filename mirrors filepath (idempotent after pre-merge normalize)
                        normalize_architecture_filenames(merged_arch)
                        # Write full merged architecture to disk
                        with open(arch_file, "w", encoding="utf-8") as f:
                            json.dump(merged_arch, f, indent=2, ensure_ascii=False)

                        # Use full merged architecture for downstream steps
                        step_output = json.dumps(merged_arch, indent=2)

                        if not quiet:
                            console.print(
                                f"   → architecture.json merged: "
                                f"{len(merge_report['added'])} added, "
                                f"{len(merge_report['updated'])} updated, "
                                f"{len(merge_report['unchanged'])} unchanged"
                            )

                        # Record in registry
                        record_generation(
                            project_root=cwd,
                            issue_number=issue_number,
                            issue_url=issue_url,
                            modules_added=merge_report["added"],
                            modules_updated=merge_report["updated"],
                            target_dir=target_dir,
                        )
                    else:
                        # Issue #617: ensure filename mirrors filepath before writing
                        normalize_architecture_filenames(arch_data)
                        with open(arch_file, "w", encoding="utf-8") as f:
                            json.dump(arch_data, f, indent=2, ensure_ascii=False)
                        step_output = json.dumps(arch_data, indent=2)
                        if not quiet:
                            console.print(f"   → architecture.json created with {len(arch_data)} modules")

                        # Record first generation in registry
                        module_filenames = [
                            m.get("filename", "") for m in arch_data
                            if m.get("filename")
                        ]
                        record_generation(
                            project_root=cwd,
                            issue_number=issue_number,
                            issue_url=issue_url,
                            modules_added=module_filenames,
                            modules_updated=[],
                            target_dir=target_dir,
                        )

                except (json.JSONDecodeError, ValueError) as e:
                    if not quiet:
                        console.print(f"[yellow]Warning: architecture.json issue: {e}[/yellow]")

        # Special handling for Step 8 (.pddrc generation)
        if step_num == 8:
            created_files = _parse_files_marker(step_output, "FILES_CREATED:")
            if created_files:
                verified_files = _verify_files_exist(cwd, created_files, quiet)
                for vf in verified_files:
                    if vf not in scaffolding_files:
                        scaffolding_files.append(vf)
                state["scaffolding_files"] = scaffolding_files

            # Verify .pddrc exists and is valid YAML
            pddrc_file = cwd / ".pddrc"
            if pddrc_file.exists():
                try:
                    import yaml
                    with open(pddrc_file, "r", encoding="utf-8") as f:
                        pddrc_content = f.read()
                    yaml.safe_load(pddrc_content)

                    # Safety net: restore any contexts the LLM dropped
                    if existing_pddrc:
                        _ensure_pddrc_contexts_preserved(
                            pddrc_file, existing_pddrc, quiet
                        )

                    if not quiet:
                        if existing_pddrc:
                            console.print(f"   → .pddrc merged with existing configuration")
                        else:
                            console.print(f"   → .pddrc created and validated")
                except Exception as e:
                    if not quiet:
                        console.print(f"[yellow]Warning: .pddrc issue: {e}[/yellow]")
            else:
                if not quiet:
                    console.print(f"[yellow]Warning: .pddrc was not created[/yellow]")

            # Guard: remove stray .pddrc from subdirectory
            if target_dir:
                stray_pddrc = base_dir / ".pddrc"
                if stray_pddrc.exists() and stray_pddrc != pddrc_file:
                    if not quiet:
                        console.print(
                            f"[yellow]Warning: Removing stray .pddrc from "
                            f"{target_dir}/ (must live at repo root)[/yellow]"
                        )
                    # If root .pddrc missing but stray exists, move it to root
                    if not pddrc_file.exists():
                        import shutil
                        shutil.move(str(stray_pddrc), str(pddrc_file))
                        if not quiet:
                            console.print("   → Moved stray .pddrc to repo root")
                    else:
                        stray_pddrc.unlink()

        context[f"step{step_num}_output"] = step_output

        # Issue #467: Only advance last_completed_step on success.
        if step_success:
            state["step_outputs"][str(step_num)] = step_output
            state["last_completed_step"] = step_num
        else:
            state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"

        save_result = save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
        if save_result:
            github_comment_id = save_result
            state["github_comment_id"] = github_comment_id

        if not quiet:
            lines = step_output.strip().split('\n')
            brief = lines[-1] if lines else "Done"
            if len(brief) > 80: brief = brief[:77] + "..."
            console.print(f"   → {escape(brief)}")
            if step_success:
                console.print(f"  → Step {step_num} complete.")

        # --- Step 7b: Architecture Self-Review (after Step 7) ---
        if step_num == 7 and step_success and start_step <= 7.5 and state.get("last_completed_step", 0) < 7.5:
            if not quiet:
                console.print(f"[bold][Step 7b/{TOTAL_STEPS}][/bold] Reviewing architecture consistency...")

            review_template_name = "agentic_arch_step7b_review_LLM"
            review_template = load_prompt_template(review_template_name)
            if review_template:
                exclude_keys_7b = list(context.keys())
                review_template = preprocess(review_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys_7b)
                review_template = review_template.replace("{{", "{").replace("}}", "}")
                formatted_review = review_template
                for key, value in context.items():
                    formatted_review = formatted_review.replace(f'{{{key}}}', str(value))

                timeout_7b = ARCH_STEP_TIMEOUTS.get(7.5, 340.0) + timeout_adder
                review_success, review_output, review_cost, review_model = run_agentic_task(
                    instruction=formatted_review,
                    cwd=cwd,
                    verbose=verbose,
                    quiet=quiet,
                    timeout=timeout_7b,
                    label="step7b",
                    max_retries=DEFAULT_MAX_RETRIES,
                )

                total_cost += review_cost
                model_used = review_model
                state["total_cost"] = total_cost

                context["step7b_output"] = review_output
                state["step_outputs"]["7b"] = review_output
                state["last_completed_step"] = 7.5

                # If architecture was fixed, apply scoped fixes from architecture_review.json
                if "REVIEW_RESULT: FIXED" in review_output:
                    arch_file = base_dir / "architecture.json"
                    review_file = base_dir / "architecture_review.json"
                    if review_file.exists() and arch_file.exists():
                        try:
                            with open(arch_file, "r", encoding="utf-8") as f:
                                current_arch = json.loads(f.read())
                            with open(review_file, "r", encoding="utf-8") as f:
                                review_modules = json.loads(f.read())
                            if isinstance(current_arch, list) and isinstance(review_modules, list):
                                # Index reviewed modules by filename
                                review_by_name = {
                                    m.get("filename", ""): m
                                    for m in review_modules if m.get("filename")
                                }
                                # Replace only matching modules in current arch
                                merged = []
                                for m in current_arch:
                                    fn = m.get("filename", "")
                                    if fn in review_by_name:
                                        merged.append(review_by_name.pop(fn))
                                    else:
                                        merged.append(m)
                                # Append any new modules from review
                                for m in review_by_name.values():
                                    merged.append(m)
                                with open(arch_file, "w", encoding="utf-8") as f:
                                    json.dump(merged, f, indent=2, ensure_ascii=False)
                                arch_content = json.dumps(merged, indent=2, ensure_ascii=False)
                                context["step7_output"] = arch_content
                                state["step_outputs"]["7"] = arch_content
                                if not quiet:
                                    console.print(f"   → Architecture review applied ({len(review_modules)} modules updated)")
                            # Clean up review file
                            review_file.unlink(missing_ok=True)
                        except (json.JSONDecodeError, ValueError, OSError) as e:
                            if not quiet:
                                console.print(f"[yellow]Warning: Could not apply architecture review: {e}[/yellow]")
                    elif arch_file.exists():
                        # Fallback: agent wrote fixes directly to architecture.json (legacy behavior)
                        # Re-read but do NOT trust blindly — validate module count
                        try:
                            with open(arch_file, "r", encoding="utf-8") as f:
                                arch_content = f.read()
                            arch_data = json.loads(arch_content)
                            if isinstance(arch_data, list):
                                # Safety: if module count dropped, restore from snapshot
                                snapshot_count = len(existing_arch_snapshot) if existing_arch_snapshot else 0
                                if len(arch_data) < snapshot_count:
                                    if not quiet:
                                        console.print(f"[yellow]Warning: Step 7b reduced modules from {snapshot_count} to {len(arch_data)} — restoring merged architecture[/yellow]")
                                    merged_content = state["step_outputs"].get("7", "")
                                    if merged_content:
                                        with open(arch_file, "w", encoding="utf-8") as f:
                                            f.write(merged_content)
                                else:
                                    context["step7_output"] = arch_content
                                    state["step_outputs"]["7"] = arch_content
                                    if not quiet:
                                        console.print("   → Architecture fixed, updated context")
                        except (json.JSONDecodeError, ValueError):
                            pass

                save_result = save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
                if save_result:
                    github_comment_id = save_result
                    state["github_comment_id"] = github_comment_id

                if not quiet:
                    if "REVIEW_RESULT: CLEAN" in review_output:
                        console.print("   → Architecture review passed ✓")
                    elif "REVIEW_RESULT: FIXED" in review_output:
                        console.print("   → Architecture issues found and fixed")
                    else:
                        console.print("   → Architecture review complete")
            else:
                if not quiet:
                    console.print(f"[yellow]Warning: Missing template {review_template_name}, skipping 7b[/yellow]")

    # --- Step 8.5: Generate Shared Context Documents ---
    if (
        not skip_prompts
        and state.get("last_completed_step", 0) >= 8
        and state.get("last_completed_step", 0) < 8.5
    ):
        # Read existing context docs so the LLM can merge rather than regenerate
        existing_ctx_parts = []
        ctx_dir = base_dir / "prompts" / "_context"
        for ctx_filename in ("data_dictionary.yaml", "api_contracts.yaml", "integration_points.yaml"):
            ctx_file = ctx_dir / ctx_filename
            if ctx_file.exists():
                try:
                    with open(ctx_file, "r", encoding="utf-8") as f:
                        existing_ctx_parts.append(f"--- {ctx_filename} ---\n{f.read()}")
                except OSError as e:
                    if not quiet:
                        console.print(f"[yellow]Warning: Failed to read existing context doc {ctx_filename}: {e}[/yellow]")
        if existing_ctx_parts:
            context["existing_context_docs"] = "\n\n".join(existing_ctx_parts)
        else:
            context["existing_context_docs"] = ""

        if not quiet:
            console.print(f"[bold][Step 8.5/{TOTAL_STEPS}][/bold] Generating shared context documents...")

        ctx_template_name = "agentic_arch_step8_5_context_docs_LLM"
        ctx_template = load_prompt_template(ctx_template_name)
        if ctx_template:
            exclude_keys_8_5 = list(context.keys())
            ctx_template = preprocess(ctx_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys_8_5)
            ctx_template = ctx_template.replace("{{", "{").replace("}}", "}")
            formatted_ctx = ctx_template
            for key, value in context.items():
                formatted_ctx = formatted_ctx.replace(f'{{{key}}}', str(value))

            timeout_8_5 = ARCH_STEP_TIMEOUTS.get(8.5, 600.0) + timeout_adder
            ctx_success, ctx_output, ctx_cost, ctx_model = run_agentic_task(
                instruction=formatted_ctx,
                cwd=cwd,
                verbose=verbose,
                quiet=quiet,
                timeout=timeout_8_5,
                label="step8_5",
                max_retries=DEFAULT_MAX_RETRIES,
            )

            total_cost += ctx_cost
            model_used = ctx_model
            state["total_cost"] = total_cost

            context["step8_5_output"] = ctx_output
            state["step_outputs"]["8_5"] = ctx_output
            state["last_completed_step"] = 8.5

            # Track created context files
            created_ctx_files = _parse_files_marker(ctx_output, "FILES_CREATED:")
            if created_ctx_files:
                verified_ctx = _verify_files_exist(cwd, created_ctx_files, quiet)
                for cf in verified_ctx:
                    if cf not in scaffolding_files:
                        scaffolding_files.append(cf)
                state["scaffolding_files"] = scaffolding_files
                if not quiet and verified_ctx:
                    console.print(f"   → Context documents created: {len(verified_ctx)}")

            # Verify key context file exists
            data_dict_path = base_dir / "prompts" / "_context" / "data_dictionary.yaml"
            if data_dict_path.exists():
                if not quiet:
                    console.print("   → Data dictionary verified ✓")
            elif not quiet:
                console.print("[yellow]Warning: data_dictionary.yaml was not created[/yellow]")

            save_result = save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
            if save_result:
                github_comment_id = save_result
                state["github_comment_id"] = github_comment_id
        else:
            if not quiet:
                console.print(f"[yellow]Warning: Missing template {ctx_template_name}, skipping 8.5[/yellow]")
            state["last_completed_step"] = 8.5
            save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)

    # --- Step 9: Prompt Generation ---
    if not skip_prompts and start_step <= 9:
        if not quiet:
            console.print(f"[bold][Step 9/{TOTAL_STEPS}][/bold] Generating prompt files...")

        pddrc_path = cwd / ".pddrc"
        pddrc_content = ""
        if pddrc_path.exists():
            try:
                with open(pddrc_path, "r", encoding="utf-8") as f:
                    pddrc_content = f.read()
            except Exception as e:
                if not quiet:
                    console.print(f"[yellow]Warning: Could not read .pddrc: {e}[/yellow]")
        else:
            if not quiet:
                console.print(f"[yellow]Warning: .pddrc not found. Step 8 may have failed.[/yellow]")

        context["pddrc_content"] = pddrc_content

        template_name_9 = "agentic_arch_step9_prompts_LLM"
        prompt_template_9 = load_prompt_template(template_name_9)
        if not prompt_template_9:
            return False, f"Missing prompt template: {template_name_9}", total_cost, model_used, []

        # Preprocess to expand <include> tags and escape curly braces
        exclude_keys_9 = list(context.keys())
        prompt_template_9 = preprocess(prompt_template_9, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys_9)

        # Safe substitution (Issue #549): un-double template braces first, then substitute.
        prompt_template_9 = prompt_template_9.replace("{{", "{").replace("}}", "}")
        formatted_prompt_9 = prompt_template_9
        for key, value in context.items():
            formatted_prompt_9 = formatted_prompt_9.replace(f'{{{key}}}', str(value))

        timeout_9 = ARCH_STEP_TIMEOUTS.get(9, 900.0) + timeout_adder

        success_9, output_9, cost_9, model_9 = run_agentic_task(
            instruction=formatted_prompt_9,
            cwd=cwd,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout_9,
            label="step9",
            max_retries=DEFAULT_MAX_RETRIES,
        )

        total_cost += cost_9
        model_used = model_9
        state["total_cost"] = total_cost

        # Track created prompt files
        created_prompts = _parse_files_marker(output_9, "FILES_CREATED:")
        if created_prompts:
            verified_prompts = _verify_files_exist(cwd, created_prompts, quiet)
            prompt_files = verified_prompts
            state["prompt_files"] = prompt_files
            if not quiet and verified_prompts:
                console.print(f"   → Prompt files generated: {len(verified_prompts)}")

        context["step9_output"] = output_9
        state["step_outputs"]["9"] = output_9
        state["last_completed_step"] = 9

        save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)

        # --- Post-Step-9: Validate embedded code block syntax in prompts ---
        syntax_errors = _validate_generated_test_syntax(cwd)
        if syntax_errors and not quiet:
            console.print("[yellow]Warning: Syntax issues in embedded code blocks:[/yellow]")
            for err in syntax_errors:
                console.print(f"   [yellow]• {escape(err)}[/yellow]")

    # --- Step 9b: Cross-File Consistency Audit ---
    if not skip_prompts and state.get("last_completed_step", 0) >= 9 and state.get("last_completed_step", 0) < 9.5:
        if not quiet:
            console.print(f"[bold][Step 9b/{TOTAL_STEPS}][/bold] Cross-file consistency audit...")

        audit_template_name = "agentic_arch_step9b_cross_audit_LLM"
        audit_template = load_prompt_template(audit_template_name)
        if audit_template:
            # Ensure pddrc_content is in context
            if "pddrc_content" not in context:
                pddrc_path = cwd / ".pddrc"
                if pddrc_path.exists():
                    try:
                        with open(pddrc_path, "r", encoding="utf-8") as f:
                            context["pddrc_content"] = f.read()
                    except Exception:
                        context["pddrc_content"] = ""
                else:
                    context["pddrc_content"] = ""

            exclude_keys_9b = list(context.keys())
            audit_template = preprocess(audit_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys_9b)
            audit_template = audit_template.replace("{{", "{").replace("}}", "}")
            formatted_audit = audit_template
            for key, value in context.items():
                formatted_audit = formatted_audit.replace(f'{{{key}}}', str(value))

            timeout_9b = ARCH_STEP_TIMEOUTS.get(9.5, 600.0) + timeout_adder
            audit_success, audit_output, audit_cost, audit_model = run_agentic_task(
                instruction=formatted_audit,
                cwd=cwd,
                verbose=verbose,
                quiet=quiet,
                timeout=timeout_9b,
                label="step9b",
                max_retries=DEFAULT_MAX_RETRIES,
            )

            total_cost += audit_cost
            model_used = audit_model
            state["total_cost"] = total_cost

            context["step9b_output"] = audit_output
            state["step_outputs"]["9b"] = audit_output
            state["last_completed_step"] = 9.5

            # Track modified prompt files
            if "AUDIT_RESULT: INCONSISTENT" in audit_output:
                modified_prompts = _parse_files_marker(audit_output, "FILES_MODIFIED:")
                if modified_prompts:
                    verified_modified = _verify_files_exist(cwd, modified_prompts, quiet)
                    for mp in verified_modified:
                        if mp not in prompt_files:
                            prompt_files.append(mp)
                    state["prompt_files"] = prompt_files
                if not quiet:
                    console.print("   → Inconsistencies found and fixed")
            elif not quiet:
                console.print("   → All prompt files are consistent ✓")

            save_result = save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
            if save_result:
                github_comment_id = save_result
                state["github_comment_id"] = github_comment_id
        else:
            if not quiet:
                console.print(f"[yellow]Warning: Missing template {audit_template_name}, skipping 9b[/yellow]")
            state["last_completed_step"] = 9.5
            save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)

    # --- Step 9c: Cross-Sub-Issue Reconciliation ---
    if (
        not skip_prompts
        and related_issues
        and state.get("last_completed_step", 0) >= 9.5
        and state.get("last_completed_step", 0) < 9.7
    ):
        if not quiet:
            console.print(f"[bold][Step 9c/{TOTAL_STEPS}][/bold] Cross-sub-issue reconciliation...")

        reconcile_template_name = "cross_issue_reconcile_LLM"
        reconcile_template = load_prompt_template(reconcile_template_name)
        if reconcile_template:
            exclude_keys_9c = list(context.keys())
            reconcile_template = preprocess(reconcile_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys_9c)
            reconcile_template = reconcile_template.replace("{{", "{").replace("}}", "}")
            formatted_reconcile = reconcile_template
            for key, value in context.items():
                formatted_reconcile = formatted_reconcile.replace(f'{{{key}}}', str(value))

            timeout_9c = ARCH_STEP_TIMEOUTS.get(9.7, 600.0) + timeout_adder
            reconcile_success, reconcile_output, reconcile_cost, reconcile_model = run_agentic_task(
                instruction=formatted_reconcile,
                cwd=cwd,
                verbose=verbose,
                quiet=quiet,
                timeout=timeout_9c,
                label="step9c",
                max_retries=DEFAULT_MAX_RETRIES,
            )

            total_cost += reconcile_cost
            model_used = reconcile_model
            state["total_cost"] = total_cost

            context["step9c_output"] = reconcile_output
            state["step_outputs"]["9c"] = reconcile_output
            state["last_completed_step"] = 9.7

            if "RECONCILE_RESULT: CONFLICTS_FIXED" in reconcile_output:
                modified_files_9c = _parse_files_marker(reconcile_output, "FILES_MODIFIED:")
                if modified_files_9c:
                    verified_9c = _verify_files_exist(cwd, modified_files_9c, quiet)
                    for mf in verified_9c:
                        if mf not in prompt_files:
                            prompt_files.append(mf)
                    state["prompt_files"] = prompt_files
                if not quiet:
                    console.print("   → Cross-issue conflicts found and fixed")
            elif not quiet:
                console.print("   → All sub-issues are consistent ✓")

            save_result = save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
            if save_result:
                github_comment_id = save_result
                state["github_comment_id"] = github_comment_id
        else:
            if not quiet:
                console.print(f"[yellow]Warning: Missing template {reconcile_template_name}, skipping 9c[/yellow]")
            state["last_completed_step"] = 9.7
            save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
    elif (
        not skip_prompts
        and not related_issues
        and state.get("last_completed_step", 0) >= 9.5
        and state.get("last_completed_step", 0) < 9.7
    ):
        # No related issues — skip 9c cleanly
        state["last_completed_step"] = 9.7
        save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)

    # --- Validation Steps (10-12) with In-Place Fixing ---
    # Design: Each validation step retries with fixes up to MAX_STEP_RETRIES times.
    # Once a step passes, we move to the next step and don't re-validate previous steps.
    # This prevents the loop where fixing step 11 breaks step 10.
    MAX_STEP_RETRIES = 3

    validation_success = True  # Assume success, set to False if any step fails

    if not skip_prompts:

        # Helper function to run a validation step with retries
        def _run_validation_with_fix(
            step_num: int,
            step_name: str,
            template_name: str,
            fix_template_name: str,
            description: str
        ) -> bool:
            """Run a validation step, fixing in-place if it fails."""
            nonlocal total_cost, model_used, scaffolding_files, prompt_files

            for attempt in range(1, MAX_STEP_RETRIES + 1):
                if not quiet:
                    attempt_str = f" (attempt {attempt}/{MAX_STEP_RETRIES})" if attempt > 1 else ""
                    console.print(f"[bold][Step {step_num}/{TOTAL_STEPS}][/bold] {description}{attempt_str}...")

                prompt_template = load_prompt_template(template_name)
                if not prompt_template:
                    if not quiet:
                        console.print(f"[yellow]Warning: Missing template {template_name}[/yellow]")
                    return True  # Skip this validation if template missing

                # Preprocess to expand <include> tags and escape curly braces
                exclude_keys_val = list(context.keys())
                prompt_template = preprocess(prompt_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys_val)

                # Safe substitution (Issue #549): un-double template braces first, then substitute.
                prompt_template = prompt_template.replace("{{", "{").replace("}}", "}")
                formatted_prompt = prompt_template
                for key, value in context.items():
                    formatted_prompt = formatted_prompt.replace(f'{{{key}}}', str(value))
                timeout = ARCH_STEP_TIMEOUTS.get(step_num, 600.0) + timeout_adder

                success, output, cost, model = run_agentic_task(
                    instruction=formatted_prompt,
                    cwd=cwd,
                    verbose=verbose,
                    quiet=quiet,
                    timeout=timeout,
                    label=f"step{step_num}_attempt{attempt}",
                    max_retries=DEFAULT_MAX_RETRIES,
                )

                total_cost += cost
                model_used = model
                context[f"step{step_num}_output"] = output

                if _check_validation_result(output):
                    if not quiet:
                        console.print(f"   → {step_name} validated ✓")
                    return True

                # Validation failed - try to fix if not last attempt
                if attempt < MAX_STEP_RETRIES:
                    if not quiet:
                        console.print(f"   → {step_name} issues found, fixing...")

                    # Run fix step
                    fix_template = load_prompt_template(fix_template_name)
                    if fix_template:
                        context["failed_validation_step"] = step_name.lower()
                        context["failed_validation_output"] = output

                        # Preprocess to expand <include> tags and escape curly braces
                        exclude_keys_fix = list(context.keys())
                        fix_template = preprocess(fix_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys_fix)

                        # Safe substitution (Issue #549): un-double template braces first, then substitute.
                        fix_template = fix_template.replace("{{", "{").replace("}}", "}")
                        formatted_fix = fix_template
                        for key, value in context.items():
                            formatted_fix = formatted_fix.replace(f'{{{key}}}', str(value))
                        fix_timeout = ARCH_STEP_TIMEOUTS.get(13, 900.0) + timeout_adder

                        fix_success, fix_output, fix_cost, fix_model = run_agentic_task(
                            instruction=formatted_fix,
                            cwd=cwd,
                            verbose=verbose,
                            quiet=quiet,
                            timeout=fix_timeout,
                            label=f"step{step_num}_fix{attempt}",
                            max_retries=DEFAULT_MAX_RETRIES,
                        )

                        total_cost += fix_cost
                        model_used = fix_model
                        state["total_cost"] = total_cost

                        # Track modified files
                        modified_files = _parse_files_marker(fix_output, "FILES_MODIFIED:")
                        if modified_files:
                            verified_modified = _verify_files_exist(cwd, modified_files, quiet)
                            for mf in verified_modified:
                                if mf not in scaffolding_files and mf != "architecture.json":
                                    scaffolding_files.append(mf)
                            new_prompts = [f for f in verified_modified if f.endswith(".prompt")]
                            for np in new_prompts:
                                if np not in prompt_files:
                                    prompt_files.append(np)
                            state["scaffolding_files"] = scaffolding_files
                            state["prompt_files"] = prompt_files
                            if not quiet:
                                console.print(f"   → Fixed: {len(verified_modified)} files modified")

                        # Re-read architecture.json after fix (use base_dir for subproject)
                        arch_file = base_dir / "architecture.json"
                        if arch_file.exists():
                            try:
                                with open(arch_file, "r", encoding="utf-8") as f:
                                    arch_content = f.read()
                                arch_data = json.loads(arch_content)
                                if isinstance(arch_data, list):
                                    context["step7_output"] = arch_content
                            except (json.JSONDecodeError, ValueError):
                                pass

                else:
                    if not quiet:
                        console.print(f"   → {step_name} still failing after {MAX_STEP_RETRIES} attempts")
                    return False

            return False

        # --- Step 10: Completeness Validation ---
        if not _run_validation_with_fix(
            10, "Completeness", "agentic_arch_step10_completeness_LLM",
            "agentic_arch_step13_fix_LLM", "Validating architecture completeness"
        ):
            validation_success = False
            if not quiet:
                console.print("[yellow]Warning: Completeness validation failed, continuing anyway...[/yellow]")

        # --- Step 11: Sync Validation ---
        if not _run_validation_with_fix(
            11, "Sync", "agentic_arch_step11_sync_LLM",
            "agentic_arch_step13_fix_LLM", "Validating sync configuration (pdd sync --dry-run)"
        ):
            validation_success = False
            if not quiet:
                console.print("[yellow]Warning: Sync validation failed, continuing anyway...[/yellow]")

        # --- Step 12: Dependency Validation ---
        if not _run_validation_with_fix(
            12, "Dependencies", "agentic_arch_step12_deps_LLM",
            "agentic_arch_step13_fix_LLM", "Validating prompt dependencies (preprocess)"
        ):
            validation_success = False
            if not quiet:
                console.print("[yellow]Warning: Dependency validation failed, continuing anyway...[/yellow]")

        if validation_success and not quiet:
            console.print("   → All validations passed!")

    # --- Post-Processing ---
    final_architecture = context.get("step7_output", "")
    output_files = _save_architecture_files(base_dir, final_architecture, issue_title)

    # Add scaffolding files to output list
    for sf in scaffolding_files:
        sf_path = str(cwd / sf)
        if sf_path not in output_files and sf != "architecture.json":
            output_files.append(sf_path)

    # Add prompt files to output list
    for pf in prompt_files:
        pf_path = str(cwd / pf)
        if pf_path not in output_files:
            output_files.append(pf_path)

    if not quiet:
        console.print("\n[green]✅ Architecture generation complete[/green]")
        console.print(f"   Total cost: ${total_cost:.4f}")
        console.print(f"   Output files:")

        arch_files = [f for f in output_files if "architecture" in f.lower()]
        pddrc_files = [f for f in output_files if ".pddrc" in f]
        prompt_out_files = [f for f in output_files if ".prompt" in f]
        other_files = [f for f in output_files if f not in arch_files and f not in pddrc_files and f not in prompt_out_files]

        for f in arch_files + pddrc_files:
            console.print(f"     - {f}")
        if prompt_out_files:
            console.print(f"     - {len(prompt_out_files)} prompt file(s) in prompts/")
        for f in other_files:
            console.print(f"     - {f}")

    # Issue #624: Validation failures should block generation
    if not validation_success:
        return False, "Architecture generation failed: validation errors detected", total_cost, model_used, output_files

    # Clear state on success
    clear_workflow_state(cwd, issue_number, "architecture", state_dir, repo_owner, repo_name, use_github_state)

    return True, "Architecture generated successfully", total_cost, model_used, output_files
