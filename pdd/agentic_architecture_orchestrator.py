"""
Orchestrator for the 11-step agentic architecture workflow.
Runs each step as a separate agentic task, accumulates context between steps,
tracks overall progress and cost, and supports resuming from saved state.

Steps 1-6: Analysis and generation (architecture.json, scaffolding)
Step 7: Generate and validate .pddrc configuration
Step 8: Prompt generation
Steps 9-11: Validation with in-place fixing (completeness, sync, dependencies)

Each validation step (9-11) retries up to 3 times with fixes before moving to next.
Once a step passes, we don't re-validate it (prevents fix loops).
"""

from __future__ import annotations

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
    DEFAULT_MAX_RETRIES,
)
from pdd.load_prompt_template import load_prompt_template
from pdd.preprocess import preprocess
# Import render_mermaid dynamically or assume it's available in the package
try:
    from pdd.render_mermaid import generate_mermaid_code, generate_html
    HAS_MERMAID = True
except ImportError:
    HAS_MERMAID = False

# Initialize console for rich output
console = Console()

# Per-Step Timeouts (Workflow specific)
ARCH_STEP_TIMEOUTS: Dict[int, float] = {
    1: 340.0,   # Analyze PRD
    2: 340.0,   # Deep Analysis
    3: 600.0,   # Research
    4: 600.0,   # Design
    5: 600.0,   # Research Dependencies
    6: 1000.0,  # Generate (architecture.json + scaffolding)
    7: 600.0,   # Generate and validate .pddrc
    8: 900.0,   # Generate prompts
    9: 340.0,   # Validate completeness
    10: 600.0,  # Validate sync (pdd sync --dry-run for each module)
    11: 600.0,  # Validate dependencies (preprocess)
    12: 900.0,  # Fix all validation errors
}

MAX_VALIDATION_ITERATIONS = 5


def _check_hard_stop(step_num: int, output: str) -> Optional[str]:
    """Check output for hard stop conditions."""
    if step_num == 1 and "PRD Content Insufficient" in output:
        return "PRD insufficient"
    if step_num == 2 and "Tech Stack Ambiguous" in output:
        return "Tech stack ambiguous"
    if step_num == 4 and "Clarification Needed" in output:
        return "Clarification needed"
    return None


def _get_state_dir(cwd: Path) -> Path:
    """Get the state directory relative to git root or cwd."""
    return cwd / ".pdd" / "arch-state"


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

        with open(json_path, "w", encoding="utf-8") as f:
            json.dump(arch_data, f, indent=2)
        output_files.append(str(json_path))

        if HAS_MERMAID:
            mermaid_code = generate_mermaid_code(arch_data, issue_title)
            html_content = generate_html(mermaid_code, arch_data, issue_title)

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
    skip_prompts: bool = False
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Orchestrates the 11-step agentic architecture workflow.

    Steps 1-6: Analysis and generation (architecture.json, scaffolding)
    Step 7: Generate and validate .pddrc configuration
    Step 8: Prompt generation
    Steps 9-11: Validation with in-place fixing (completeness, sync, dependencies)

    Each validation step retries up to 3 times with fixes before moving to next step.
    Once a step passes, we don't re-validate it (prevents fix loops).

    Args:
        skip_prompts: If True, skip Step 8 and validation steps 9-11.

    Returns:
        (success, final_message, total_cost, model_used, output_files)
    """

    if not quiet:
        console.print(f"Generating architecture for issue #{issue_number}: \"{issue_title}\"")

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
    else:
        state = {"step_outputs": {}}
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
    }

    # Populate context with previous step outputs
    for s_key, s_out in step_outputs.items():
        context[f"step{s_key}_output"] = s_out

    # Track scaffolding files created during generation
    scaffolding_files: List[str] = state.get("scaffolding_files", [])
    prompt_files: List[str] = state.get("prompt_files", [])

    # Determine start step
    start_step = last_completed_step + 1

    # Handle resume logic
    if last_completed_step >= 8:
        # If we finished step 8 or later, start at validation loop (step 9)
        start_step = 9
        if not quiet:
            console.print(f"Resuming architecture generation for issue #{issue_number}")
            console.print(f"   Steps 1-8 already complete (cached)")
            console.print(f"   Starting Validation Loop (Step 9)")
    elif last_completed_step >= 7:
        # If we finished step 7, start at step 8 (prompt generation)
        start_step = 8
        if not quiet:
            console.print(f"Resuming architecture generation for issue #{issue_number}")
            console.print(f"   Steps 1-7 already complete (cached)")
            console.print(f"   Starting Step 8 (Prompt Generation)")
    elif last_completed_step >= 6:
        # If we finished step 6, start at step 7 (.pddrc generation)
        start_step = 7
        if not quiet:
            console.print(f"Resuming architecture generation for issue #{issue_number}")
            console.print(f"   Steps 1-6 already complete (cached)")
            console.print(f"   Starting Step 7 (.pddrc Generation)")
    elif last_completed_step > 0:
        if not quiet:
            console.print(f"Resuming architecture generation for issue #{issue_number}")
            console.print(f"   Steps 1-{last_completed_step} already complete (cached)")
            console.print(f"   Starting from Step {start_step}")

    # --- Steps 1-7: Analysis, Generation, and .pddrc ---
    steps_1_7 = [
        (1, "analyze_prd", "Extract features, tech stack, requirements from PRD"),
        (2, "analyze", "Deep analysis: module boundaries, shared concerns"),
        (3, "research", "Web research for tech stack docs and conventions"),
        (4, "design", "Design module breakdown with dependency graph"),
        (5, "research_deps", "Find API docs and code examples per module"),
        (6, "generate", "Generate architecture.json and scaffolding"),
        (7, "pddrc", "Generate and validate .pddrc configuration"),
    ]

    for step_num, name, description in steps_1_7:
        if step_num < start_step:
            continue

        if not quiet:
            console.print(f"[bold][Step {step_num}/12][/bold] {description}...")

        template_name = f"agentic_arch_step{step_num}_{name}_LLM"
        prompt_template = load_prompt_template(template_name)
        if not prompt_template:
            return False, f"Missing prompt template: {template_name}", total_cost, model_used, []

        # Preprocess to expand <include> tags and escape curly braces
        # Exclude context keys from escaping so they can be substituted
        exclude_keys = list(context.keys())
        prompt_template = preprocess(prompt_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys)

        try:
            formatted_prompt = prompt_template.format(**context)
        except KeyError as e:
            return False, f"Context missing key for step {step_num}: {e}", total_cost, model_used, []

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

        if not step_success:
            console.print(f"[yellow]Warning: Step {step_num} reported failure but continuing...[/yellow]")

        # Special handling for Step 6
        if step_num == 6:
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

            # Validate architecture.json
            arch_file = cwd / "architecture.json"
            if arch_file.exists():
                try:
                    with open(arch_file, "r", encoding="utf-8") as f:
                        arch_content = f.read()
                    arch_data = json.loads(arch_content)
                    if not isinstance(arch_data, list):
                        raise ValueError("Architecture must be a JSON array")
                    step_output = arch_content
                    if not quiet:
                        console.print(f"   → architecture.json created with {len(arch_data)} modules")
                except (json.JSONDecodeError, ValueError) as e:
                    if not quiet:
                        console.print(f"[yellow]Warning: architecture.json issue: {e}[/yellow]")

        # Special handling for Step 7 (.pddrc generation)
        if step_num == 7:
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
                    if not quiet:
                        console.print(f"   → .pddrc created and validated")
                except Exception as e:
                    if not quiet:
                        console.print(f"[yellow]Warning: .pddrc issue: {e}[/yellow]")
            else:
                if not quiet:
                    console.print(f"[yellow]Warning: .pddrc was not created[/yellow]")

        context[f"step{step_num}_output"] = step_output
        state["step_outputs"][str(step_num)] = step_output
        state["last_completed_step"] = step_num

        save_result = save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
        if save_result:
            github_comment_id = save_result
            state["github_comment_id"] = github_comment_id

        if not quiet:
            lines = step_output.strip().split('\n')
            brief = lines[-1] if lines else "Done"
            if len(brief) > 80: brief = brief[:77] + "..."
            console.print(f"   → {escape(brief)}")

    # --- Step 8: Prompt Generation ---
    if not skip_prompts and start_step <= 8:
        if not quiet:
            console.print(f"[bold][Step 8/12][/bold] Generating prompt files...")

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
                console.print(f"[yellow]Warning: .pddrc not found. Step 7 may have failed.[/yellow]")

        context["pddrc_content"] = pddrc_content

        template_name_8 = "agentic_arch_step8_prompts_LLM"
        prompt_template_8 = load_prompt_template(template_name_8)
        if not prompt_template_8:
            return False, f"Missing prompt template: {template_name_8}", total_cost, model_used, []

        # Preprocess to expand <include> tags and escape curly braces
        exclude_keys_8 = list(context.keys())
        prompt_template_8 = preprocess(prompt_template_8, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys_8)

        try:
            formatted_prompt_8 = prompt_template_8.format(**context)
        except KeyError as e:
            return False, f"Context missing key for step 8: {e}", total_cost, model_used, []

        timeout_8 = ARCH_STEP_TIMEOUTS.get(8, 900.0) + timeout_adder

        success_8, output_8, cost_8, model_8 = run_agentic_task(
            instruction=formatted_prompt_8,
            cwd=cwd,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout_8,
            label="step8",
            max_retries=DEFAULT_MAX_RETRIES,
        )

        total_cost += cost_8
        model_used = model_8
        state["total_cost"] = total_cost

        # Track created prompt files
        created_prompts = _parse_files_marker(output_8, "FILES_CREATED:")
        if created_prompts:
            verified_prompts = _verify_files_exist(cwd, created_prompts, quiet)
            prompt_files = verified_prompts
            state["prompt_files"] = prompt_files
            if not quiet and verified_prompts:
                console.print(f"   → Prompt files generated: {len(verified_prompts)}")

        context["step8_output"] = output_8
        state["step_outputs"]["8"] = output_8
        state["last_completed_step"] = 8

        save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)

    # --- Validation Steps (9-11) with In-Place Fixing ---
    # Design: Each validation step retries with fixes up to MAX_STEP_RETRIES times.
    # Once a step passes, we move to the next step and don't re-validate previous steps.
    # This prevents the loop where fixing step 10 breaks step 9.
    MAX_STEP_RETRIES = 3

    if not skip_prompts:
        validation_success = True  # Assume success, set to False if any step fails

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
                    console.print(f"[bold][Step {step_num}/11][/bold] {description}{attempt_str}...")

                prompt_template = load_prompt_template(template_name)
                if not prompt_template:
                    if not quiet:
                        console.print(f"[yellow]Warning: Missing template {template_name}[/yellow]")
                    return True  # Skip this validation if template missing

                # Preprocess to expand <include> tags and escape curly braces
                exclude_keys_val = list(context.keys())
                prompt_template = preprocess(prompt_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys_val)

                try:
                    formatted_prompt = prompt_template.format(**context)
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

                            try:
                                formatted_fix = fix_template.format(**context)
                                fix_timeout = ARCH_STEP_TIMEOUTS.get(12, 900.0) + timeout_adder

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

                                # Re-read architecture.json after fix
                                arch_file = cwd / "architecture.json"
                                if arch_file.exists():
                                    try:
                                        with open(arch_file, "r", encoding="utf-8") as f:
                                            arch_content = f.read()
                                        arch_data = json.loads(arch_content)
                                        if isinstance(arch_data, list):
                                            context["step6_output"] = arch_content
                                    except (json.JSONDecodeError, ValueError):
                                        pass

                            except KeyError as e:
                                if not quiet:
                                    console.print(f"[yellow]Warning: Fix context missing key: {e}[/yellow]")
                    else:
                        if not quiet:
                            console.print(f"   → {step_name} still failing after {MAX_STEP_RETRIES} attempts")
                        return False

                except KeyError as e:
                    if not quiet:
                        console.print(f"[yellow]Warning: Context missing key for step {step_num}: {e}[/yellow]")
                    return True  # Skip if context issue

            return False

        # --- Step 9: Completeness Validation ---
        if not _run_validation_with_fix(
            9, "Completeness", "agentic_arch_step9_completeness_LLM",
            "agentic_arch_step12_fix_LLM", "Validating architecture completeness"
        ):
            validation_success = False
            if not quiet:
                console.print("[yellow]Warning: Completeness validation failed, continuing anyway...[/yellow]")

        # --- Step 10: Sync Validation ---
        if not _run_validation_with_fix(
            10, "Sync", "agentic_arch_step10_sync_LLM",
            "agentic_arch_step12_fix_LLM", "Validating sync configuration (pdd sync --dry-run)"
        ):
            validation_success = False
            if not quiet:
                console.print("[yellow]Warning: Sync validation failed, continuing anyway...[/yellow]")

        # --- Step 11: Dependency Validation ---
        if not _run_validation_with_fix(
            11, "Dependencies", "agentic_arch_step11_deps_LLM",
            "agentic_arch_step12_fix_LLM", "Validating prompt dependencies (preprocess)"
        ):
            validation_success = False
            if not quiet:
                console.print("[yellow]Warning: Dependency validation failed, continuing anyway...[/yellow]")

        if validation_success and not quiet:
            console.print("   → All validations passed!")

    # --- Post-Processing ---
    final_architecture = context.get("step6_output", "")
    output_files = _save_architecture_files(cwd, final_architecture, issue_title)

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

    # Clear state on success
    clear_workflow_state(cwd, issue_number, "architecture", state_dir, repo_owner, repo_name, use_github_state)

    return True, "Architecture generated successfully", total_cost, model_used, output_files
