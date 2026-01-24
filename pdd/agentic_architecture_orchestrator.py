"""
Orchestrator for the 8-step agentic architecture workflow.
Runs each step as a separate agentic task, accumulates context between steps,
tracks overall progress and cost, and supports resuming from saved state.
Includes a validation loop (steps 7-8) to ensure architectural integrity.
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
    6: 1000.0,  # Generate
    7: 340.0,   # Validate
    8: 600.0,   # Fix
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
    # Ideally we find git root, but falling back to cwd/.pdd is acceptable if not in a repo
    return cwd / ".pdd" / "arch-state"


def _save_architecture_files(
    cwd: Path, 
    architecture_json_content: str, 
    issue_title: str
) -> List[str]:
    """
    Saves the architecture JSON and generates the Mermaid HTML diagram.
    Returns a list of generated file paths.
    """
    output_files = []
    
    # 1. Save architecture.json
    json_path = cwd / "architecture.json"
    try:
        # Ensure it's valid JSON before saving, or save raw if parsing fails
        # The agent should output valid JSON, but we might need to strip markdown code blocks
        clean_content = architecture_json_content.strip()
        if clean_content.startswith("```json"):
            clean_content = clean_content[7:]
        if clean_content.startswith("```"):
            clean_content = clean_content[3:]
        if clean_content.endswith("```"):
            clean_content = clean_content[:-3]
        
        # Validate JSON
        arch_data = json.loads(clean_content)
        
        with open(json_path, "w", encoding="utf-8") as f:
            json.dump(arch_data, f, indent=2)
        output_files.append(str(json_path))
        
        # 2. Generate Mermaid Diagram
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
        console.print("[red]Error: Failed to parse generated architecture as JSON. Saving raw output.[/red]")
        with open(json_path, "w", encoding="utf-8") as f:
            f.write(architecture_json_content)
        output_files.append(str(json_path))
    except Exception as e:
        console.print(f"[red]Error saving architecture files: {e}[/red]")

    return output_files


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
    use_github_state: bool = True
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Orchestrates the 8-step agentic architecture workflow.
    
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
        # If we are resuming inside the validation loop, we might need extra state
        # For simplicity, if we crashed in the loop, we restart the loop (step 7)
        # using the output from step 6 as the base.
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

    # Determine start step
    start_step = last_completed_step + 1
    
    # If we finished step 6, we enter the validation loop (Step 7)
    # If we finished step 7 or 8 previously, we restart the validation loop to be safe,
    # unless we marked the whole workflow as complete (which clears state).
    # So if state exists and last_completed_step >= 6, we force start at 7 to re-validate.
    if last_completed_step >= 6:
        start_step = 7
        if not quiet:
            console.print(f"Resuming architecture generation for issue #{issue_number}")
            console.print(f"   Steps 1-6 already complete (cached)")
            console.print(f"   Starting Validation Loop (Step 7)")
    elif last_completed_step > 0:
        if not quiet:
            console.print(f"Resuming architecture generation for issue #{issue_number}")
            console.print(f"   Steps 1-{last_completed_step} already complete (cached)")
            console.print(f"   Starting from Step {start_step}")

    steps_config = [
        (1, "analyze_prd", "Extract features, tech stack, requirements from PRD"),
        (2, "analyze", "Deep analysis: module boundaries, shared concerns"),
        (3, "research", "Web research for tech stack docs and conventions"),
        (4, "design", "Design module breakdown with dependency graph"),
        (5, "research_deps", "Find API docs and code examples per module"),
        (6, "generate", "Generate complete architecture.json"),
    ]

    # --- Sequential Steps 1-6 ---
    for step_num, name, description in steps_config:
        if step_num < start_step:
            continue

        if not quiet:
            console.print(f"[bold][Step {step_num}/8][/bold] {description}...")

        template_name = f"agentic_arch_step{step_num}_{name}_LLM"
        prompt_template = load_prompt_template(template_name)
        if not prompt_template:
            return False, f"Missing prompt template: {template_name}", total_cost, model_used, []

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

    # --- Validation Loop (Steps 7-8) ---
    
    # We need the architecture from step 6 to start validation
    current_architecture = context.get("step6_output", "")
    if not current_architecture:
        return False, "Missing Step 6 output (Architecture JSON)", total_cost, model_used, []

    validation_iteration = 0
    final_architecture = current_architecture
    validation_success = False

    while validation_iteration < MAX_VALIDATION_ITERATIONS:
        validation_iteration += 1
        
        # --- Step 7: Validate ---
        if not quiet:
            console.print(f"[bold][Step 7/8][/bold] Validating (iteration {validation_iteration}/{MAX_VALIDATION_ITERATIONS})...")
        
        # Update context with the architecture we are currently validating
        # Note: Step 7 prompt expects 'step6_output' or 'current_architecture'
        # We override step6_output in context to point to the *current* version for the prompt
        context["step6_output"] = current_architecture
        
        template_name_7 = "agentic_arch_step7_validate_LLM"
        prompt_template_7 = load_prompt_template(template_name_7)
        if not prompt_template_7:
            return False, f"Missing prompt template: {template_name_7}", total_cost, model_used, []
            
        formatted_prompt_7 = prompt_template_7.format(**context)
        
        timeout_7 = ARCH_STEP_TIMEOUTS.get(7, 340.0) + timeout_adder
        
        success_7, output_7, cost_7, model_7 = run_agentic_task(
            instruction=formatted_prompt_7,
            cwd=cwd,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout_7,
            label=f"step7_iter{validation_iteration}",
            max_retries=DEFAULT_MAX_RETRIES,
        )
        
        total_cost += cost_7
        model_used = model_7 # Update to latest model used
        state["total_cost"] = total_cost
        
        # Check if valid
        # Note: "INVALID" contains "VALID", so we must check for INVALID explicitly or ensure it's not present.
        if "INVALID" not in output_7 and "VALID" in output_7:
            if not quiet:
                console.print("   → Architecture validated successfully.")
            validation_success = True
            final_architecture = current_architecture
            break
        
        if not quiet:
            console.print("   → Validation issues found. Proceeding to fix...")

        # --- Step 8: Fix ---
        if not quiet:
            console.print(f"[bold][Step 8/8][/bold] Fixing validation errors (iteration {validation_iteration}/{MAX_VALIDATION_ITERATIONS})...")
            
        context["step7_output"] = output_7
        context["current_architecture"] = current_architecture
        
        template_name_8 = "agentic_arch_step8_fix_LLM"
        prompt_template_8 = load_prompt_template(template_name_8)
        if not prompt_template_8:
            return False, f"Missing prompt template: {template_name_8}", total_cost, model_used, []
            
        formatted_prompt_8 = prompt_template_8.format(**context)
        
        timeout_8 = ARCH_STEP_TIMEOUTS.get(8, 600.0) + timeout_adder
        
        success_8, output_8, cost_8, model_8 = run_agentic_task(
            instruction=formatted_prompt_8,
            cwd=cwd,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout_8,
            label=f"step8_iter{validation_iteration}",
            max_retries=DEFAULT_MAX_RETRIES,
        )
        
        total_cost += cost_8
        model_used = model_8
        state["total_cost"] = total_cost
        
        # The output of Step 8 is the new architecture JSON
        current_architecture = output_8
        
        # Save intermediate state (optional, but good for debugging costs)
        save_workflow_state(cwd, issue_number, "architecture", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)

    if not validation_success:
        console.print("[yellow]Warning: Maximum validation iterations reached. Using last generated architecture.[/yellow]")

    # --- Post-Processing ---
    output_files = _save_architecture_files(cwd, final_architecture, issue_title)

    if not quiet:
        console.print("\n[green]✅ Architecture generation complete[/green]")
        console.print(f"   Total cost: ${total_cost:.4f}")
        console.print(f"   Output files:")
        for f in output_files:
            console.print(f"     - {f}")

    # Clear state on success
    clear_workflow_state(cwd, issue_number, "architecture", state_dir, repo_owner, repo_name, use_github_state)

    return True, "Architecture generated successfully", total_cost, model_used, output_files