from __future__ import annotations
import os
import shutil
import subprocess
from pathlib import Path
from typing import Tuple, List, Optional

from .llm_invoke import _load_model_data
from .load_prompt_template import load_prompt_template
from .agentic_logging import info, always, print_head, AGENT_COST_PER_CALL, AGENT_CALL_TIMEOUT
from .agentic_extract import begin_marker, end_marker, extract_files_from_output, extract_corrected_single, extract_python_code_block, normalize_code_text
from .agentic_io import apply_file_map, print_diff
from .agentic_runners import run_openai_variants, run_anthropic_variants, run_google_variants, which_or_skip, run_cli
from .agentic_harvest import try_harvest_then_verify
from .agentic_verify import verify_and_log

AGENT_PROVIDER_PREFERENCE = ["anthropic", "google", "openai"]

def get_agent_command(provider: str, instruction_file: Path) -> List[str]:
    p = provider.lower()
    if p == "anthropic":
        return []
    if p == "google":
        return []
    if p == "openai":
        return ["codex", "exec", "--skip-git-repo-check"]
    return []

def find_llm_csv_path() -> Optional[Path]:
    home_path = Path.home() / ".pdd" / "llm_model.csv"
    project_path = Path.cwd() / ".pdd" / "llm_model.csv"
    if home_path.is_file():
        return home_path
    if project_path.is_file():
        return project_path
    return None

def run_agentic_fix(
    prompt_file: str,
    code_file: str,
    unit_test_file: str,
    error_log_file: str,
) -> Tuple[bool, str, float, str]:
    always("[bold yellow]Standard fix failed. Initiating agentic fallback (AGENT-ONLY)...[/bold yellow]")

    instruction_file: Optional[Path] = None
    est_cost: float = 0.0
    used_model: str = "agentic-cli"

    try:
        cwd = Path.cwd()
        info(f"[cyan]Project root (cwd): {cwd}[/cyan]")

        csv_path = find_llm_csv_path()
        model_df = _load_model_data(csv_path)

        available_agents: List[str] = []
        present_keys: List[str] = []
        seen = set()

        for provider in AGENT_PROVIDER_PREFERENCE:
            provider_df = model_df[model_df["provider"].str.lower() == provider]
            if provider_df.empty:
                continue
            api_key_name = provider_df.iloc[0]["api_key"]
            if not api_key_name:
                continue
            if os.getenv(api_key_name):
                present_keys.append(api_key_name)
                if provider not in seen:
                    available_agents.append(provider)
                    seen.add(provider)

        info(f"[cyan]Env API keys present (names only): {', '.join(present_keys) or 'none'}[/cyan]")
        if not available_agents:
            return False, "No configured agent API keys found in environment.", est_cost, used_model

        info(f"[cyan]Available agents found: {', '.join(available_agents)}[/cyan]")

        prompt_content = Path(prompt_file).read_text(encoding="utf-8")
        code_path = Path(code_file).resolve()
        orig_code = code_path.read_text(encoding="utf-8")
        test_content = Path(unit_test_file).read_text(encoding="utf-8")
        error_content = Path(error_log_file).read_text(encoding="utf-8")

        primary_prompt_template = load_prompt_template("agentic_fix_primary_LLM")
        if not primary_prompt_template:
            return False, "Failed to load primary agent prompt template.", est_cost, used_model

        primary_instr = primary_prompt_template.format(
            code_abs=str(code_path),
            test_abs=str(Path(unit_test_file).resolve()),
            begin=begin_marker(code_path),
            end=end_marker(code_path),
            prompt_content=prompt_content,
            code_content=orig_code,
            test_content=test_content,
            error_content=error_content,
        )
        instruction_file = Path("agentic_fix_instructions.txt")
        instruction_file.write_text(primary_instr, encoding="utf-8")
        info(f"[cyan]Instruction file: {instruction_file.resolve()} ({instruction_file.stat().st_size} bytes)[/cyan]")
        print_head("Instruction preview", primary_instr)

        ext = code_path.suffix.lower()
        is_python = ext == ".py"

        env_verify = os.getenv("PDD_AGENTIC_VERIFY", None)
        verify_force = os.getenv("PDD_AGENTIC_VERIFY_FORCE", "0") == "1"
        verify_cmd = os.getenv("PDD_AGENTIC_VERIFY_CMD", None)

        if verify_force:
            verify_enabled = True
        else:
            if is_python:
                verify_enabled = (env_verify is None and True) or (env_verify is not None and env_verify != "0")
            else:
                if env_verify is None:
                    verify_enabled = bool(verify_cmd)
                else:
                    verify_enabled = (env_verify != "0")

        allow_new = False

        for provider in available_agents:
            used_model = f"agentic-{provider}"
            cmd = get_agent_command(provider, instruction_file)
            binary = which_or_skip(provider, cmd)
            info(f"[cyan]Attempting fix with {provider.capitalize()} agent...[/cyan]")
            if binary is None:
                info(f"[yellow]Skipping {provider.capitalize()} (CLI not found in PATH).[/yellow]")
                continue

            if provider in ("google", "openai", "anthropic"):
                est_cost += AGENT_COST_PER_CALL
                try:
                    if try_harvest_then_verify(
                        provider,
                        code_path,
                        unit_test_file,
                        orig_code,
                        test_content,
                        error_content,
                        cwd,
                        verify_cmd=verify_cmd,
                        verify_enabled=verify_enabled,
                    ):
                        try:
                            instruction_file.unlink()
                        except Exception:
                            pass
                        return True, f"Agentic fix successful with {provider.capitalize()}.", est_cost, used_model
                except subprocess.TimeoutExpired:
                    info(f"[yellow]{provider.capitalize()} harvest attempt timed out, moving on...[/yellow]")
                info("[yellow]Harvest-first attempt did not pass; trying primary instruction path...[/yellow]")

            est_cost += AGENT_COST_PER_CALL
            try:
                if provider == "openai":
                    res = run_openai_variants(primary_instr, cwd, max(30, AGENT_CALL_TIMEOUT // 2), "primary")
                elif provider == "anthropic":
                    res = run_anthropic_variants(primary_instr, cwd, max(30, AGENT_CALL_TIMEOUT // 2), "primary")
                elif provider == "google":
                    res = run_google_variants(primary_instr, cwd, max(30, AGENT_CALL_TIMEOUT // 2), "primary")
                else:
                    res = run_cli(cmd, cwd, AGENT_CALL_TIMEOUT)
            except subprocess.TimeoutExpired:
                info(f"[yellow]{provider.capitalize()} agent timed out after {AGENT_CALL_TIMEOUT}s. Trying next...[/yellow]")
                continue

            print_head(f"{provider.capitalize()} stdout", res.stdout or "")
            print_head(f"{provider.capitalize()} stderr", res.stderr or "")

            multi = extract_files_from_output(res.stdout or "", res.stderr or "")
            if multi:
                info("[cyan]Detected multi-file corrected content (primary attempt). Applying...[/cyan]")
                apply_file_map(multi, cwd, code_path, allow_new, normalize_code_text)
            else:
                harvested = extract_corrected_single(res.stdout or "", res.stderr or "", code_path.resolve())
                if harvested is not None:
                    info("[cyan]Detected corrected file content in agent output (primary attempt). Applying patch...[/cyan]")
                    body_to_write = normalize_code_text(harvested)
                    code_path.write_text(body_to_write, encoding="utf-8")
                elif provider == "google":
                    code_block = extract_python_code_block(res.stdout or "", res.stderr or "")
                    if code_block:
                        info("[cyan]Detected a Python code block from Google (no markers). Applying patch...[/cyan]")
                        body_to_write = normalize_code_text(code_block)
                        code_path.write_text(body_to_write, encoding="utf-8")

            new_code = code_path.read_text(encoding="utf-8")
            print_diff(orig_code, new_code, code_path)

            proceed_to_verify = (res.returncode == 0) or (new_code != orig_code) or bool(multi)
            if proceed_to_verify:
                if verify_and_log(unit_test_file, cwd, verify_cmd=verify_cmd, enabled=verify_enabled):
                    always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
                    try:
                        instruction_file.unlink()
                    except Exception:
                        pass
                    return True, f"Agentic fix successful with {provider.capitalize()}.", est_cost, used_model

            orig_code = new_code
            info(f"[yellow]{provider.capitalize()} attempt did not yield a passing test. Trying next...[/yellow]")

        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, "All agents failed to produce a passing fix (no local fallback).", est_cost, used_model

    except FileNotFoundError as e:
        msg = f"A required file or command was not found: {e}. Is the agent CLI installed and in your PATH?"
        always(f"[bold red]Error:[/bold red] {msg}")
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, msg, 0.0, "agentic-cli"
    except Exception as e:
        always(f"[bold red]An unexpected error occurred during agentic fix:[/bold red] {e}")
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, str(e), 0.0, "agentic-cli"
