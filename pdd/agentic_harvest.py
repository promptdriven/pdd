from __future__ import annotations
import subprocess
from pathlib import Path
from typing import Optional

from .agentic_logging import info, always, print_head, AGENT_CALL_TIMEOUT
from .agentic_extract import begin_marker, end_marker, extract_files_from_output, extract_corrected_single, extract_python_code_block, normalize_code_text
from .agentic_io import apply_file_map
from .agentic_runners import run_openai_variants, run_anthropic_variants, run_google_variants, run_cli
from .load_prompt_template import load_prompt_template
from .agentic_verify import verify_and_log

def try_harvest_then_verify(
    provider: str,
    code_path: Path,
    unit_test_file: str,
    code_snapshot: str,
    test_content: str,
    error_content: str,
    cwd: Path,
    *,
    verify_cmd: Optional[str],
    verify_enabled: bool,
) -> bool:
    harvest_prompt_template = load_prompt_template("agentic_fix_harvest_only_LLM")
    if not harvest_prompt_template:
        info("[yellow]Failed to load harvest-only agent prompt template.[/yellow]")
        return False

    harvest_instr = harvest_prompt_template.format(
        code_abs=str(code_path),
        begin=begin_marker(code_path),
        end=end_marker(code_path),
        code_content=code_snapshot,
        test_content=test_content,
        error_content=error_content,
    )
    harvest_file = Path("agentic_fix_harvest.txt")
    harvest_file.write_text(harvest_instr, encoding="utf-8")
    info(f"[cyan]Executing {provider.capitalize()} with harvest-only instructions: {harvest_file.resolve()}[/cyan]")
    print_head("Harvest-only instruction preview", harvest_instr)

    try:
        if provider == "openai":
            res = run_openai_variants(harvest_instr, cwd, max(60, AGENT_CALL_TIMEOUT // 3), "harvest")
        elif provider == "anthropic":
            res = run_anthropic_variants(harvest_instr, cwd, max(60, AGENT_CALL_TIMEOUT // 3), "harvest")
        elif provider == "google":
            res = run_google_variants(harvest_instr, cwd, max(60, AGENT_CALL_TIMEOUT // 3), "harvest")
        else:
            res = run_cli([], cwd, max(60, AGENT_CALL_TIMEOUT // 2))
    except subprocess.TimeoutExpired:
        info(f"[yellow]{provider.capitalize()} harvest-only attempt timed out.[/yellow]")
        try:
            harvest_file.unlink()
        except Exception:
            pass
        return False

    print_head(f"{provider.capitalize()} harvest stdout", res.stdout or "")
    print_head(f"{provider.capitalize()} harvest stderr", res.stderr or "")

    allow_new = False

    multi = extract_files_from_output(res.stdout or "", res.stderr or "")
    if multi:
        info("[cyan]Applying multi-file harvest from agent output...[/cyan]")
        apply_file_map(multi, cwd, code_path, allow_new, normalize_code_text)
        if verify_and_log(unit_test_file, cwd, verify_cmd=verify_cmd, enabled=verify_enabled):
            always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
            try:
                harvest_file.unlink()
            except Exception:
                pass
            return True
        try:
            harvest_file.unlink()
        except Exception:
            pass
        return False

    harvested_single = extract_corrected_single(res.stdout or "", res.stderr or "", code_path.resolve())
    if harvested_single is None:
        if provider == "google":
            code_block = extract_python_code_block(res.stdout or "", res.stderr or "")
            if code_block:
                info("[cyan]No markers found, but detected a Python code block from Google. Applying it...[/cyan]")
                body_to_write = normalize_code_text(code_block)
                code_path.write_text(body_to_write, encoding="utf-8")
                newest = code_path.read_text(encoding="utf-8")
                if verify_and_log(unit_test_file, cwd, verify_cmd=verify_cmd, enabled=verify_enabled):
                    always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
                    try:
                        harvest_file.unlink()
                    except Exception:
                        pass
                    return True
                try:
                    harvest_file.unlink()
                except Exception:
                    pass
                return False
        info("[yellow]Harvest-only attempt did not include the required markers.[/yellow]")
        try:
            harvest_file.unlink()
        except Exception:
            pass
        return False

    info("[cyan]Applying harvested corrected file (single)...[/cyan]")
    body_to_write = normalize_code_text(harvested_single)
    code_path.write_text(body_to_write, encoding="utf-8")

    if verify_and_log(unit_test_file, cwd, verify_cmd=verify_cmd, enabled=verify_enabled):
        always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
        try:
            harvest_file.unlink()
        except Exception:
            pass
        return True

    try:
        harvest_file.unlink()
    except Exception:
        pass
    return False
