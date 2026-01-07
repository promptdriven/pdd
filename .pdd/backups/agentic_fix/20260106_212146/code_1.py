from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import difflib
import tempfile
import logging
from pathlib import Path
from typing import Tuple, List, Optional, Dict, Any

from .get_language import get_language_from_ext
from .get_run_command import get_run_command
from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .agentic_langtest import run_langtest_preflight
from .agentic_common import (
    setup_logging,
    parse_multi_file_markers,
    get_mtime_snapshot,
    detect_mtime_changes,
    AgentResult
)

logger = logging.getLogger(__name__)

# Provider selection order
AGENT_PROVIDER_PREFERENCE = ["anthropic", "google", "openai"]

_AGENT_COST_PER_CALL = float(os.getenv("PDD_AGENTIC_COST_PER_CALL", "0.02"))
_AGENT_CALL_TIMEOUT = int(os.getenv("PDD_AGENTIC_TIMEOUT", "240"))
_VERIFY_TIMEOUT = int(os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "120"))

def _begin_marker(path: Path) -> str:
    return f"<<<BEGIN_FILE:{path}>>>"

def _end_marker(path: Path) -> str:
    return f"<<<END_FILE:{path}>>>"

def _is_useless_error_content(content: str) -> bool:
    stripped = (content or "").strip()
    if not stripped:
        return True
    cleaned = re.sub(r"<[^>]+>\s*</[^>]+>", "", stripped).strip()
    if not cleaned:
        return True
    error_indicators = ["Error", "Exception", "Traceback", "failed", "FAILED", "error:"]
    return not any(ind in content for ind in error_indicators)

def _run_testcmd(cmd: str, cwd: Path) -> bool:
    try:
        proc = subprocess.run(
            ["bash", "-lc", cmd],
            capture_output=True,
            text=True,
            check=False,
            timeout=_VERIFY_TIMEOUT,
            cwd=str(cwd),
        )
        return proc.returncode == 0
    except Exception:
        return False

def _try_harvest_then_verify(
    provider: str,
    code_path: Path,
    unit_test_file: str,
    prompt_content: str,
    test_content: str,
    error_content: str,
    working_dir: Path,
    *,
    verify_cmd: Optional[str] = None,
    verbose: bool = False,
    quiet: bool = False,
) -> Tuple[bool, List[Path]]:
    harvest_prompt_template = load_prompt_template("agentic_fix_harvest_only_LLM")
    if not harvest_prompt_template:
        return False, []

    instr = harvest_prompt_template.format(
        code_abs=str(code_path),
        test_abs=str(Path(unit_test_file).resolve()),
        begin=_begin_marker(code_path),
        end=_end_marker(code_path),
        prompt_content=prompt_content,
        test_content=test_content,
        error_content=error_content,
        verify_cmd=verify_cmd or "No verification command provided.",
    )

    snapshot = get_mtime_snapshot(working_dir)
    response, cost, model = llm_invoke(instr)
    
    changed = parse_multi_file_markers(response, working_dir)
    direct = detect_mtime_changes(snapshot, working_dir)
    all_changed = list(set(changed + direct))

    success = False
    if all_changed:
        if verify_cmd:
            cmd = verify_cmd.replace("{test}", unit_test_file).replace("{cwd}", str(working_dir))
            success = _run_testcmd(cmd, working_dir)
        else:
            lang = get_language_from_ext(str(code_path))
            cmd = get_run_command(lang, unit_test_file)
            success = _run_testcmd(cmd, working_dir) if cmd else False

    return success, all_changed

def run_agentic_fix(
    prompt_file: str,
    code_file: str,
    unit_test_file: str,
    error_log_file: str,
    verify_cmd: Optional[str] = None,
    cwd: Optional[Path] = None,
    *,
    verbose: bool = False,
    quiet: bool = False,
) -> Tuple[bool, str, float, str, List[Path]]:
    setup_logging(verbose=verbose, quiet=quiet)
    working_dir = cwd or Path.cwd()
    
    est_cost = 0.0
    used_model = "agentic-fix"
    all_changed_files: List[Path] = []

    try:
        prompt_content = Path(prompt_file).read_text(encoding="utf-8")
        code_path = (working_dir / code_file).resolve()
        test_path = (working_dir / unit_test_file).resolve()
        
        orig_code = code_path.read_text(encoding="utf-8")
        orig_test = test_path.read_text(encoding="utf-8")
        
        error_log_path = Path(error_log_file)
        error_content = error_log_path.read_text(encoding="utf-8") if error_log_path.exists() else ""

        if _is_useless_error_content(error_content):
            rc, out = run_langtest_preflight(code_path, test_path, verify_cmd, working_dir)
            error_content = out
            error_log_path.write_text(error_content, encoding="utf-8")

        primary_template = load_prompt_template("agentic_fix_primary_LLM")
        if not primary_template:
            return False, "Missing primary template", 0.0, used_model, []

        for provider in AGENT_PROVIDER_PREFERENCE:
            # PRIMARY FIRST
            instr = primary_template.format(
                code_abs=str(code_path),
                test_abs=str(test_path),
                begin=_begin_marker(code_path),
                end=_end_marker(code_path),
                prompt_content=prompt_content,
                code_content=orig_code,
                test_content=orig_test,
                error_content=error_content,
                verify_cmd=verify_cmd or "No verification command provided.",
            )
            
            snapshot = get_mtime_snapshot(working_dir)
            response, cost, model = llm_invoke(instr)
            est_cost += cost
            used_model = model

            changed = parse_multi_file_markers(response, working_dir)
            direct = detect_mtime_changes(snapshot, working_dir)
            current_batch = list(set(changed + direct))
            all_changed_files.extend(current_batch)

            new_code = code_path.read_text(encoding="utf-8")
            new_test = test_path.read_text(encoding="utf-8")
            
            code_changed = new_code != orig_code
            test_changed = new_test != orig_test
            
            if code_changed or test_changed or current_batch:
                v_cmd = verify_cmd or get_run_command(get_language_from_ext(str(code_path)), str(test_path))
                if _run_testcmd(v_cmd, working_dir):
                    return True, f"Fixed by {provider} (primary)", est_cost, used_model, list(set(all_changed_files))

            # HARVEST FALLBACK
            h_success, h_changed = _try_harvest_then_verify(
                provider, code_path, str(test_path), prompt_content, orig_test, error_content, working_dir,
                verify_cmd=verify_cmd, verbose=verbose, quiet=quiet
            )
            all_changed_files.extend(h_changed)
            if h_success:
                return True, f"Fixed by {provider} (harvest)", est_cost, used_model, list(set(all_changed_files))

        return False, "All agents failed", est_cost, used_model, list(set(all_changed_files))

    except Exception as e:
        return False, str(e), est_cost, used_model, list(set(all_changed_files))

try_harvest_then_verify = _try_harvest_then_verify