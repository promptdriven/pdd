# pdd/sync_orchestration.py
"""
Orchestrates the complete PDD sync workflow by coordinating operations and
animations in parallel, serving as the core engine for the `pdd sync` command.
"""

import threading
import time
import json
import datetime
import subprocess
import re
import os
import sys
import logging
import tempfile
import traceback
from pathlib import Path
from typing import Dict, Any, Optional, List, Callable
from dataclasses import asdict, dataclass, field
import click

from .sync_tui import maybe_steer_operation, DEFAULT_STEER_TIMEOUT_S, SyncApp
from .operation_log import (
    load_operation_log,
    create_log_entry,
    update_log_entry,
    append_log_entry,
    log_event,
    save_fingerprint,
    save_run_report,
    clear_run_report,
)
from .sync_determine_operation import (
    sync_determine_operation,
    get_pdd_file_paths,
    RunReport,
    SyncDecision,
    PDD_DIR,
    META_DIR,
    SyncLock,
    read_run_report,
    calculate_sha256,
    calculate_current_hashes,
    _safe_basename,
)
from .auto_deps_main import auto_deps_main
from .code_generator_main import code_generator_main
from .context_generator_main import context_generator_main
from .crash_main import crash_main
from .fix_verification_main import fix_verification_main
from .cmd_test_main import cmd_test_main
from .fix_main import fix_main
from .update_main import update_main
from .python_env_detector import detect_host_python_executable
from .get_run_command import get_run_command_for_file
from .pytest_output import extract_failing_files_from_output, _find_project_root
from . import DEFAULT_STRENGTH

# --- Constants ---
MAX_CONSECUTIVE_TESTS = 3
MAX_TEST_EXTEND_ATTEMPTS = 2
MAX_CONSECUTIVE_CRASHES = 3

# --- Helper Classes ---

class AtomicStateUpdate:
    """
    Context manager for atomic state updates.
    Ensures run_report and fingerprint are both written or neither is written.
    """
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self.pending_report = None
        self.report_path = None
        self.pending_fingerprint = None
        self.fp_path = None
        self._temp_files = []

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            self._commit()
        else:
            self._rollback()
        return False

    def set_run_report(self, report: Dict, path: Path):
        self.pending_report = report
        self.report_path = path

    def set_fingerprint(self, fp: Dict, path: Path):
        self.pending_fingerprint = fp
        self.fp_path = path

    def _atomic_write(self, data: Dict, target: Path):
        target.parent.mkdir(parents=True, exist_ok=True)
        fd, temp_path = tempfile.mkstemp(dir=target.parent, suffix=".tmp")
        self._temp_files.append(temp_path)
        with os.fdopen(fd, 'w') as f:
            json.dump(data, f, indent=2)
        os.replace(temp_path, target)

    def _commit(self):
        if self.pending_fingerprint:
            self._atomic_write(self.pending_fingerprint, self.fp_path)
        if self.pending_report:
            self._atomic_write(self.pending_report, self.report_path)

    def _rollback(self):
        for f in self._temp_files:
            try: os.unlink(f)
            except: pass

# --- Internal Helpers ---

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    return language.lower() != 'python' or agentic_mode

def _save_fingerprint_atomic(basename: str, language: str, operation: str, paths: Dict[str, Path], 
                             cost: float, model: str, atomic_state: Optional[AtomicStateUpdate] = None):
    if atomic_state:
        from . import __version__
        hashes = calculate_current_hashes(paths)
        fp = {
            "pdd_version": __version__,
            "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "command": operation,
            "prompt_hash": hashes.get('prompt_hash'),
            "code_hash": hashes.get('code_hash'),
            "example_hash": hashes.get('example_hash'),
            "test_hash": hashes.get('test_hash'),
            "test_files": hashes.get('test_files')
        }
        atomic_state.set_fingerprint(fp, META_DIR / f"{_safe_basename(basename)}_{language.lower()}.json")
    else:
        save_fingerprint(basename, language, operation, paths, cost, model)

def _save_run_report_atomic(report: Dict, basename: str, language: str, atomic_state: Optional[AtomicStateUpdate] = None):
    if atomic_state:
        path = META_DIR / f"{_safe_basename(basename)}_{language.lower()}_run.json"
        atomic_state.set_run_report(report, path)
    else:
        save_run_report(basename, language, report)

def _python_cov_target_for_test_and_code(test_file: Path, code_file: Path, fallback: str) -> str:
    # Simplified logic for coverage target
    return code_file.stem if code_file else fallback

def _create_synthetic_run_report_for_agentic_success(test_file: Path, basename: str, language: str, atomic_state=None):
    report = {
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "exit_code": 0,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 0.0,
        "test_hash": calculate_sha256(test_file) if test_file.exists() else "agentic_test_success"
    }
    _save_run_report_atomic(report, basename, language, atomic_state)
    return RunReport(**report)

def _parse_test_output(output: str, language: str) -> tuple[int, int, float]:
    passed, failed, coverage = 0, 0, 0.0
    # Basic regex parsing for pytest and common runners
    if 'passed' in output:
        m = re.search(r'(\d+) passed', output)
        if m: passed = int(m.group(1))
    if 'failed' in output:
        m = re.search(r'(\d+) failed', output)
        if m: failed = int(m.group(1))
    if 'error' in output:
        m = re.search(r'(\d+) error', output)
        if m: failed += int(m.group(1))
    m = re.search(r'TOTAL.*?(\d+)%', output)
    if m: coverage = float(m.group(1))
    return passed, failed, coverage

def _execute_tests_and_create_run_report(test_file: Path, basename: str, language: str, target_coverage: float = 90.0, 
                                        code_file=None, atomic_state=None, test_files=None) -> RunReport:
    from .get_test_command import get_test_command_for_file
    all_tests = test_files if test_files else [test_file]
    clean_env = os.environ.copy()
    for v in ['FORCE_COLOR', 'COLUMNS']: clean_env.pop(v, None)
    
    try:
        if language.lower() == "python":
            python_exe = detect_host_python_executable()
            root = _find_project_root(test_file)
            cov_target = _python_cov_target_for_test_and_code(test_file, code_file, basename)
            cmd = [python_exe, "-m", "pytest"] + [str(f) for f in all_tests] + ["-v", f"--cov={cov_target}"]
            if root:
                clean_env["PYTHONPATH"] = f"{root}:{root}/src:{clean_env.get('PYTHONPATH', '')}"
                cmd += [f"--rootdir={root}", "-c", "/dev/null"]
            res = subprocess.run(cmd, capture_output=True, text=True, env=clean_env, timeout=300)
        else:
            cmd = get_test_command_for_file(str(test_file), language)
            if not cmd: return RunReport(datetime.datetime.now().isoformat(), 127, 0, 0, 0.0)
            res = subprocess.run(cmd, shell=True, capture_output=True, text=True, env=clean_env, cwd=str(test_file.parent))
        
        p, f, c = _parse_test_output(res.stdout + res.stderr, language)
        report_data = {"timestamp": datetime.datetime.now().isoformat(), "exit_code": res.returncode, 
                       "tests_passed": p, "tests_failed": f, "coverage": c, "test_hash": calculate_sha256(test_file) if test_file.exists() else None}
    except Exception:
        report_data = {"timestamp": datetime.datetime.now().isoformat(), "exit_code": 1, "tests_passed": 0, "tests_failed": 1, "coverage": 0.0}
    
    _save_run_report_atomic(report_data, basename, language, atomic_state)
    return RunReport(**report_data)

def _detect_example_errors(output: str) -> tuple[bool, str]:
    if "Traceback (most recent call last):" in output:
        return True, "Python traceback"
    if " - ERROR - " in output:
        return True, "Error log message"
    return False, ""

def _run_example_with_error_detection(cmd, env, cwd=None, timeout=60):
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env, cwd=cwd, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        out, err = proc.communicate()
    combined = (out + err).decode('utf-8', errors='replace')
    has_err, summary = _detect_example_errors(combined)
    rc = proc.returncode if proc.returncode is not None else (1 if has_err else 0)
    if rc == 0 and has_err: rc = 1
    return rc, combined, combined

def _try_auto_fix_import_error(error_log, code_file, example_file):
    return False, "Not implemented"

def _create_mock_context(**kwargs):
    ctx = click.Context(click.Command('sync'))
    ctx.obj = kwargs
    ctx.params = kwargs
    return ctx

def _display_sync_log(basename, language, verbose):
    entries = load_operation_log(basename, language)
    # Simple console print logic
    return {"success": True, "log_entries": entries}

# --- Main Orchestrator ---

def sync_orchestration(basename, target_coverage=90.0, language="python", prompts_dir="prompts", code_dir="src", 
                       examples_dir="examples", tests_dir="tests", max_attempts=3, budget=10.0, 
                       skip_verify=False, skip_tests=False, dry_run=False, force=False, strength=DEFAULT_STRENGTH, 
                       temperature=0.0, time_param=0.25, verbose=False, quiet=False, output_cost=None, 
                       review_examples=False, local=False, context_config=None, context_override=None, 
                       confirm_callback=None, no_steer=False, steer_timeout=DEFAULT_STEER_TIMEOUT_S, agentic_mode=False) -> Dict:
    
    target_coverage = target_coverage or 90.0
    budget = budget or 10.0
    max_attempts = max_attempts or 3

    if dry_run:
        return _display_sync_log(basename, language, verbose)

    from .sync_determine_operation import get_extension
    try:
        pdd_files = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
    except FileNotFoundError:
        ext = get_extension(language)
        pdd_files = {
            'prompt': Path(prompts_dir) / f"{basename}_{language}.prompt",
            'code': Path(code_dir) / f"{basename}.{ext}",
            'example': Path(examples_dir) / f"{basename}_example.{ext}",
            'test': Path(tests_dir) / f"test_{basename}.{ext}"
        }

    state_refs = {
        "fn": ["initializing"], "cost": [0.0], "stop": threading.Event(), "app": [None],
        "paths": [str(pdd_files.get('prompt')), str(pdd_files.get('code')), str(pdd_files.get('example')), str(pdd_files.get('test'))],
        "colors": ["blue", "blue", "blue", "blue"], "overwrite": [False]
    }

    def get_cb():
        if state_refs["overwrite"][0]: return lambda m, t: True
        if state_refs["app"][0]:
            def wrap(m, t):
                res = state_refs["app"][0].request_confirmation(m, t)
                if res: state_refs["overwrite"][0] = True
                return res
            return wrap
        def headless(m, t):
            res = click.confirm(m, default=True)
            if res: state_refs["overwrite"][0] = True
            return res
        return confirm_callback or headless

    def worker():
        ops_done, skipped, errs, history = [], [], [], []
        start_t = time.time()
        
        try:
            with SyncLock(basename, language):
                log_event(basename, language, "lock_acquired", {"pid": os.getpid()}, "sync")
                while True:
                    if state_refs["cost"][0] >= budget:
                        errs.append(f"Budget of ${budget:.2f} exceeded.")
                        break
                    
                    decision = sync_determine_operation(basename, language, target_coverage, budget - state_refs["cost"][0], 
                                                       False, prompts_dir, skip_tests, skip_verify, context_override)
                    op = decision.operation
                    if not no_steer:
                        op, abort = maybe_steer_operation(op, decision.reason, state_refs["app"][0], quiet, skip_tests, skip_verify, steer_timeout)
                        if abort: errs.append("Aborted by user"); break
                    
                    if op in ['all_synced', 'nothing']: break
                    if op in ['fail_and_request_manual_merge', 'error']: errs.append(decision.reason); break
                    
                    # Logic for skips and specific op handling
                    history.append(op)
                    if history.count('auto-deps') >= 2 and history[-1] == 'auto-deps': op = 'generate'
                    if len(history) >= 4 and history[-4:] in [['test', 'fix', 'test', 'fix'], ['fix', 'test', 'fix', 'test']]:
                        errs.append("Detected test-fix cycle"); break

                    state_refs["fn"][0] = op
                    ctx = _create_mock_context(force=force, strength=strength, temperature=temperature, time=time_param, 
                                              local=local, confirm_callback=get_cb(), agentic_mode=agentic_mode)
                    
                    with AtomicStateUpdate(basename, language) as atomic:
                        res = None
                        if op == 'auto-deps':
                            res = auto_deps_main(ctx, str(pdd_files['prompt']), examples_dir, output=str(pdd_files['prompt']))
                        elif op == 'generate':
                            res = code_generator_main(ctx, str(pdd_files['prompt'].resolve()), output=str(pdd_files['code'].resolve()))
                            clear_run_report(basename, language)
                        elif op == 'example':
                            res = context_generator_main(ctx, str(pdd_files['prompt'].resolve()), str(pdd_files['code'].resolve()), output=str(pdd_files['example'].resolve()))
                        elif op == 'crash':
                            eff_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                            res = crash_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), "crash.log", loop=True, max_attempts=eff_max)
                        elif op == 'verify':
                            eff_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                            res = fix_verification_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), loop=True, max_attempts=eff_max)
                        elif op == 'test':
                            res = cmd_test_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['test']), language=language)
                            if (isinstance(res, tuple) and len(res) >= 4 and res[3]) or _use_agentic_path(language, agentic_mode):
                                _create_synthetic_run_report_for_agentic_success(pdd_files['test'], basename, language, atomic)
                            else:
                                _execute_tests_and_create_run_report(pdd_files['test'], basename, language, target_coverage, pdd_files['code'], atomic)
                        elif op == 'fix':
                            eff_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                            res = fix_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['test']), loop=True, max_attempts=eff_max)
                            _execute_tests_and_create_run_report(pdd_files['test'], basename, language, target_coverage, pdd_files['code'], atomic)
                        elif op == 'update':
                            res = update_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), use_git=True)

                        # Result extraction
                        success = res.get('success') if isinstance(res, dict) else (res[3] if op == 'test' and len(res) >= 4 else bool(res[0]))
                        cost = res.get('cost', 0.0) if isinstance(res, dict) else (res[1] if op == 'test' and len(res) >= 4 else res[-2])
                        model = res.get('model', 'unknown') if isinstance(res, dict) else (res[2] if op == 'test' and len(res) >= 4 else res[-1])
                        
                        state_refs["cost"][0] += cost
                        if success:
                            ops_done.append(op)
                            _save_fingerprint_atomic(basename, language, op, pdd_files, cost, model, atomic)
                        else:
                            errs.append(f"Operation {op} failed"); break
        except Exception as e:
            errs.append(f"Fatal: {e}")
            traceback.print_exc()
        
        return {"success": not errs, "operations_completed": ops_done, "skipped_operations": skipped, "total_cost": state_refs["cost"][0], 
                "errors": errs, "final_state": {k: {"exists": v.exists(), "path": str(v)} for k, v in pdd_files.items() if isinstance(v, Path)}}

    headless = quiet or not sys.stdout.isatty() or os.environ.get('CI')
    if headless:
        os.environ['PDD_FORCE'] = '1'
        result = worker()
    else:
        app = SyncApp(basename, budget, worker, state_refs["fn"], state_refs["cost"], [state_refs["paths"][0]], [state_refs["paths"][1]], 
                      [state_refs["paths"][2]], [state_refs["paths"][3]], [state_refs["colors"][0]], [state_refs["colors"][1]], 
                      [state_refs["colors"][2]], [state_refs["colors"][3]], state_refs["stop"])
        state_refs["app"][0] = app
        result = app.run()
        from .sync_tui import show_exit_animation
        show_exit_animation()

    return result or {"success": False, "errors": ["Interrupted"]}