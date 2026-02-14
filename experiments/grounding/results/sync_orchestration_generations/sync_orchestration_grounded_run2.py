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
import tempfile
import traceback
from pathlib import Path
from typing import Dict, Any, Optional, List, Callable
from dataclasses import asdict, dataclass

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
MAX_CYCLE_REPEATS = 2

# --- Atomic State Update (Issue #159 Fix) ---

@dataclass
class PendingStateUpdate:
    run_report: Optional[Dict[str, Any]] = None
    fingerprint: Optional[Dict[str, Any]] = None
    run_report_path: Optional[Path] = None
    fingerprint_path: Optional[Path] = None

class AtomicStateUpdate:
    """Ensures run_report and fingerprint are both written or neither is written."""
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self.pending = PendingStateUpdate()
        self._temp_files: List[str] = []

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            self._commit()
        else:
            self._rollback()
        return False

    def set_run_report(self, report: Dict[str, Any], path: Path):
        self.pending.run_report = report
        self.pending.run_report_path = path

    def set_fingerprint(self, fingerprint: Dict[str, Any], path: Path):
        self.pending.fingerprint = fingerprint
        self.pending.fingerprint_path = path

    def _atomic_write(self, data: Dict[str, Any], target_path: Path) -> None:
        target_path.parent.mkdir(parents=True, exist_ok=True)
        fd, temp_path = tempfile.mkstemp(dir=target_path.parent, prefix=f".{target_path.stem}_", suffix=".tmp")
        self._temp_files.append(temp_path)
        try:
            with os.fdopen(fd, 'w') as f:
                json.dump(data, f, indent=2, default=str)
            os.replace(temp_path, target_path)
            if temp_path in self._temp_files:
                self._temp_files.remove(temp_path)
        except Exception:
            raise

    def _commit(self):
        if self.pending.fingerprint and self.pending.fingerprint_path:
            self._atomic_write(self.pending.fingerprint, self.pending.fingerprint_path)
        if self.pending.run_report and self.pending.run_report_path:
            self._atomic_write(self.pending.run_report, self.pending.run_report_path)

    def _rollback(self):
        for temp_path in self._temp_files:
            try:
                if os.path.exists(temp_path):
                    os.unlink(temp_path)
            except OSError:
                pass
        self._temp_files.clear()

# --- Helper Functions ---

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    return language.lower() != 'python' or agentic_mode

def _save_run_report_atomic(report: Dict[str, Any], basename: str, language: str, atomic_state: Optional[AtomicStateUpdate] = None):
    if atomic_state:
        report_file = META_DIR / f"{_safe_basename(basename)}_{language.lower()}_run.json"
        atomic_state.set_run_report(report, report_file)
    else:
        save_run_report(basename, language, report)

def _save_fingerprint_atomic(basename: str, language: str, operation: str, paths: Dict[str, Path], cost: float, model: str, atomic_state: Optional[AtomicStateUpdate] = None):
    if atomic_state:
        from . import __version__
        current_hashes = calculate_current_hashes(paths)
        fp = {
            "pdd_version": __version__,
            "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "command": operation,
            "prompt_hash": current_hashes.get('prompt_hash'),
            "code_hash": current_hashes.get('code_hash'),
            "example_hash": current_hashes.get('example_hash'),
            "test_hash": current_hashes.get('test_hash'),
            "test_files": current_hashes.get('test_files'),
        }
        fp_file = META_DIR / f"{_safe_basename(basename)}_{language.lower()}.json"
        atomic_state.set_fingerprint(fp, fp_file)
    else:
        save_fingerprint(basename, language, operation, paths, cost, model)

def _python_cov_target_for_test_and_code(test_file: Path, code_file: Path, fallback: str) -> str:
    # Logic to find dotted module or stem based on imports
    stem = code_file.stem
    try:
        source = test_file.read_text(encoding='utf-8', errors='ignore')
        if re.search(rf"^\s*(import|from)\s+{re.escape(stem)}\b", source, re.M):
            return stem
    except Exception:
        pass
    return stem or fallback

def _parse_test_output(output: str, language: str) -> tuple[int, int, float]:
    passed, failed, coverage = 0, 0, 0.0
    lang = language.lower()
    if lang == 'python':
        pm = re.search(r'(\d+) passed', output); passed = int(pm.group(1)) if pm else 0
        fm = re.search(r'(\d+) failed', output); failed = int(fm.group(1)) if fm else 0
        em = re.search(r'(\d+) error', output); failed += int(em.group(1)) if em else 0
        cm = re.search(r'TOTAL.*?(\d+)%', output)
        if cm: coverage = float(cm.group(1))
    elif lang in ('javascript', 'typescript'):
        pm = re.search(r'Tests:\s*(\d+)\s+passed', output); passed = int(pm.group(1)) if pm else 0
        fm = re.search(r'Tests:.*?(\d+)\s+failed', output); failed = int(fm.group(1)) if fm else 0
        cm = re.search(r'All files[^|]*|\s*(\d+\.?\d*)', output)
        if cm: coverage = float(cm.group(1))
    return passed, failed, coverage

def _detect_example_errors(output: str) -> tuple[bool, str]:
    if "Traceback (most recent call last):" in output:
        return True, "Python traceback"
    if " - ERROR - " in output:
        return True, "Error log message"
    return False, ""

def _try_auto_fix_import_error(error_output: str, code_file: Path, example_file: Path) -> tuple[bool, str]:
    # Placeholder for auto-fix logic (sys.path insertion or pip install)
    return False, "Not attempted"

def _run_example_with_error_detection(cmd_parts: list[str], env: dict, cwd: Optional[str] = None, timeout: int = 60) -> tuple[int, str, str]:
    proc = subprocess.Popen(cmd_parts, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL, env=env, cwd=cwd, start_new_session=True)
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.terminate()
        stdout, stderr = proc.communicate()
    stdout_s = stdout.decode('utf-8', errors='replace')
    stderr_s = stderr.decode('utf-8', errors='replace')
    has_err, _ = _detect_example_errors(stdout_s + stderr_s)
    rc = proc.returncode if not has_err else (proc.returncode or 1)
    return rc, stdout_s, stderr_s

def _create_synthetic_run_report_for_agentic_success(test_file: Path, basename: str, language: str, *, atomic_state: Optional[AtomicStateUpdate] = None) -> RunReport:
    report = RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 0, 1, 0, 0.0, test_hash=calculate_sha256(test_file) if test_file.exists() else "agentic_test_success")
    _save_run_report_atomic(asdict(report), basename, language, atomic_state)
    return report

def _execute_tests_and_create_run_report(test_file: Path, basename: str, language: str, target_coverage: float = 90.0, *, code_file: Optional[Path] = None, atomic_state: Optional[AtomicStateUpdate] = None, test_files: Optional[List[Path]] = None) -> RunReport:
    from .get_test_command import get_test_command_for_file
    all_files = test_files if test_files else [test_file]
    clean_env = os.environ.copy()
    for v in ['FORCE_COLOR', 'COLUMNS']: clean_env.pop(v, None)
    
    if language.lower() == 'python':
        py_exe = detect_host_python_executable()
        cov_target = _python_cov_target_for_test_and_code(test_file, code_file, basename)
        root = _find_project_root(test_file)
        args = [py_exe, '-m', 'pytest'] + [str(f) for f in all_files] + ['-v', '--tb=short', f'--cov={cov_target}', '--cov-report=term-missing']
        if root:
            clean_env["PYTHONPATH"] = f"{root}:{root}/src:{clean_env.get('PYTHONPATH', '')}"
            args.extend([f'--rootdir={root}', '-c', '/dev/null'])
        res = subprocess.run(args, capture_output=True, text=True, env=clean_env, cwd=str(root) if root else None)
        passed, failed, cov = _parse_test_output(res.stdout + res.stderr, 'python')
        rc = res.returncode
    else:
        cmd = get_test_command_for_file(str(test_file), language)
        if not cmd: return RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 127, 0, 0, 0.0)
        res = subprocess.run(cmd, shell=True, capture_output=True, text=True, env=clean_env, cwd=str(test_file.parent))
        passed, failed, cov = _parse_test_output(res.stdout + res.stderr, language)
        rc = res.returncode

    report = RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), rc, passed, failed, cov, test_hash=calculate_sha256(test_file) if test_file.exists() else None)
    _save_run_report_atomic(asdict(report), basename, language, atomic_state)
    return report

def _create_mock_context(**kwargs) -> click.Context:
    ctx = click.Context(click.Command('sync'))
    ctx.obj = kwargs
    return ctx

def _display_sync_log(basename: str, language: str, verbose: bool = False) -> Dict[str, Any]:
    entries = load_operation_log(basename, language)
    if not entries: return {'success': True, 'log_entries': []}
    for e in entries:
        print(f"[{e.get('timestamp', '')[:19]}] {e.get('operation', 'EVENT'):<12} | {e.get('reason', e.get('event', ''))}")
    return {'success': True, 'log_entries': entries}

# --- Main Orchestration ---

def sync_orchestration(
    basename: str,
    target_coverage: float = 90.0,
    language: str = "python",
    prompts_dir: str = "prompts",
    code_dir: str = "src",
    examples_dir: str = "examples",
    tests_dir: str = "tests",
    max_attempts: int = 3,
    budget: float = 10.0,
    skip_verify: bool = False,
    skip_tests: bool = False,
    dry_run: bool = False,
    force: bool = False,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time_param: float = 0.25,
    verbose: bool = False,
    quiet: bool = False,
    output_cost: Optional[str] = None,
    review_examples: bool = False,
    local: bool = False,
    context_config: Optional[Dict[str, str]] = None,
    context_override: Optional[str] = None,
    confirm_callback: Optional[Callable[[str, str], bool]] = None,
    no_steer: bool = False,
    steer_timeout: float = DEFAULT_STEER_TIMEOUT_S,
    agentic_mode: bool = False,
) -> Dict[str, Any]:
    target_coverage = target_coverage or 90.0
    budget = budget or 10.0
    max_attempts = max_attempts or 3

    if dry_run:
        return _display_sync_log(basename, language, verbose)

    try:
        pdd_files = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
    except FileNotFoundError:
        # Fallback path construction
        from .sync_determine_operation import get_extension
        ext = get_extension(language)
        pdd_files = {
            'prompt': Path(prompts_dir) / f"{basename}_{language}.prompt",
            'code': Path(f"{code_dir}/{basename}.{ext}"),
            'example': Path(f"{examples_dir}/{basename}_example.{ext}"),
            'test': Path(f"{tests_dir}/test_{basename}.{ext}")
        }

    # Shared refs for TUI
    current_function_name_ref = ["initializing"]
    current_cost_ref = [0.0]
    stop_event = threading.Event()
    app_ref: List[Optional[SyncApp]] = [None]
    user_confirmed_overwrite = [False]
    progress_callback_ref = [None]

    def get_confirm_cb():
        if user_confirmed_overwrite[0]: return lambda m, t: True
        if app_ref[0]:
            def cb(m, t):
                res = app_ref[0].request_confirmation(m, t)
                if res: user_confirmed_overwrite[0] = True
                return res
            return cb
        def headless_cb(m, t):
            res = click.confirm(m, default=True)
            if res: user_confirmed_overwrite[0] = True
            return res
        return headless_cb

    def sync_worker_logic():
        ops_completed, skipped_ops, errors = [], [], []
        start_time = time.time()
        history = []
        last_model = ""

        try:
            with SyncLock(basename, language):
                log_event(basename, language, "lock_acquired", {"pid": os.getpid()}, "sync")
                while current_cost_ref[0] < budget:
                    decision = sync_determine_operation(basename, language, target_coverage, budget - current_cost_ref[0], False, prompts_dir, skip_tests, skip_verify, context_override)
                    op = decision.operation

                    if not no_steer:
                        op, abort = maybe_steer_operation(op, decision.reason, app_ref[0], quiet, skip_tests, skip_verify, steer_timeout)
                        if abort: errors.append("Aborted via steering"); break

                    if op in ('all_synced', 'nothing', 'fail_and_request_manual_merge', 'error'):
                        if 'merge' in op or 'error' in op: errors.append(decision.reason)
                        break

                    # Cycle/Loop detection
                    history.append(op)
                    if history.count('auto-deps') >= 2 and history[-1] == 'auto-deps': op = 'generate'
                    if len(history) >= 4 and history[-4:] in (['test','fix','test','fix'], ['fix','test','fix','test']):
                        errors.append("Detected test-fix cycle"); break
                    if history[-5:].count('fix') == 5: errors.append("Max consecutive fixes"); break
                    if history[-3:].count('test') == 3: errors.append("Max consecutive tests"); break
                    if history[-3:].count('crash') == 3: errors.append("Max consecutive crashes"); break

                    current_function_name_ref[0] = op
                    ctx = _create_mock_context(force=force, strength=strength, temperature=temperature, time=time_param, local=local, confirm_callback=get_confirm_cb(), agentic_mode=agentic_mode)
                    
                    with AtomicStateUpdate(basename, language) as atomic_state:
                        res = None
                        try:
                            if op == 'auto-deps':
                                res = auto_deps_main(ctx, str(pdd_files['prompt']), examples_dir, output=str(pdd_files['prompt']), progress_callback=progress_callback_ref[0])
                            elif op == 'generate':
                                res = code_generator_main(ctx, str(pdd_files['prompt'].resolve()), str(pdd_files['code'].resolve()))
                                clear_run_report(basename, language)
                            elif op == 'example':
                                res = context_generator_main(ctx, str(pdd_files['prompt'].resolve()), str(pdd_files['code'].resolve()), str(pdd_files['example'].resolve()))
                            elif op == 'crash':
                                eff_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                res = crash_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), "crash.log", output=str(pdd_files['code']), loop=True, max_attempts=eff_max)
                            elif op == 'verify':
                                eff_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                res = fix_verification_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), output_code=str(pdd_files['code']), loop=True, max_attempts=eff_max)
                            elif op == 'test' or op == 'test_extend':
                                res = cmd_test_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['test']), language=language, merge=(op=='test_extend'))
                                agent_ok = res[3] if isinstance(res, tuple) and len(res) >= 4 else None
                                if agent_ok: _create_synthetic_run_report_for_agentic_success(pdd_files['test'], basename, language, atomic_state=atomic_state)
                                elif pdd_files['test'].exists(): _execute_tests_and_create_run_report(pdd_files['test'], basename, language, target_coverage, code_file=pdd_files['code'], atomic_state=atomic_state)
                            elif op == 'fix':
                                eff_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                res = fix_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['test']), "fix_errors.log", loop=True, max_attempts=eff_max, auto_submit=(not local))
                                if bool(res[0] if isinstance(res, tuple) else res.get('success')):
                                    if _use_agentic_path(language, agentic_mode): _create_synthetic_run_report_for_agentic_success(pdd_files['test'], basename, language, atomic_state=atomic_state)
                                    else: _execute_tests_and_create_run_report(pdd_files['test'], basename, language, target_coverage, code_file=pdd_files['code'], atomic_state=atomic_state)
                            elif op == 'update':
                                res = update_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), use_git=True)
                        except Exception as e:
                            errors.append(f"Op {op} failed: {e}"); break

                        # Result parsing
                        success = False
                        if isinstance(res, dict):
                            success = res.get('success', False)
                            cost = res.get('cost', 0.0); last_model = res.get('model', '')
                        elif isinstance(res, tuple):
                            success = bool(res[0]); cost = res[1]; last_model = res[2]
                        
                        if success:
                            current_cost_ref[0] += cost
                            ops_completed.append(op)
                            _save_fingerprint_atomic(basename, language, op, pdd_files, cost, last_model, atomic_state)
                        else:
                            errors.append(f"Operation {op} was unsuccessful"); break

        except Exception as e:
            errors.append(f"Sync error: {e}")
        finally:
            log_event(basename, language, "sync_end", {"cost": current_cost_ref[0]}, "sync")

        return {
            'success': not errors,
            'operations_completed': ops_completed,
            'skipped_operations': skipped_ops,
            'total_cost': current_cost_ref[0],
            'total_time': time.time() - start_time,
            'final_state': {p: {'exists': f.exists(), 'path': str(f)} for p, f in pdd_files.items() if p != 'test_files'},
            'errors': errors,
            'error': "; ".join(errors) if errors else None,
            'model_name': last_model,
        }

    headless = quiet or not sys.stdout.isatty() or os.environ.get('CI')
    if headless:
        return sync_worker_logic()
    else:
        app = SyncApp(basename, budget, sync_worker_logic, current_function_name_ref, current_cost_ref, prompt_path_ref, code_path_ref, example_path_ref, tests_path_ref, stop_event=stop_event, progress_callback_ref=progress_callback_ref)
        app_ref[0] = app
        res = app.run()
        from .sync_tui import show_exit_animation
        if not quiet: show_exit_animation()
        return res or {"success": False, "error": "Interrupted"}