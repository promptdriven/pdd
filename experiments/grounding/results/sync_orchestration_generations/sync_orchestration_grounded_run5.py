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
import shutil
import traceback
from pathlib import Path
from typing import Dict, Any, Optional, List, Callable
from dataclasses import asdict, dataclass

import click

from .sync_tui import maybe_steer_operation, DEFAULT_STEER_TIMEOUT_S, SyncApp, show_exit_animation
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
    get_extension,
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

# --- Helpers ---

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    return language.lower() != 'python' or agentic_mode

def _display_sync_log(basename: str, language: str, verbose: bool = False) -> Dict[str, Any]:
    log_file = META_DIR / f"{_safe_basename(basename)}_{language.lower()}_sync.log"
    if not log_file.exists():
        print(f"No sync log found for '{basename}' in language '{language}'.")
        return {'success': False, 'errors': ['Log file not found.'], 'log_entries': []}
    entries = load_operation_log(basename, language)
    print(f"--- Sync Log for {basename} ({language}) ---")
    for entry in entries:
        ts = entry.get('timestamp', 'N/A')[:19]
        if 'event' in entry:
            print(f"[{ts}] EVENT: {entry.get('event', 'N/A')}")
            continue
        op = entry.get('operation', 'N/A')
        res = entry.get('reason', 'N/A')
        succ = entry.get('success')
        cost = entry.get('actual_cost')
        icon = "✓" if succ else "✗" if succ is False else "?"
        print(f"[{ts}] {op:<12} | {res} | {icon} ${cost if cost is not None else 0.0:.2f}")
    print("--- End of Log ---")
    return {'success': True, 'log_entries': entries}

def _create_mock_context(**kwargs) -> click.Context:
    ctx = click.Context(click.Command('sync'))
    ctx.obj = kwargs
    return ctx

def _parse_test_output(output: str, language: str) -> tuple[int, int, float]:
    passed, failed, coverage = 0, 0, 0.0
    lang = language.lower()
    if lang == 'python':
        p_m = re.search(r'(\d+) passed', output); passed = int(p_m.group(1)) if p_m else 0
        f_m = re.search(r'(\d+) failed', output); failed = int(f_m.group(1)) if f_m else 0
        e_m = re.search(r'(\d+) error', output); failed += int(e_m.group(1)) if e_m else 0
        c_m = re.search(r'TOTAL.*?(\d+)%', output); coverage = float(c_m.group(1)) if c_m else 0.0
    elif lang in ('javascript', 'typescript'):
        p_m = re.search(r'Tests:\s*(\d+)\s+passed', output); passed = int(p_m.group(1)) if p_m else 0
        f_m = re.search(r'Tests:.*?(\d+)\s+failed', output); failed = int(f_m.group(1)) if f_m else 0
        c_m = re.search(r'All files[^|]*|\s*(\d+\.?\d*)', output); coverage = float(c_m.group(1)) if c_m else 0.0
    return passed, failed, coverage

def _execute_tests_and_create_run_report(test_file: Path, basename: str, language: str, target_coverage: float, *, code_file=None, atomic_state=None, test_files=None) -> RunReport:
    from .get_test_command import get_test_command_for_file
    all_tests = test_files if test_files else [test_file]
    hashes = {f.name: calculate_sha256(f) for f in all_tests if f.exists()}
    clean_env = os.environ.copy()
    for var in ['FORCE_COLOR', 'COLUMNS']: clean_env.pop(var, None)
    
    try:
        if language.lower() == "python":
            python = detect_host_python_executable()
            root = _find_project_root(test_file)
            args = [python, '-m', 'pytest'] + [str(f) for f in all_tests] + ['-v', '--tb=short']
            if code_file: args.append(f'--cov={code_file.stem}')
            kw = {'capture_output': True, 'text': True, 'timeout': 300, 'env': clean_env, 'stdin': subprocess.DEVNULL, 'start_new_session': True}
            if root:
                clean_env["PYTHONPATH"] = os.pathsep.join([str(root), str(root/"src"), clean_env.get("PYTHONPATH","")])
                args.extend([f'--rootdir={root}', '-c', '/dev/null'])
                kw['cwd'] = str(root)
            res = subprocess.run(args, **kw)
            p, f, c = _parse_test_output(res.stdout + res.stderr, language)
            report = RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), res.returncode, p, f, c, test_hash=hashes.get(test_file.name), test_files=hashes)
        else:
            cmd = get_test_command_for_file(str(test_file), language)
            if not cmd: return RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 127, 0, 0, 0.0)
            res = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=300, env=clean_env, cwd=str(test_file.parent), start_new_session=True)
            p, f, c = _parse_test_output(res.stdout + res.stderr, language)
            report = RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), res.returncode, p, f, c, test_hash=hashes.get(test_file.name), test_files=hashes)
    except Exception:
        report = RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 1, 0, 1, 0.0)
    
    _save_run_report_atomic(asdict(report), basename, language, atomic_state)
    return report

def _create_synthetic_run_report_for_agentic_success(test_file, basename, language, *, atomic_state=None):
    h = calculate_sha256(test_file) if test_file.exists() else "agentic_test_success"
    report = RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 0, 1, 0, 0.0, test_hash=h)
    _save_run_report_atomic(asdict(report), basename, language, atomic_state)
    return report

def _run_example_with_error_detection(cmd, env, cwd=None, timeout=60):
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL, env=env, cwd=cwd, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill(); out, err = proc.communicate()
    stdout = out.decode('utf-8', errors='replace')
    stderr = err.decode('utf-8', errors='replace')
    has_err = "Traceback" in stderr or " - ERROR - " in (stdout + stderr)
    return (1 if has_err or proc.returncode != 0 else 0), stdout, stderr

def _try_auto_fix_import_error(err, code_file, example_file):
    m = re.search(r"ModuleNotFoundError: No module named ['\"]([^'\"]+)['\"]", err)
    if m and m.group(1) == code_file.stem:
        try:
            content = example_file.read_text()
            fix = f"\nimport sys\nsys.path.insert(0, '{code_file.parent.resolve()}')\n"
            example_file.write_text(fix + content)
            return True, "Fixed import path"
        except Exception: pass
    return False, ""

def _save_fingerprint_atomic(basename, language, op, paths, cost, model, atomic_state=None):
    if atomic_state:
        from . import __version__
        hashes = calculate_current_hashes(paths)
        fp = {'pdd_version': __version__, 'timestamp': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'command': op, 'prompt_hash': hashes.get('prompt_hash'), 'code_hash': hashes.get('code_hash'), 'example_hash': hashes.get('example_hash'), 'test_hash': hashes.get('test_hash'), 'test_files': hashes.get('test_files')}
        atomic_state.set_fingerprint(fp, META_DIR / f"{_safe_basename(basename)}_{language.lower()}.json")
    else:
        save_fingerprint(basename, language, op, paths, cost, model)

def _save_run_report_atomic(report, basename, language, atomic_state=None):
    if atomic_state:
        atomic_state.set_run_report(report, META_DIR / f"{_safe_basename(basename)}_{language.lower()}_run.json")
    else:
        save_run_report(basename, language, report)

# --- Main Orchestration ---

def sync_orchestration(
    basename: str, target_coverage: float = 90.0, language: str = "python",
    prompts_dir: str = "prompts", code_dir: str = "src", examples_dir: str = "examples",
    tests_dir: str = "tests", max_attempts: int = 3, budget: float = 10.0,
    skip_verify: bool = False, skip_tests: bool = False, dry_run: bool = False,
    force: bool = False, strength: float = DEFAULT_STRENGTH, temperature: float = 0.0,
    time_param: float = 0.25, verbose: bool = False, quiet: bool = False,
    output_cost: Optional[str] = None, review_examples: bool = False, local: bool = False,
    context_config: Optional[Dict[str, str]] = None, context_override: Optional[str] = None,
    confirm_callback: Optional[Callable[[str, str], bool]] = None, no_steer: bool = False,
    steer_timeout: float = DEFAULT_STEER_TIMEOUT_S, agentic_mode: bool = False,
) -> Dict[str, Any]:
    
    target_coverage = target_coverage or 90.0
    budget = budget or 10.0
    max_attempts = max_attempts or 3

    if dry_run: return _display_sync_log(basename, language, verbose)

    try:
        pdd_files = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
    except FileNotFoundError:
        ext = get_extension(language)
        pdd_files = {'prompt': Path(prompts_dir)/f"{basename}_{language}.prompt", 'code': Path(code_dir)/f"{basename}.{ext}", 'example': Path(examples_dir)/f"{basename}_example.{ext}", 'test': Path(tests_dir)/f"test_{basename}.{ext}"}

    cur_fn, cur_cost, stop_event = ["initializing"], [0.0], threading.Event()
    app_ref, progress_ref, confirmed = [None], [None], [False]

    def get_cb():
        if confirmed[0]: return lambda m, t: True
        if app_ref[0]:
            def cb(m, t):
                res = app_ref[0].request_confirmation(m, t)
                if res: confirmed[0] = True
                return res
            return cb
        def h_cb(m, t):
            res = click.confirm(click.style(m, fg="yellow"), default=True)
            if res: confirmed[0] = True
            return res
        return h_cb

    def worker():
        ops, skipped, errs, history = [], [], [], []
        start = time.time()
        model = ""
        try:
            with SyncLock(basename, language):
                while True:
                    rem = budget - cur_cost[0]
                    if cur_cost[0] >= budget: errs.append("Budget exceeded"); break
                    
                    dec = sync_determine_operation(basename, language, target_coverage, rem, False, prompts_dir, skip_tests, skip_verify, context_override)
                    op = dec.operation
                    if not no_steer:
                        op, abort = maybe_steer_operation(op, dec.reason, app_ref[0], quiet, skip_tests, skip_verify, steer_timeout)
                        if abort: errs.append("Aborted by user"); break
                    
                    history.append(op)
                    if len(history) >= 3 and history[-3:].count('auto-deps') >= 2: op = 'generate'
                    if len(history) >= 4:
                        if history[-4:] in (['crash','verify','crash','verify'], ['verify','crash','verify','crash']): break
                        if history[-4:] in (['test','fix','test','fix'], ['fix','test','fix','test']): break
                    if history.count('fix') >= 5 or history.count('test') >= MAX_CONSECUTIVE_TESTS or history.count('crash') >= MAX_CONSECUTIVE_CRASHES: break

                    if op in ('all_synced', 'nothing', 'error', 'fail_and_request_manual_merge'):
                        if op.startswith('fail'): errs.append(f"Manual merge: {dec.reason}")
                        break

                    if op == 'verify' and (skip_verify or skip_tests):
                        _save_fingerprint_atomic(basename, language, 'skip:verify', pdd_files, 0.0, 'skipped'); skipped.append('verify'); continue
                    if op == 'test' and skip_tests:
                        _save_fingerprint_atomic(basename, language, 'skip:test', pdd_files, 0.0, 'skipped'); skipped.append('test'); continue

                    cur_fn[0] = op
                    ctx = _create_mock_context(force=force, strength=strength, temperature=temperature, time=time_param, verbose=verbose, quiet=quiet, local=local, budget=rem, max_attempts=max_attempts, confirm_callback=get_cb(), agentic_mode=agentic_mode)
                    
                    with AtomicStateUpdate(basename, language) as state:
                        try:
                            res, success = {}, False
                            if op == 'auto-deps':
                                res = auto_deps_main(ctx, str(pdd_files['prompt']), examples_dir, "project_dependencies.csv", progress_callback=progress_ref[0])
                                success = bool(res)
                            elif op == 'generate':
                                res = code_generator_main(ctx, str(pdd_files['prompt'].resolve()), str(pdd_files['code'].resolve()))
                                clear_run_report(basename, language); success = True
                            elif op == 'example':
                                res = context_generator_main(ctx, str(pdd_files['prompt'].resolve()), str(pdd_files['code'].resolve()), str(pdd_files['example'].resolve()))
                                success = True
                            elif op == 'crash':
                                eff_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                res = crash_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), "crash.log", str(pdd_files['code']), str(pdd_files['example']), True, eff_max, rem)
                                success = res[0] if isinstance(res, tuple) else res.get('success')
                            elif op == 'verify':
                                eff_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                res = fix_verification_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), f"{basename}_verify.log", str(pdd_files['code']), str(pdd_files['example']), True, None, eff_max, rem)
                                success = res[0] if isinstance(res, tuple) else res.get('success')
                            elif op == 'test':
                                res = cmd_test_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['test']), language)
                                success = res[3] if len(res) >= 4 and res[3] is not None else pdd_files['test'].exists()
                                if success:
                                    if len(res) >= 4 and res[3]: _create_synthetic_run_report_for_agentic_success(pdd_files['test'], basename, language, atomic_state=state)
                                    else: _execute_tests_and_create_run_report(pdd_files['test'], basename, language, target_coverage, code_file=pdd_files['code'], atomic_state=state)
                            elif op == 'fix':
                                eff_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                res = fix_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['test']), "fix_errors.log", str(pdd_files['test']), str(pdd_files['code']), f"{basename}_fix.log", True, str(pdd_files['example']), eff_max, rem, auto_submit=(not local))
                                success = res[0] if isinstance(res, tuple) else res.get('success')
                                if success: _execute_tests_and_create_run_report(pdd_files['test'], basename, language, target_coverage, atomic_state=state)
                            elif op == 'update':
                                res = update_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), use_git=True)
                                success = True

                            cost = res.get('cost', 0.0) if isinstance(res, dict) else (res[1] if op == 'test' else res[-2]) if isinstance(res, tuple) else 0.0
                            model = res.get('model', '') if isinstance(res, dict) else (res[2] if op == 'test' else res[-1]) if isinstance(res, tuple) else ''
                            cur_cost[0] += cost
                            if success:
                                ops.append(op)
                                _save_fingerprint_atomic(basename, language, op, pdd_files, cost, str(model), state)
                            else: break
                        except click.Abort: break
                        except Exception as e: errs.append(f"{op} exception: {e}"); break
        except Exception as e: errs.append(f"Fatal: {e}")
        return {'success': not errs, 'operations_completed': ops, 'skipped_operations': skipped, 'total_cost': cur_cost[0], 'total_time': time.time() - start, 'errors': errs, 'model_name': model, 'final_state': {p: {'exists': f.exists(), 'path': str(f)} for p, f in pdd_files.items() if p != 'test_files'}}

    headless = quiet or not sys.stdout.isatty() or os.environ.get('CI')
    if headless:
        os.environ['PDD_FORCE'] = '1'
        return worker()
    
    # Note: prompt_path_ref and others are assumed to be defined in the outer scope or passed in
    # For this extraction, we assume they are part of the SyncApp initialization context.
    app = SyncApp(basename, budget, worker, cur_fn, cur_cost, stop_event, progress_callback_ref=progress_ref)
    app_ref[0] = app
    res = app.run()
    show_exit_animation()
    if app.worker_exception: traceback.print_exception(type(app.worker_exception), app.worker_exception, app.worker_exception.__traceback__)
    return res or {"success": False, "errors": ["App exited"]}