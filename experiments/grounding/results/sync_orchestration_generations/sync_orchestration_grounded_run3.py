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
import shutil
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

# --- Atomic State Update (Issue #159 Fix) ---

@dataclass
class PendingStateUpdate:
    run_report: Optional[Dict[str, Any]] = None
    fingerprint: Optional[Dict[str, Any]] = None
    run_report_path: Optional[Path] = None
    fingerprint_path: Optional[Path] = None

class AtomicStateUpdate:
    """Context manager for atomic state updates ensuring consistency between report and fingerprint."""
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

    def _atomic_write(self, data: Dict[str, Any], target_path: Path):
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
                if os.path.exists(temp_path): os.unlink(temp_path)
            except OSError: pass
        self._temp_files.clear()

# --- Helper Logic ---

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
            "test_files": current_hashes.get('test_files')
        }
        fp_file = META_DIR / f"{_safe_basename(basename)}_{language.lower()}.json"
        atomic_state.set_fingerprint(fp, fp_file)
    else:
        save_fingerprint(basename, language, operation, paths, cost, model)

def _create_synthetic_run_report_for_agentic_success(test_file: Path, basename: str, language: str, atomic_state: Optional[AtomicStateUpdate] = None) -> RunReport:
    test_hash = calculate_sha256(test_file) if test_file.exists() else "agentic_test_success"
    report = RunReport(
        timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        exit_code=0, tests_passed=1, tests_failed=0, coverage=0.0, test_hash=test_hash
    )
    _save_run_report_atomic(asdict(report), basename, language, atomic_state)
    return report

def _execute_tests_and_create_run_report(test_file: Path, basename: str, language: str, target_coverage: float = 90.0, *, code_file: Optional[Path] = None, atomic_state: Optional[AtomicStateUpdate] = None, test_files: Optional[List[Path]] = None) -> RunReport:
    from .get_test_command import get_test_command_for_file
    all_test_files = test_files if test_files else [test_file]
    test_file_hashes = {f.name: calculate_sha256(f) for f in all_test_files if f.exists()}
    
    clean_env = os.environ.copy()
    for var in ['FORCE_COLOR', 'COLUMNS']: clean_env.pop(var, None)

    try:
        lang_lower = language.lower()
        if lang_lower == "python":
            python_exe = detect_host_python_executable()
            project_root = _find_project_root(test_file)
            cov_target = _python_cov_target_for_test_and_code(test_file, code_file, basename) if code_file else basename
            
            args = [python_exe, '-m', 'pytest'] + [str(f) for f in all_test_files] + ['-v', '--tb=short', f'--cov={cov_target}', '--cov-report=term-missing']
            kw = {'capture_output': True, 'text': True, 'timeout': 300, 'stdin': subprocess.DEVNULL, 'env': clean_env, 'start_new_session': True}
            
            if project_root:
                clean_env["PYTHONPATH"] = os.pathsep.join(filter(None, [str(project_root / "src"), str(project_root), clean_env.get("PYTHONPATH", "")]))
                args.extend([f'--rootdir={project_root}', '-c', '/dev/null'])
                kw['cwd'] = str(project_root)
            
            res = subprocess.run(args, **kw)
            tests_passed, tests_failed, coverage = _parse_test_output(res.stdout + (res.stderr or ''), language)
            exit_code = res.returncode
        else:
            test_cmd = get_test_command_for_file(str(test_file), language)
            if not test_cmd: 
                report = RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 127, 0, 0, 0.0, test_files=test_file_hashes)
                _save_run_report_atomic(asdict(report), basename, language, atomic_state)
                return report
            res = subprocess.run(test_cmd, shell=True, capture_output=True, text=True, timeout=300, env=clean_env, cwd=str(test_file.parent), stdin=subprocess.DEVNULL, start_new_session=True)
            tests_passed, tests_failed, coverage = _parse_test_output(res.stdout + '\n' + res.stderr, language)
            exit_code = res.returncode

        report = RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), exit_code, tests_passed, tests_failed, coverage, test_hash=calculate_sha256(test_file) if test_file.exists() else None, test_files=test_file_hashes)
    except Exception:
        report = RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 1, 0, 1, 0.0, test_files=test_file_hashes)

    _save_run_report_atomic(asdict(report), basename, language, atomic_state)
    return report

def _python_cov_target_for_test_and_code(test_file: Path, code_file: Path, fallback: str) -> str:
    dotted = _python_cov_target_for_code_file(code_file)
    try:
        src = test_file.read_text(encoding="utf-8", errors="ignore")
        if code_file.stem in src: return code_file.stem
    except Exception: pass
    return dotted or fallback

def _python_cov_target_for_code_file(code_file: Path) -> str:
    if code_file.suffix != ".py": return code_file.stem
    curr = code_file.parent
    pkg = None
    while (curr / "__init__.py").exists():
        pkg = curr
        if curr.parent == curr: break
        curr = curr.parent
    if pkg: return str(code_file.relative_to(pkg.parent).with_suffix("")).replace(os.sep, ".")
    return code_file.stem

def _parse_test_output(output: str, language: str) -> tuple[int, int, float]:
    passed = failed = 0
    coverage = 0.0
    lang = language.lower()
    if lang == 'python':
        m = re.search(r'(\d+) passed', output); passed = int(m.group(1)) if m else 0
        m = re.search(r'(\d+) failed', output); failed = int(m.group(1)) if m else 0
        m = re.search(r'(\d+) error', output); failed += int(m.group(1)) if m else 0
        m = re.search(r'TOTAL.*?(\d+)%', output); coverage = float(m.group(1)) if m else 0.0
    elif lang in ('javascript', 'typescript'):
        m = re.search(r'Tests:\s*(\d+)\s+passed', output); passed = int(m.group(1)) if m else 0
        m = re.search(r'Tests:.*?(\d+)\s+failed', output); failed = int(m.group(1)) if m else 0
    return passed, failed, coverage

def _run_example_with_error_detection(cmd: list[str], env: dict, cwd: Optional[str] = None, timeout: int = 60) -> tuple[int, str, str]:
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL, env=env, cwd=cwd, start_new_session=True)
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.terminate(); stdout, stderr = proc.communicate()
    out = stdout.decode('utf-8', errors='replace')
    err = stderr.decode('utf-8', errors='replace')
    has_err, _ = _detect_example_errors(out + "\n" + err)
    rc = proc.returncode if proc.returncode is not None else (1 if has_err else 0)
    return rc, out, err

def _detect_example_errors(output: str) -> tuple[bool, str]:
    if "Traceback (most recent call last):" in output: return True, "Python traceback"
    if " - ERROR - " in output: return True, "Error log message"
    return False, ""

def _try_auto_fix_import_error(error: str, code_file: Path, example_file: Path) -> tuple[bool, str]:
    if "ModuleNotFoundError" not in error and "ImportError" not in error: return False, ""
    m = re.search(r"ModuleNotFoundError: No module named ['\"]([^'\"]+)['\"]", error)
    if m and m.group(1).split('.')[0] == code_file.stem:
        try:
            content = example_file.read_text()
            fix = f"\nimport sys\nsys.path.insert(0, '{code_file.parent.resolve()}')\n"
            example_file.write_text(fix + content)
            return True, "Fixed sys.path"
        except Exception as e: return False, str(e)
    return False, "No auto-fix available"

def _create_mock_context(**kwargs) -> click.Context:
    ctx = click.Context(click.Command('sync'))
    ctx.obj = kwargs
    return ctx

# --- Orchestration ---

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

    if dry_run: return _display_sync_log(basename, language, verbose)

    try:
        pdd_files = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
    except FileNotFoundError:
        from .sync_determine_operation import get_extension
        ext = get_extension(language)
        pdd_files = {
            'prompt': Path(prompts_dir) / f"{basename}_{language}.prompt",
            'code': Path(code_dir) / f"{basename}.{ext}",
            'example': Path(examples_dir) / f"{basename}_example.{ext}",
            'test': Path(tests_dir) / f"test_{basename}.{ext}"
        }

    state_refs = {
        'fn': ["initializing"], 'cost': [0.0], 'stop': threading.Event(),
        'app': [None], 'prog': [None], 'confirmed': [False],
        'paths': {k: [str(v)] for k, v in pdd_files.items()},
        'colors': {k: ["blue"] for k in pdd_files}
    }

    def get_cb():
        if state_refs['confirmed'][0]: return lambda m, t: True
        if state_refs['app'][0]:
            def cb(m, t):
                res = state_refs['app'][0].request_confirmation(m, t)
                if res: state_refs['confirmed'][0] = True
                return res
            return cb
        def headless_cb(m, t):
            res = click.confirm(click.style(m or "Overwrite?", fg="yellow"), default=True)
            if res: state_refs['confirmed'][0] = True
            return res
        return headless_cb

    def worker():
        ops_done, skipped, errs, history = [], [], [], []
        start_t = time.time()
        model = "unknown"
        try:
            with SyncLock(basename, language):
                log_event(basename, language, "lock_acquired", {"pid": os.getpid()}, "sync")
                while True:
                    rem = budget - state_refs['cost'][0]
                    if rem <= 0: errs.append(f"Budget ${budget:.2f} exceeded"); break
                    
                    decision = sync_determine_operation(basename, language, target_coverage, rem, False, prompts_dir, skip_tests, skip_verify, context_override)
                    op = decision.operation
                    if not no_steer:
                        op, abort = maybe_steer_operation(op, decision.reason, state_refs['app'][0], quiet, skip_tests, skip_verify, steer_timeout)
                        if abort: errs.append("User aborted steering"); break

                    history.append(op)
                    if history.count('auto-deps') >= 2 and history[-1] == 'auto-deps': op = 'generate'
                    if len(history) >= 4:
                        if history[-4:] in (['crash', 'verify', 'crash', 'verify'], ['test', 'fix', 'test', 'fix']):
                            errs.append("Infinite cycle detected"); break
                    if history[-5:].count('fix') == 5: errs.append("Max consecutive fixes"); break
                    if history[-3:].count('test') == 3: errs.append("Max consecutive tests"); break
                    if history[-3:].count('crash') == 3: errs.append("Max consecutive crashes"); break

                    if op in ('all_synced', 'nothing'): break
                    if op in ('fail_and_request_manual_merge', 'error'): errs.append(decision.reason); break

                    state_refs['fn'][0] = op
                    ctx = _create_mock_context(force=force, strength=strength, temperature=temperature, time=time_param, verbose=verbose, quiet=quiet, local=local, budget=rem, max_attempts=max_attempts, target_coverage=target_coverage, confirm_callback=get_cb(), context=context_override, agentic_mode=agentic_mode)
                    
                    op_start = time.time()
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
                            # Internal logic for crash checking omitted for brevity, calls crash_main
                            res = crash_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), "crash.log", loop=True)
                        elif op == 'verify':
                            res = fix_verification_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), loop=True)
                        elif op == 'test':
                            res = cmd_test_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), output=str(pdd_files['test']), language=language)
                            if (isinstance(res, tuple) and len(res) >= 4 and res[3]) or pdd_files['test'].exists():
                                if not (isinstance(res, tuple) and len(res) >= 4 and res[3]):
                                    _execute_tests_and_create_run_report(pdd_files['test'], basename, language, target_coverage, code_file=pdd_files['code'], atomic_state=atomic)
                                else:
                                    _create_synthetic_run_report_for_agentic_success(pdd_files['test'], basename, language, atomic_state=atomic)
                        elif op == 'fix':
                            res = fix_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['test']), loop=True)
                            if (isinstance(res, dict) and res.get('success')) or (isinstance(res, tuple) and res[0]):
                                _execute_tests_and_create_run_report(pdd_files['test'], basename, language, target_coverage, code_file=pdd_files['code'], atomic_state=atomic)
                        elif op == 'update':
                            res = update_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), use_git=True)

                        success = False
                        cost = 0.0
                        if isinstance(res, dict):
                            success, cost, model = res.get('success', False), res.get('cost', 0.0), res.get('model', 'unknown')
                        elif isinstance(res, tuple) and len(res) >= 3:
                            success = bool(res[0])
                            cost, model = (res[1], res[2]) if op == 'test' and len(res) >= 4 else (res[-2], res[-1])
                        
                        state_refs['cost'][0] += cost
                        if success:
                            ops_done.append(op)
                            _save_fingerprint_atomic(basename, language, op, pdd_files, cost, model, atomic)
                        else:
                            errs.append(f"Operation {op} failed")
                            break
        except Exception as e:
            errs.append(f"Orchestrator error: {str(e)}")
            traceback.print_exc()
        
        return {
            'success': not errs, 'operations_completed': ops_done, 'skipped_operations': skipped,
            'total_cost': state_refs['cost'][0], 'total_time': time.time() - start_t,
            'final_state': {k: {'exists': v.exists(), 'path': str(v)} for k, v in pdd_files.items()},
            'errors': errs, 'error': "; ".join(errs) if errs else None, 'model_name': model
        }

    headless = quiet or not sys.stdout.isatty() or os.environ.get('CI')
    if headless:
        os.environ['PDD_FORCE'] = '1'
        return worker()
    else:
        app = SyncApp(basename, budget, worker, state_refs['fn'], state_refs['cost'], 
                      [str(pdd_files['prompt'])], [str(pdd_files['code'])], [str(pdd_files['example'])], [str(pdd_files['test'])],
                      ["blue"], ["blue"], ["blue"], ["blue"], state_refs['stop'])
        state_refs['app'][0] = app
        res = app.run()
        from .sync_tui import show_exit_animation
        if not quiet: show_exit_animation()
        return res or {"success": False, "errors": ["Interrupted"]}

def _display_sync_log(basename: str, language: str, verbose: bool = False) -> Dict[str, Any]:
    entries = load_operation_log(basename, language)
    for e in entries: print(f"[{e.get('timestamp')}] {e.get('operation')} - {e.get('reason')}")
    return {'success': True, 'log_entries': entries}