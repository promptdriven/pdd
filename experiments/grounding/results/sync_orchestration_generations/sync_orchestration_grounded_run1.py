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
from pathlib import Path
typing import Dict, Any, Optional, List, Callable
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

def _python_cov_target_for_code_file(code_file: Path) -> str:
    if code_file.suffix != ".py": return code_file.stem
    pkg_dir: Optional[Path] = None
    curr = code_file.parent
    while (curr / "__init__.py").exists():
        pkg_dir = curr
        parent = curr.parent
        if parent == curr: break
        curr = parent
    if pkg_dir:
        rel = code_file.relative_to(pkg_dir.parent).with_suffix("")
        return str(rel).replace(os.sep, ".")
    return code_file.stem

def _python_cov_target_for_test_and_code(test_file: Path, code_file: Path, fallback: str) -> str:
    def _imports(src, mod):
        return bool(re.search(rf"^\s*(import|from)\s+{re.escape(mod)}\b", src, re.M))
    stem = code_file.stem
    dotted = _python_cov_target_for_code_file(code_file)
    try: src = test_file.read_text(encoding="utf-8", errors="ignore")
    except: src = ""
    if stem and _imports(src, stem): return stem
    if dotted and dotted != stem and _imports(src, dotted): return dotted
    return stem or fallback

def _parse_test_output(output: str, language: str) -> tuple[int, int, float]:
    passed, failed, coverage = 0, 0, 0.0
    lang = language.lower()
    if lang == 'python':
        m = re.search(r'(\d+) passed', output); passed = int(m.group(1)) if m else 0
        m = re.search(r'(\d+) failed', output); failed = int(m.group(1)) if m else 0
        m = re.search(r'(\d+) error', output); failed += int(m.group(1)) if m else 0
        m = re.search(r'TOTAL.*?(\d+)%', output) or re.search(r'(\d+(?:\.\d+)?)%', output)
        if m: coverage = float(m.group(1))
    elif lang in ('javascript', 'typescript', 'typescriptreact'):
        m = re.search(r'Tests:\s*(\d+)\s+passed', output); passed = int(m.group(1)) if m else 0
        m = re.search(r'Tests:.*?(\d+)\s+failed', output); failed = int(m.group(1)) if m else 0
        m = re.search(r'All files[^|]*\|\s*(\d+\.?\d*)', output); coverage = float(m.group(1)) if m else 0.0
    elif lang == 'go':
        passed = len(re.findall(r'--- PASS:', output))
        failed = len(re.findall(r'--- FAIL:', output))
        m = re.search(r'coverage:\s*(\d+\.?\d*)%', output); coverage = float(m.group(1)) if m else 0.0
    return passed, failed, coverage

def _detect_example_errors(output: str) -> tuple[bool, str]:
    if re.search(r'Traceback \(most recent call last\):', output, re.M): return True, 'Python traceback'
    if re.search(r' - ERROR - ', output, re.M): return True, 'Error log message'
    return False, ''

def _run_example_with_error_detection(cmd_parts: list[str], env: dict, cwd: Optional[str] = None, timeout: int = 60) -> tuple[int, str, str]:
    proc = subprocess.Popen(cmd_parts, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL, env=env, cwd=cwd, start_new_session=True)
    out_chunks, err_chunks = [], []
    def read(p, c):
        try:
            for line in iter(p.readline, b''):
                c.append(line)
        except: pass
    t1 = threading.Thread(target=read, args=(proc.stdout, out_chunks), daemon=True)
    t2 = threading.Thread(target=read, args=(proc.stderr, err_chunks), daemon=True)
    t1.start(); t2.start()
    try: proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.terminate()
        try: proc.wait(timeout=5)
        except subprocess.TimeoutExpired: proc.kill(); proc.wait()
    t1.join(2); t2.join(2)
    stdout = b''.join(out_chunks).decode('utf-8', errors='replace')
    stderr = b''.join(err_chunks).decode('utf-8', errors='replace')
    has_err, _ = _detect_example_errors(stdout + '\n' + stderr)
    if proc.returncode is not None and proc.returncode == 0: return 0, stdout, stderr
    if proc.returncode is not None and proc.returncode > 0: return proc.returncode, stdout, stderr
    return (1 if has_err else 0), stdout, stderr

def _try_auto_fix_import_error(error_output: str, code_file: Path, example_file: Path) -> tuple[bool, str]:
    m1 = re.search(r"ModuleNotFoundError: No module named ['\"]([^'\"]+)['\"]", error_output)
    if m1:
        pkg = m1.group(1).split('.')[0]
        if pkg == code_file.stem:
            try:
                content = example_file.read_text(encoding='utf-8')
                code_dir = str(code_file.parent.resolve())
                if 'sys.path' in content:
                    fixed = re.sub(r"module_path\s*=\s*os\.path\.abspath\([^)]+\)", f"module_path = '{code_dir}'", content)
                    example_file.write_text(fixed, encoding='utf-8')
                    return True, f"Fixed sys.path to {code_dir}"
                lines = content.split('\n')
                fix = f"\nimport sys\nsys.path.insert(0, '{code_dir}')\n"
                lines.insert(0, fix); example_file.write_text('\n'.join(lines), encoding='utf-8')
                return True, f"Added sys.path for {code_dir}"
            except: return False, "Path fix failed"
        else:
            try:
                res = subprocess.run([sys.executable, '-m', 'pip', 'install', pkg], capture_output=True, timeout=60)
                return (True, f"Installed {pkg}") if res.returncode == 0 else (False, f"Install failed {pkg}")
            except: return False, "pip failed"
    return False, ""

def _create_synthetic_run_report_for_agentic_success(test_file: Path, basename: str, language: str, *, atomic_state: Optional[AtomicStateUpdate] = None) -> RunReport:
    report = RunReport(
        timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        exit_code=0, tests_passed=1, tests_failed=0, coverage=0.0,
        test_hash=calculate_sha256(test_file) if test_file.exists() else "agentic_test_success"
    )
    report_file = META_DIR / f"{_safe_basename(basename)}_{language.lower()}_run.json"
    if atomic_state: atomic_state.set_run_report(asdict(report), report_file)
    else:
        report_file.parent.mkdir(parents=True, exist_ok=True)
        report_file.write_text(json.dumps(asdict(report), indent=2))
    return report

def _execute_tests_and_create_run_report(test_file: Path, basename: str, language: str, target_coverage: float = 90.0, *, code_file: Optional[Path] = None, atomic_state: Optional[AtomicStateUpdate] = None, test_files: Optional[List[Path]] = None) -> RunReport:
    from .get_test_command import get_test_command_for_file
    all_files = test_files if test_files else [test_file]
    clean_env = os.environ.copy()
    for v in ['FORCE_COLOR', 'COLUMNS']: clean_env.pop(v, None)
    try:
        if language.lower() == 'python':
            python = detect_host_python_executable()
            cov_t = _python_cov_target_for_test_and_code(test_file, code_file, basename) if code_file else basename
            root = _find_project_root(test_file)
            args = [python, '-m', 'pytest'] + [str(f) for f in all_files] + ['-v', '--tb=short', f'--cov={cov_t}', '--cov-report=term-missing']
            kw = {'capture_output': True, 'text': True, 'timeout': 300, 'env': clean_env, 'stdin': subprocess.DEVNULL, 'start_new_session': True}
            if root:
                clean_env["PYTHONPATH"] = os.pathsep.join(filter(None, [str(root / "src"), str(root), clean_env.get("PYTHONPATH")]))
                args.extend([f'--rootdir={root}', '-c', '/dev/null'])
                kw['cwd'] = str(root)
            res = subprocess.run(args, **kw)
            passed, failed, cov = _parse_test_output(res.stdout + res.stderr, language)
            rc = res.returncode
        else:
            cmd = get_test_command_for_file(str(test_file), language)
            if not cmd:
                report = RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 127, 0, 0, 0.0)
                _save_run_report_atomic(asdict(report), basename, language, atomic_state); return report
            res = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=300, env=clean_env, cwd=str(test_file.parent), start_new_session=True)
            passed, failed, cov = _parse_test_output(res.stdout + res.stderr, language)
            rc = res.returncode
        report = RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), rc, passed, failed, cov,
                           test_hash=calculate_sha256(test_file) if test_file.exists() else None,
                           test_files={f.name: calculate_sha256(f) for f in all_files if f.exists()} if test_files else None)
    except:
        report = RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 1, 0, 1, 0.0)
    _save_run_report_atomic(asdict(report), basename, language, atomic_state)
    return report

def _create_mock_context(**kwargs) -> click.Context:
    ctx = click.Context(click.Command('sync'))
    ctx.obj = kwargs
    return ctx

def _display_sync_log(basename: str, language: str, verbose: bool = False) -> Dict[str, Any]:
    log_file = META_DIR / f"{_safe_basename(basename)}_{language.lower()}_sync.log"
    if not log_file.exists(): return {'success': False, 'errors': ['Log not found.']}
    entries = load_operation_log(basename, language)
    for e in entries:
        ts = e.get('timestamp', '')[:19]
        if 'event' in e: print(f"[{ts}] EVENT: {e['event']}"); continue
        op, reas = e.get('operation', 'N/A'), e.get('reason', 'N/A')
        cost = e.get('actual_cost', 0.0)
        print(f"[{ts}] {op:<12} | {reas} | ${cost:.2f}")
    return {'success': True, 'log_entries': entries}

# --- Orchestration ---

def sync_orchestration(basename: str, target_coverage: float = 90.0, language: str = "python", prompts_dir: str = "prompts", code_dir: str = "src", examples_dir: str = "examples", tests_dir: str = "tests", max_attempts: int = 3, budget: float = 10.0, skip_verify: bool = False, skip_tests: bool = False, dry_run: bool = False, force: bool = False, strength: float = DEFAULT_STRENGTH, temperature: float = 0.0, time_param: float = 0.25, verbose: bool = False, quiet: bool = False, output_cost: Optional[str] = None, review_examples: bool = False, local: bool = False, context_config: Optional[Dict[str, str]] = None, context_override: Optional[str] = None, confirm_callback: Optional[Callable[[str, str], bool]] = None, no_steer: bool = False, steer_timeout: float = DEFAULT_STEER_TIMEOUT_S, agentic_mode: bool = False) -> Dict[str, Any]:
    target_coverage = target_coverage or 90.0
    budget = budget or 10.0
    max_attempts = max_attempts or 3
    from .sync_determine_operation import get_extension
    if dry_run: return _display_sync_log(basename, language, verbose)
    try:
        pdd_files = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
    except FileNotFoundError:
        pdd_files = {'prompt': Path(prompts_dir)/f"{basename}_{language}.prompt", 'code': Path(f"src/{basename}.{get_extension(language)}"), 'example': Path(f"context/{basename}_example.{get_extension(language)}"), 'test': Path(f"tests/test_{basename}.{get_extension(language)}")}

    shared = {"func": ["initializing"], "cost": [0.0], "stop": threading.Event(), "app": [None], "overwrite": [False], "prog": [None]}

    def get_cb():
        if shared["overwrite"][0]: return lambda m, t: True
        if shared["app"][0]:
            def cb(m, t):
                res = shared["app"][0].request_confirmation(m, t)
                if res: shared["overwrite"][0] = True
                return res
            return cb
        if confirm_callback is None:
            def headless_cb(m, t):
                try: res = click.confirm(click.style(m or "Overwrite?", fg="yellow"), default=True)
                except: res = False
                if res: shared["overwrite"][0] = True
                return res
            return headless_cb
        return confirm_callback

    def sync_worker():
        ops_done, skipped, errors, history = [], [], [], []
        start = time.time()
        model = "unknown"
        try:
            with SyncLock(basename, language):
                log_event(basename, language, "lock_acquired", {"pid": os.getpid()}, "sync")
                while True:
                    rem = budget - shared["cost"][0]
                    if rem <= 0: errors.append(f"Budget ${budget:.2f} exceeded"); break
                    dec = sync_determine_operation(basename, language, target_coverage, rem, False, prompts_dir, skip_tests, skip_verify, context_override)
                    op = dec.operation
                    if not no_steer:
                        op, abort = maybe_steer_operation(op, dec.reason, shared["app"][0], quiet, skip_tests, skip_verify, steer_timeout)
                        if abort: errors.append("User aborted"); break
                    history.append(op)
                    if len(history) >= 3 and history[-3:].count('auto-deps') >= 2: op = 'generate'
                    if len(history) >= 4:
                        if history[-4:] in (['crash','verify','crash','verify'], ['verify','crash','verify','crash']): errors.append("Crash-verify loop"); break
                        if history[-4:] in (['test','fix','test','fix'], ['fix','test','fix','test']): errors.append("Test-fix loop"); break
                    if history.count('fix') >= 5: errors.append("Fix limit"); break
                    if history.count('test') >= MAX_CONSECUTIVE_TESTS: errors.append("Test limit"); break
                    if history.count('crash') >= MAX_CONSECUTIVE_CRASHES: errors.append("Crash limit"); break
                    if op == 'test_extend' and (_use_agentic_path(language, agentic_mode) or sum(1 for x in history if x=='test_extend') >= MAX_TEST_EXTEND_ATTEMPTS): break
                    if op in ('all_synced','nothing','fail_and_request_manual_merge','error'): break
                    
                    if op == 'verify' and (skip_verify or skip_tests):
                        skipped.append('verify'); _save_fingerprint_atomic(basename, language, 'skip:verify', pdd_files, 0.0, 'skipped'); continue
                    if op == 'test' and skip_tests:
                        skipped.append('test'); _save_fingerprint_atomic(basename, language, 'skip:test', pdd_files, 0.0, 'skipped'); continue
                    if op == 'crash' and (skip_tests or skip_verify):
                        skipped.append('crash'); _save_fingerprint_atomic(basename, language, 'skip:crash', pdd_files, 0.0, 'skipped')
                        _save_run_report_atomic(asdict(RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 0, 0, 0, 0.0)), basename, language); continue

                    shared["func"][0] = op
                    ctx = _create_mock_context(force=force, strength=strength, temperature=temperature, time=time_param, verbose=verbose, quiet=quiet, output_cost=output_cost, review_examples=review_examples, local=local, budget=rem, max_attempts=max_attempts, target_coverage=target_coverage, confirm_callback=get_cb(), context=context_override, agentic_mode=agentic_mode)
                    success, cost, op_start = False, 0.0, time.time()
                    with AtomicStateUpdate(basename, language) as atomic:
                        try:
                            if op == 'auto-deps':
                                res = auto_deps_main(ctx, str(pdd_files['prompt']), examples_dir, "project_dependencies.csv", str(pdd_files['prompt']), False, shared["prog"][0])
                            elif op == 'generate':
                                pdd_files['code'].parent.mkdir(parents=True, exist_ok=True)
                                res = code_generator_main(ctx, str(pdd_files['prompt'].resolve()), str(pdd_files['code'].resolve()), None, False)
                                clear_run_report(basename, language)
                            elif op == 'example':
                                pdd_files['example'].parent.mkdir(parents=True, exist_ok=True)
                                res = context_generator_main(ctx, str(pdd_files['prompt'].resolve()), str(pdd_files['code'].resolve()), str(pdd_files['example'].resolve()))
                            elif op == 'crash':
                                if not pdd_files['code'].exists() or not pdd_files['example'].exists(): skipped.append('crash'); continue
                                has_crash = False
                                if _use_agentic_path(language, agentic_mode): has_crash = True
                                else:
                                    env = os.environ.copy(); env['PYTHONPATH'] = f"{pdd_files['code'].resolve().parent}:{env.get('PYTHONPATH','')}"
                                    for v in ['FORCE_COLOR','COLUMNS']: env.pop(v,None)
                                    rc, out, err = _run_example_with_error_detection([sys.executable, str(pdd_files['example'].resolve())], env, timeout=60)
                                    if rc != 0: has_crash = True
                                    else:
                                        _save_run_report_atomic(asdict(RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 0, 1, 0, 0.0)), basename, language)
                                        skipped.append('crash'); continue
                                if has_crash:
                                    eff_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                    Path("crash.log").write_text(f"Crash detected in {language}")
                                    res = crash_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), "crash.log", str(pdd_files['code']), str(pdd_files['example']), True, eff_max, rem, strength, temperature)
                            elif op == 'verify':
                                eff_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                res = fix_verification_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), f"{basename.replace('/','_')}_verify.log", str(pdd_files['code']), str(pdd_files['example']), True, str(pdd_files['example']), eff_max, rem, agentic_fallback=True)
                            elif op in ('test', 'test_extend'):
                                pdd_files['test'].parent.mkdir(parents=True, exist_ok=True)
                                merge = pdd_files['test'].exists() if op == 'test' else True
                                res = cmd_test_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['test']), language, merge=merge, strength=strength, temperature=temperature)
                                if isinstance(res, tuple) and len(res) >= 4 and res[3] is True:
                                    _create_synthetic_run_report_for_agentic_success(pdd_files['test'], basename, language, atomic_state=atomic)
                                elif pdd_files['test'].exists():
                                    _execute_tests_and_create_run_report(pdd_files['test'], basename, language, target_coverage, code_file=pdd_files['code'], atomic_state=atomic, test_files=pdd_files.get('test_files'))
                            elif op == 'fix':
                                eff_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                res = fix_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['test']), "fix_errors.log", str(pdd_files['test']), str(pdd_files['code']), f"{basename.replace('/','_')}_fix.log", True, str(pdd_files['example']), eff_max, rem, not local, strength, temperature)
                            elif op == 'update':
                                res = update_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), None, str(pdd_files['prompt']), True, strength, temperature)
                            
                            if isinstance(res, dict): success, cost = res.get('success', False), res.get('cost', 0.0); model = res.get('model', 'unknown')
                            elif isinstance(res, tuple):
                                if op == 'test': success = res[3] if len(res) >= 4 and res[3] is not None else pdd_files['test'].exists(); cost = res[1]; model = res[2]
                                else: success = bool(res[0]); cost = res[-2]; model = res[-1]
                            shared["cost"][0] += cost
                            if success:
                                ops_done.append(op)
                                _save_fingerprint_atomic(basename, language, op, pdd_files, cost, str(model), atomic)
                                if op == 'crash':
                                    if _use_agentic_path(language, agentic_mode):
                                        _save_run_report_atomic(asdict(RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 0, 1, 0, 0.0)), basename, language, atomic)
                                    else:
                                        env = os.environ.copy(); env['PYTHONPATH'] = f"{pdd_files['code'].resolve().parent}:{env.get('PYTHONPATH','')}"
                                        rc, _, _ = _run_example_with_error_detection([sys.executable, str(pdd_files['example'].resolve())], env, timeout=60)
                                        _save_run_report_atomic(asdict(RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), rc, 1 if rc==0 else 0, 0 if rc==0 else 1, 0.0)), basename, language, atomic)
                                if op == 'fix':
                                    if _use_agentic_path(language, agentic_mode):
                                        _save_run_report_atomic(asdict(RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 0, 1, 0, 0.0)), basename, language, atomic)
                                    elif pdd_files['test'].exists():
                                        _execute_tests_and_create_run_report(pdd_files['test'], basename, language, target_coverage, code_file=pdd_files['code'], atomic_state=atomic, test_files=pdd_files.get('test_files'))
                            else: errors.append(f"Op '{op}' failed"); break
                        except click.Abort: errors.append(f"'{op}' cancelled"); break
                        except Exception as e: errors.append(f"'{op}' error: {e}"); break
        except Exception as e: errors.append(f"Sync error: {e}")
        return {'success': not errors, 'operations_completed': ops_done, 'skipped_operations': skipped, 'total_cost': shared["cost"][0], 'total_time': time.time() - start, 'final_state': {p: {'exists': f.exists(), 'path': str(f)} for p, f in pdd_files.items() if p != 'test_files'}, 'errors': errors, 'model_name': model}

    headless = quiet or not sys.stdout.isatty() or os.environ.get('CI')
    if headless:
        os.environ['PDD_FORCE'] = '1'
        return sync_worker()
    
    # Note: These path and color references would typically be defined in the calling scope or sync_tui
    # For the purpose of this extraction, we assume they are available or handled by SyncApp
    app = SyncApp(basename, budget, sync_worker, shared["func"], shared["cost"], None, None, None, None, None, None, None, None, shared["stop"], shared["prog"])
    shared["app"][0] = app
    res = app.run()
    from .sync_tui import show_exit_animation
    if not quiet: show_exit_animation()
    return res or {'success': False, 'error': 'App exited'}

if __name__ == '__main__':
    res = sync_orchestration("example", language="python", quiet=True)
    print(json.dumps(res, indent=2))"
}