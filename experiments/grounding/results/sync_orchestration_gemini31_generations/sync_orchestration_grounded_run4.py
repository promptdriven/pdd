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
from pathlib import Path
from typing import Dict, Any, Optional, List, Callable
from dataclasses import asdict, dataclass, field
import tempfile
import sys
import traceback

from .sync_tui import maybe_steer_operation, DEFAULT_STEER_TIMEOUT_S

import click
import logging

# --- Constants ---
MAX_CONSECUTIVE_TESTS = 3
MAX_TEST_EXTEND_ATTEMPTS = 2
MAX_CONSECUTIVE_CRASHES = 3

# --- Real PDD Component Imports ---
from .sync_tui import SyncApp
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

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Returns True if we should use agentic path (non-Python OR agentic_mode for Python)."""
    return language.lower() != 'python' or agentic_mode


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
        fd, temp_path = tempfile.mkstemp(
            dir=target_path.parent,
            prefix=f".{target_path.stem}_",
            suffix=".tmp"
        )
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
                if os.path.exists(temp_path):
                    os.unlink(temp_path)
            except OSError:
                pass
        self._temp_files.clear()

def _save_run_report_atomic(report: Dict[str, Any], basename: str, language: str,
                    atomic_state: Optional['AtomicStateUpdate'] = None):
    if atomic_state:
        report_file = META_DIR / f"{_safe_basename(basename)}_{language.lower()}_run.json"
        atomic_state.set_run_report(report, report_file)
    else:
        save_run_report(basename, language, report)

def _save_fingerprint_atomic(basename: str, language: str, operation: str,
                               paths: Dict[str, Path], cost: float, model: str,
                               atomic_state: Optional['AtomicStateUpdate'] = None):
    if atomic_state:
        from datetime import datetime, timezone
        from .sync_determine_operation import calculate_current_hashes, Fingerprint
        from . import __version__
        current_hashes = calculate_current_hashes(paths)
        fingerprint = Fingerprint(
            pdd_version=__version__,
            timestamp=datetime.now(timezone.utc).isoformat(),
            command=operation,
            prompt_hash=current_hashes.get('prompt_hash'),
            code_hash=current_hashes.get('code_hash'),
            example_hash=current_hashes.get('example_hash'),
            test_hash=current_hashes.get('test_hash'),
            test_files=current_hashes.get('test_files'),
        )
        fingerprint_file = META_DIR / f"{_safe_basename(basename)}_{language.lower()}.json"
        atomic_state.set_fingerprint(asdict(fingerprint), fingerprint_file)
    else:
        save_fingerprint(basename, language, operation, paths, cost, model)

def _python_cov_target_for_code_file(code_file: Path) -> str:
    if code_file.suffix != ".py":
        return code_file.stem
    package_dir = None
    current = code_file.parent
    while (current / "__init__.py").exists():
        package_dir = current
        parent = current.parent
        if parent == current:
            break
        current = parent
    if package_dir:
        relative_module = code_file.relative_to(package_dir.parent).with_suffix("")
        return str(relative_module).replace(os.sep, ".")
    return code_file.stem

def _python_cov_target_for_test_and_code(test_file: Path, code_file: Path, fallback: str) -> str:
    def _imports_module(source: str, module: str) -> bool:
        escaped = re.escape(module)
        return bool(
            re.search(rf"^\s*import\s+{escaped}\b", source, re.MULTILINE)
            or re.search(rf"^\s*from\s+{escaped}\b", source, re.MULTILINE)
        )
    stem = code_file.stem
    dotted = _python_cov_target_for_code_file(code_file)
    try:
        test_source = test_file.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        test_source = ""
    if stem and _imports_module(test_source, stem):
        return stem
    if dotted and dotted != stem:
        if _imports_module(test_source, dotted):
            return dotted
        if "." in dotted:
            parent = dotted.rsplit(".", 1)[0]
            if re.search(rf"^\s*from\s+{re.escape(parent)}\s+import\s+.*\b{re.escape(stem)}\b", test_source, re.MULTILINE):
                return dotted
            if re.search(rf"^\s*import\s+{re.escape(parent)}\.{re.escape(stem)}\b", test_source, re.MULTILINE):
                return dotted
        return dotted
    return stem or fallback

def _parse_test_output(output: str, language: str) -> tuple[int, int, float]:
    tests_passed = 0
    tests_failed = 0
    coverage = 0.0
    lang = language.lower()

    if lang == 'python':
        if 'passed' in output:
            pm = re.search(r'(\d+) passed', output)
            if pm: tests_passed = int(pm.group(1))
        if 'failed' in output:
            fm = re.search(r'(\d+) failed', output)
            if fm: tests_failed = int(fm.group(1))
        if 'error' in output:
            em = re.search(r'(\d+) error', output)
            if em: tests_failed += int(em.group(1))
        cm = re.search(r'TOTAL.*?(\d+)%', output) or re.search(r'(\d+)%\s*$', output, re.MULTILINE) or re.search(r'(\d+(?:\.\d+)?)%', output)
        if cm: coverage = float(cm.group(1))
    elif lang in ('javascript', 'typescript', 'typescriptreact'):
        m = re.search(r'Tests:\s*(\d+)\s+passed', output)
        if m: tests_passed = int(m.group(1))
        m = re.search(r'Tests:.*?(\d+)\s+failed', output)
        if m: tests_failed = int(m.group(1))
        if tests_passed == 0:
            pm = re.search(r'(\d+)\s+pass(?:ing)?', output, re.I)
            if pm: tests_passed = int(pm.group(1))
        if tests_failed == 0:
            fm = re.search(r'(\d+)\s+fail(?:ing)?', output, re.I)
            if fm: tests_failed = int(fm.group(1))
        cm = re.search(r'All files[^|]*\|\s*(\d+\.?\d*)', output)
        if cm: coverage = float(cm.group(1))
    elif lang == 'go':
        tests_passed = len(re.findall(r'--- PASS:', output))
        tests_failed = len(re.findall(r'--- FAIL:', output))
        if tests_passed == 0 and 'PASS' in output and 'FAIL' not in output: tests_passed = 1
        if tests_failed == 0 and 'FAIL' in output: tests_failed = 1
        cm = re.search(r'coverage:\s*(\d+\.?\d*)%', output)
        if cm: coverage = float(cm.group(1))
    elif lang == 'rust':
        m = re.search(r'(\d+)\s+passed', output)
        if m: tests_passed = int(m.group(1))
        m = re.search(r'(\d+)\s+failed', output)
        if m: tests_failed = int(m.group(1))
    else:
        pm = re.search(r'(\d+)\s+(?:tests?\s+)?pass(?:ed)?', output, re.I)
        fm = re.search(r'(\d+)\s+(?:tests?\s+)?fail(?:ed)?', output, re.I)
        if pm: tests_passed = int(pm.group(1))
        if fm: tests_failed = int(fm.group(1))
    return tests_passed, tests_failed, coverage

def _detect_example_errors(output: str) -> tuple[bool, str]:
    errors_found = []
    for pattern, desc in [(r'Traceback \(most recent call last\):', 'Python traceback'), (r' - ERROR - ', 'Error log message')]:
        if re.search(pattern, output, re.MULTILINE):
            errors_found.append(desc)
    if errors_found:
        return True, '; '.join(errors_found)
    return False, ''

def _try_auto_fix_import_error(error_output: str, code_file: Path, example_file: Path) -> tuple[bool, str]:
    mnf = re.search(r"ModuleNotFoundError: No module named ['\"]([^'\"]+)['\"]", error_output)
    ie = re.search(r"ImportError: cannot import name ['\"]([^'\"]+)['\"]", error_output)
    if not mnf and not ie:
        return False, "No import error detected"
    if mnf:
        mm = mnf.group(1)
        top = mm.split('.')[0]
        if top == code_file.stem:
            try:
                content = example_file.read_text('utf-8')
                cdir = str(code_file.parent.resolve())
                if 'sys.path' in content:
                    fc = re.sub(r"module_path\s*=\s*os\.path\.abspath\([^)]+\)", f"module_path = '{cdir}'", content)
                    if fc != content:
                        example_file.write_text(fc, 'utf-8')
                        return True, f"Fixed sys.path to {cdir}"
                lines = content.split('\n')
                pos = 0
                for i, line in enumerate(lines):
                    if line.startswith('import ') or line.startswith('from '):
                        if 'sys' in line or 'os' in line:
                            pos = i + 1
                            continue
                    if line.strip() and not line.startswith('#') and not line.startswith('import') and not line.startswith('from'):
                        pos = i
                        break
                lines.insert(pos, f"\n# Auto-added by pdd\nimport sys\nsys.path.insert(0, '{cdir}')\n")
                example_file.write_text('\n'.join(lines), 'utf-8')
                return True, f"Added sys.path.insert for {cdir}"
            except Exception as e:
                return False, f"Failed fix: {e}"
        else:
            try:
                res = subprocess.run([sys.executable, '-m', 'pip', 'install', top], capture_output=True, text=True, timeout=120)
                if res.returncode == 0:
                    return True, f"Installed {top}"
                return False, f"pip fail: {res.stderr}"
            except Exception as e:
                return False, str(e)
    return False, "No fix available"

def _run_example_with_error_detection(cmd_parts: list[str], env: dict, cwd: Optional[str] = None, timeout: int = 60) -> tuple[int, str, str]:
    proc = subprocess.Popen(
        cmd_parts, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL,
        env=env, cwd=cwd, start_new_session=True,
    )
    so, se = [], []
    def rp(p, ch):
        try:
            for line in iter(p.readline, b''): ch.append(line)
        except: pass
    t1, t2 = threading.Thread(target=rp, args=(proc.stdout, so), daemon=True), threading.Thread(target=rp, args=(proc.stderr, se), daemon=True)
    t1.start(); t2.start()
    try:
        proc.wait(timeout)
    except subprocess.TimeoutExpired:
        proc.terminate()
        try: proc.wait(5)
        except: proc.kill(); proc.wait()
    t1.join(2); t2.join(2)
    sout = b''.join(so).decode('utf-8', 'replace')
    serr = b''.join(se).decode('utf-8', 'replace')
    he, summ = _detect_example_errors(sout + '\n' + serr)
    if proc.returncode is not None and proc.returncode == 0:
        return 0, sout, serr
    if proc.returncode is not None and proc.returncode > 0:
        return proc.returncode, sout, serr
    if he: return 1, sout, serr
    return 0, sout, serr

def _create_synthetic_run_report_for_agentic_success(test_file: Path, basename: str, language: str, *, atomic_state: Optional['AtomicStateUpdate'] = None) -> RunReport:
    ts = datetime.datetime.now(datetime.timezone.utc).isoformat()
    th = calculate_sha256(test_file) if test_file.exists() else "agentic_test_success"
    rep = RunReport(timestamp=ts, exit_code=0, tests_passed=1, tests_failed=0, coverage=0.0, test_hash=th)
    rf = META_DIR / f"{_safe_basename(basename)}_{language.lower()}_run.json"
    if atomic_state:
        atomic_state.set_run_report(asdict(rep), rf)
    else:
        rf.parent.mkdir(parents=True, exist_ok=True)
        rf.write_text(json.dumps(asdict(rep), indent=2))
    return rep

def _execute_tests_and_create_run_report(
    test_file: Path, basename: str, language: str, target_coverage: float = 90.0, *,
    code_file: Optional[Path] = None, atomic_state: Optional['AtomicStateUpdate'] = None, test_files: Optional[List[Path]] = None
) -> RunReport:
    from .get_test_command import get_test_command_for_file
    ts = datetime.datetime.now(datetime.timezone.utc).isoformat()
    atf = test_files if test_files else [test_file]
    th = calculate_sha256(test_file) if test_file.exists() else None
    tfh = {f.name: calculate_sha256(f) for f in atf if f.exists()} if atf else None
    cenv = os.environ.copy()
    for v in ['FORCE_COLOR', 'COLUMNS']: cenv.pop(v, None)

    try:
        ll = language.lower()
        if ll == 'python':
            mn = test_file.name.replace('test_', '').replace('.py', '')
            pe = detect_host_python_executable()
            ct = _python_cov_target_for_test_and_code(test_file, code_file, basename or mn) if code_file else basename or mn
            if not ct: ct = basename or mn
            pr = _find_project_root(test_file)
            pa = [pe, '-m', 'pytest'] + [str(f) for f in atf] + ['-v', '--tb=short', f'--cov={ct}', '--cov-report=term-missing']
            cw = None
            if pr:
                pta = [str(pr)]
                sd = pr / "src"
                if sd.is_dir(): pta.insert(0, str(sd))
                ep = cenv.get("PYTHONPATH", "")
                if ep: pta.append(ep)
                cenv["PYTHONPATH"] = os.pathsep.join(pta)
                pa.extend([f'--rootdir={pr}', '-c', '/dev/null'])
                cw = str(pr)
            sk = {'capture_output': True, 'text': True, 'timeout': 300, 'stdin': subprocess.DEVNULL, 'env': cenv, 'start_new_session': True}
            if cw: sk['cwd'] = cw
            res = subprocess.run(pa, **sk)
            ec = res.returncode
            out = res.stdout + (res.stderr or '')
            tp, tf, cov = _parse_test_output(out, language)
        else:
            tc = get_test_command_for_file(str(test_file), language)
            if tc is None:
                rep = RunReport(timestamp=ts, exit_code=127, tests_passed=0, tests_failed=0, coverage=0.0, test_hash=th, test_files=tfh)
                _save_run_report_atomic(asdict(rep), basename, language, atomic_state)
                return rep
            res = subprocess.run(tc, shell=True, capture_output=True, text=True, timeout=300, env=cenv, cwd=str(test_file.parent), stdin=subprocess.DEVNULL, start_new_session=True)
            ec = res.returncode
            out = (res.stdout or '') + '\n' + (res.stderr or '')
            tp, tf, cov = _parse_test_output(out, language)
        rep = RunReport(timestamp=ts, exit_code=ec, tests_passed=tp, tests_failed=tf, coverage=cov, test_hash=th, test_files=tfh)
    except Exception:
        rep = RunReport(timestamp=ts, exit_code=1, tests_passed=0, tests_failed=1, coverage=0.0, test_hash=th, test_files=tfh)
    _save_run_report_atomic(asdict(rep), basename, language, atomic_state)
    return rep

def _create_mock_context(**kwargs) -> click.Context:
    ctx = click.Context(click.Command('sync'))
    ctx.obj = kwargs
    return ctx

def _display_sync_log(basename: str, language: str, verbose: bool = False) -> Dict[str, Any]:
    log_file = META_DIR / f"{_safe_basename(basename)}_{language.lower()}_sync.log"
    if not log_file.exists():
        print(f"No sync log found for '{basename}' in language '{language}'.")
        return {'success': False, 'errors': ['Log file not found.'], 'log_entries': []}
    le = load_operation_log(basename, language)
    print(f"--- Sync Log for {basename} ({language}) ---")
    if not le:
        print("Log is empty.")
        return {'success': True, 'log_entries': []}
    for e in le:
        ts = e.get('timestamp', 'N/A')
        if 'event' in e:
            print(f"[{ts[:19]}] EVENT: {e.get('event')}")
            if verbose and 'details' in e: print(f"  Details: {json.dumps(e['details'], indent=2)}")
            continue
        op = e.get('operation', 'N/A')
        rs = e.get('reason', 'N/A')
        suc = e.get('success')
        ac = e.get('actual_cost')
        ec = e.get('estimated_cost', 0.0)
        du = e.get('duration')
        if verbose:
            print(f"[{ts[:19]}] {op:<12} | {rs}")
            print(f"  Decision Type: {e.get('decision_type', 'N/A')} | Confidence: {e.get('confidence', 'N/A')}")
            if ac is not None:
                print(f"  Cost: ${ac:.2f} (est: ${ec:.2f}) | Model: {e.get('model', 'N/A')}")
                if du is not None: print(f"  Duration: {du:.1f}s | Budget Remaining: ${e.get('details', {}).get('budget_remaining', 'N/A')}")
            else:
                print(f"  Estimated Cost: ${ec:.2f}")
            if 'details' in e and e['details']:
                dc = dict(e['details'])
                dc.pop('budget_remaining', None)
                if dc: print(f"  Details: {json.dumps(dc, indent=2)}")
        else:
            si = "✓" if suc else "✗" if suc is False else "?"
            ci = f" | {si} ${ac:.2f} (est: ${ec:.2f})" if ac is not None else f" | Est: ${ec:.2f}"
            di = f" | {du:.1f}s" if du is not None else ""
            ei = f" | Error: {e['error']}" if e.get('error') else ""
            print(f"[{ts[:19]}] {op:<12} | {rs}{ci}{di}{ei}")
    print("--- End of Log ---")
    return {'success': True, 'log_entries': le}

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
    if target_coverage is None: target_coverage = 90.0
    if budget is None: budget = 10.0
    if max_attempts is None: max_attempts = 3

    from .sync_determine_operation import get_extension
    if dry_run: return _display_sync_log(basename, language, verbose)

    try:
        pf = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
    except FileNotFoundError as e:
        if "test_config.py" in str(e) or "tests/test_" in str(e):
            fp = Path(prompts_dir) / f"{basename}_{language}.prompt"
            if not fp.exists() and Path(prompts_dir).is_dir():
                tl = fp.name.lower()
                for c in Path(prompts_dir).iterdir():
                    if c.name.lower() == tl and c.is_file():
                        fp = c; break
            pf = {'prompt': fp, 'code': Path(f"src/{basename}.{get_extension(language)}"), 'example': Path(f"context/{basename}_example.{get_extension(language)}"), 'test': Path(f"tests/test_{basename}.{get_extension(language)}")}
            if not quiet: print("Note: Test file missing, continuing to generate it")
        else:
            return {"success": False, "error": f"Path construct fail: {e}", "operations_completed": [], "errors": [f"Path construct fail: {e}"]}
    except Exception as e:
        return {"success": False, "error": f"Path construct fail: {e}", "operations_completed": [], "errors": [f"Path construct fail: {e}"]}

    cfnr = ["initializing"]
    stop_event = threading.Event()
    ccr = [0.0]
    ppr = [str(pf.get('prompt', 'N/A'))]
    cpr = [str(pf.get('code', 'N/A'))]
    epr = [str(pf.get('example', 'N/A'))]
    tpr = [str(pf.get('test', 'N/A'))]
    pbcr = ["blue"]; cbcr = ["blue"]; ebcr = ["blue"]; tbcr = ["blue"]
    app_ref = [None]
    pcr = [None]
    uco = [False]

    def get_confirm_callback():
        if uco[0]: return lambda m, t: True
        if app_ref[0] is not None:
            def cb(m, t):
                r = app_ref[0].request_confirmation(m, t)
                if r: uco[0] = True
                return r
            return cb
        if confirm_callback is None:
            def hc(m, t):
                try: r = click.confirm(click.style(m or "Overwrite?", fg="yellow"), default=True, show_default=True)
                except: return False
                if r: uco[0] = True
                return r
            return hc
        return confirm_callback

    def sync_worker_logic():
        ops = []
        sops = []
        errs = []
        st = time.time()
        lmn = ""
        oph = []
        try: log_event(basename, language, "sync_start", {"pid": os.getpid()}, "sync")
        except: pass

        try:
            with SyncLock(basename, language):
                log_event(basename, language, "lock_acquired", {"pid": os.getpid()}, "sync")
                while True:
                    br = budget - ccr[0]
                    if ccr[0] >= budget:
                        errs.append(f"Budget of ${budget:.2f} exceeded.")
                        log_event(basename, language, "budget_exceeded", {"total_cost": ccr[0], "budget": budget}, "sync")
                        break
                    if 0 < br < budget * 0.2:
                        log_event(basename, language, "budget_warning", {"remaining": br}, "sync")

                    dec = sync_determine_operation(basename, language, target_coverage, br, False, prompts_dir, skip_tests, skip_verify, context_override)
                    op = dec.operation

                    if no_steer:
                        sop, sa = op, False
                    else:
                        sop, sa = maybe_steer_operation(op, dec.reason, app_ref[0], quiet, skip_tests, skip_verify, steer_timeout)
                    if sa:
                        errs.append("User aborted sync via steering.")
                        log_event(basename, language, "steering_abort", {"recommended": op}, "sync")
                        break
                    if sop != op:
                        log_event(basename, language, "steering_override", {"recommended": op, "chosen": sop}, "sync")
                        op = dec.operation = sop

                    le = create_log_entry(operation=op, reason=dec.reason, invocation_mode="sync", estimated_cost=dec.estimated_cost, confidence=dec.confidence, decision_type=dec.details.get("decision_type", "heuristic") if dec.details else "heuristic")
                    if dec.details: le.setdefault('details', {}).update(dec.details)
                    le.setdefault('details', {})['budget_remaining'] = br
                    oph.append(op)

                    if len(oph) >= 3 and len([o for o in oph[-3:] if o == 'auto-deps']) >= 2:
                        errs.append("Cycle detected: auto-deps. Advancing to generate.")
                        op = dec.operation = 'generate'
                    if len(oph) >= 4 and (oph[-4:] == ['crash','verify','crash','verify'] or oph[-4:] == ['verify','crash','verify','crash']):
                        errs.append("Cycle detected: crash-verify.")
                        break
                    if len(oph) >= 4 and (oph[-4:] == ['test','fix','test','fix'] or oph[-4:] == ['fix','test','fix','test']):
                        errs.append("Cycle detected: test-fix.")
                        break
                    if op == 'fix' and [o for o in oph[::-1] if o == 'fix'] == ['fix']*min(len(oph),5):
                        errs.append("Detected 5 consecutive fix ops.")
                        break
                    if op == 'test' and [o for o in oph[::-1] if o == 'test'] == ['test']*min(len(oph),MAX_CONSECUTIVE_TESTS):
                        errs.append(f"Detected {MAX_CONSECUTIVE_TESTS} consecutive test ops.")
                        break
                    if op == 'crash' and [o for o in oph[::-1] if o == 'crash'] == ['crash']*min(len(oph),MAX_CONSECUTIVE_CRASHES):
                        errs.append(f"Detected {MAX_CONSECUTIVE_CRASHES} consecutive crash ops.")
                        break
                    if op == 'test_extend':
                        if _use_agentic_path(language, agentic_mode):
                            suc = True; break
                        if len([o for o in oph if o == 'test_extend']) >= MAX_TEST_EXTEND_ATTEMPTS:
                            suc = True; break

                    if op in ['all_synced', 'nothing', 'fail_and_request_manual_merge', 'error']:
                        cfnr[0] = "synced" if op in ['all_synced', 'nothing'] else "conflict"
                        suc = op in ['all_synced', 'nothing']
                        if op == 'fail_and_request_manual_merge': errs.append(f"Manual merge required: {dec.reason}")
                        elif op == 'error': errs.append(f"Error: {dec.reason}")
                        update_log_entry(le, suc, 0.0, 'none', 0.0, dec.reason if not suc else None)
                        append_log_entry(basename, language, le)
                        break

                    if op == 'verify' and (skip_verify or skip_tests):
                        sops.append('verify')
                        update_log_entry(le, True, 0.0, 'skipped', 0.0, None)
                        append_log_entry(basename, language, le)
                        _save_fingerprint_atomic(basename, language, 'skip:verify', pf, 0.0, 'skipped')
                        continue
                    if op == 'test' and skip_tests:
                        sops.append('test')
                        update_log_entry(le, True, 0.0, 'skipped', 0.0, None)
                        append_log_entry(basename, language, le)
                        _save_fingerprint_atomic(basename, language, 'skip:test', pf, 0.0, 'skipped')
                        continue
                    if op == 'crash' and (skip_tests or skip_verify):
                        sops.append('crash')
                        update_log_entry(le, True, 0.0, 'skipped', 0.0, None)
                        append_log_entry(basename, language, le)
                        _save_fingerprint_atomic(basename, language, 'skip:crash', pf, 0.0, 'skipped')
                        ch = calculate_current_hashes(pf)
                        _save_run_report_atomic(asdict(RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 0, 0, 0, 0.0, ch.get('test_hash'))), basename, language)
                        continue

                    cfnr[0] = op
                    ctx = _create_mock_context(force=force, strength=strength, temperature=temperature, time=time_param, verbose=verbose, quiet=quiet, output_cost=output_cost, review_examples=review_examples, local=local, budget=br, max_attempts=max_attempts, target_coverage=target_coverage, confirm_callback=get_confirm_callback(), context=context_override, agentic_mode=agentic_mode)
                    res = {}
                    suc = False
                    ost = time.time()

                    with AtomicStateUpdate(basename, language) as state:
                        try:
                            if op == 'auto-deps':
                                to = str(pf['prompt']).replace('.prompt', '_with_deps.prompt')
                                oc = pf['prompt'].read_text('utf-8')
                                res = auto_deps_main(ctx, str(pf['prompt']), examples_dir, "project_dependencies.csv", to, False, progress_callback=pcr[0])
                                if Path(to).exists():
                                    import shutil
                                    nc = Path(to).read_text('utf-8')
                                    if nc != oc: shutil.move(to, str(pf['prompt']))
                                    else: Path(to).unlink(); res = (nc, 0.0, 'no-changes')
                            elif op == 'generate':
                                pf['code'].parent.mkdir(parents=True, exist_ok=True)
                                res = code_generator_main(ctx, str(pf['prompt'].resolve()), str(pf['code'].resolve()), None, False)
                                clear_run_report(basename, language)
                            elif op == 'example':
                                pf['example'].parent.mkdir(parents=True, exist_ok=True)
                                res = context_generator_main(ctx, str(pf['prompt'].resolve()), str(pf['code'].resolve()), str(pf['example'].resolve()))
                            elif op == 'crash':
                                if [f for f in [pf['code'], pf['example']] if not f.exists()]: sops.append('crash'); continue
                                rr = read_run_report(basename, language)
                                clc = ""
                                hc = False
                                if rr and rr.exit_code != 0:
                                    hc = True; clc = f"Fail exit: {rr.exit_code}\n"
                                elif _use_agentic_path(language, agentic_mode):
                                    hc = True; clc = f"Delegating to agentic.\n"
                                else:
                                    env = os.environ.copy()
                                    env['PYTHONPATH'] = f"{pf['code'].resolve().parent}:{env.get('PYTHONPATH', '')}"
                                    for v in ['FORCE_COLOR', 'COLUMNS']: env.pop(v, None)
                                    rc, out, err = _run_example_with_error_detection([sys.executable, str(pf['example'].resolve())], env, 60)
                                    if rc != 0:
                                        hc = True; clc = f"Fail exit: {rc}\nSTDOUT:\n{out}\nSTDERR:\n{err}\n"
                                        if "SyntaxError" in err: clc = "SYNTAX ERROR:\n" + clc
                                    else:
                                        th = calculate_sha256(pf['test']) if pf['test'].exists() else None
                                        _save_run_report_atomic(asdict(RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 0, 1, 0, 0.0, th)), basename, language)
                                        sops.append('crash'); continue
                                if hc:
                                    af, afm = _try_auto_fix_import_error(clc, pf['code'], pf['example'])
                                    if af:
                                        rc, out, err = _run_example_with_error_detection([sys.executable, str(pf['example'].resolve())], env, 60)
                                        if rc == 0:
                                            th = calculate_sha256(pf['test']) if pf['test'].exists() else None
                                            _save_run_report_atomic(asdict(RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 0, 1, 0, 0.0, th)), basename, language)
                                            res, suc, ac, mn = (True, 0.0, 'auto-fix'), True, 0.0, 'auto-fix'
                                            ops.append('crash')
                                            _save_fingerprint_atomic(basename, language, 'crash', pf, 0.0, 'auto-fix', state)
                                            continue
                                        clc = f"Auto-fix failed:\nSTDOUT:\n{out}\nSTDERR:\n{err}\n"
                                    Path("crash.log").write_text(clc)
                                    ema = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                    try: res = crash_main(ctx, str(pf['prompt']), str(pf['code']), str(pf['example']), "crash.log", str(pf['code']), str(pf['example']), True, ema, br, strength, temperature)
                                    except Exception as e: sops.append('crash'); continue
                            elif op == 'verify':
                                if not pf['example'].exists(): sops.append('verify'); continue
                                ema = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                res = fix_verification_main(ctx, str(pf['prompt']), str(pf['code']), str(pf['example']), f"{basename.replace('/', '_')}_verify_results.log", str(pf['code']), str(pf['example']), True, str(pf['example']), ema, br, False, strength, temperature)
                            elif op == 'test':
                                pf['test'].parent.mkdir(parents=True, exist_ok=True)
                                tfe = pf['test'].exists()
                                res = cmd_test_main(ctx, str(pf['prompt']), str(pf['code']), str(pf['test']), language, None, [str(pf['test'])] if tfe else None, target_coverage, tfe, strength, temperature)
                                ags = res[3] if isinstance(res, tuple) and len(res) >= 4 else None
                                if ags is True: _create_synthetic_run_report_for_agentic_success(pf['test'], basename, language, atomic_state=state)
                                elif pf['test'].exists(): _execute_tests_and_create_run_report(pf['test'], basename, language, target_coverage, code_file=pf.get('code'), atomic_state=state, test_files=pf.get('test_files'))
                            elif op == 'test_extend':
                                pf['test'].parent.mkdir(parents=True, exist_ok=True)
                                if pf['test'].exists():
                                    res = cmd_test_main(ctx, str(pf['prompt']), str(pf['code']), str(pf['test']), language, None, [str(pf['test'])], target_coverage, True, strength, temperature)
                                    ags = res[3] if isinstance(res, tuple) and len(res) >= 4 else None
                                    if language.lower() not in ('python', 'typescript') and ags is True:
                                        _create_synthetic_run_report_for_agentic_success(pf['test'], basename, language, atomic_state=state)
                                    else:
                                        _execute_tests_and_create_run_report(pf['test'], basename, language, target_coverage, code_file=pf.get('code'), atomic_state=state, test_files=pf.get('test_files'))
                                else:
                                    res = cmd_test_main(ctx, str(pf['prompt']), str(pf['code']), str(pf['test']), language, None, None, target_coverage, False, strength, temperature)
                                    ags = res[3] if isinstance(res, tuple) and len(res) >= 4 else None
                                    if language.lower() not in ('python', 'typescript') and ags is True:
                                        if pf['test'].exists(): _create_synthetic_run_report_for_agentic_success(pf['test'], basename, language, atomic_state=state)
                                    elif pf['test'].exists():
                                        _execute_tests_and_create_run_report(pf['test'], basename, language, target_coverage, code_file=pf.get('code'), atomic_state=state, test_files=pf.get('test_files'))
                            elif op == 'fix':
                                efp = Path("fix_errors.log")
                                try:
                                    tc = get_test_command_for_file(str(pf['test']), language)
                                    cenv = os.environ.copy()
                                    for v in ['FORCE_COLOR', 'COLUMNS']: cenv.pop(v, None)
                                    if tc:
                                        if language.lower() == 'python' and not agentic_mode:
                                            pe = detect_host_python_executable()
                                            tfs = pf.get('test_files', [pf['test']])
                                            pa = [pe, '-m', 'pytest'] + [str(f) for f in tfs] + ['-v', '--tb=short']
                                            pr = _find_project_root(pf['test'])
                                            sk = {'capture_output': True, 'text': True, 'timeout': 300, 'stdin': subprocess.DEVNULL, 'env': cenv, 'start_new_session': True}
                                            if pr:
                                                pta = [str(pr)]
                                                sd = pr / "src"
                                                if sd.is_dir(): pta.insert(0, str(sd))
                                                ep = cenv.get("PYTHONPATH", "")
                                                if ep: pta.append(ep)
                                                cenv["PYTHONPATH"] = os.pathsep.join(pta)
                                                pa.extend([f'--rootdir={pr}', '-c', '/dev/null'])
                                                sk['cwd'] = str(pr)
                                            tr = subprocess.run(pa, **sk)
                                        else:
                                            tr = subprocess.run(tc, shell=True, capture_output=True, text=True, timeout=300, stdin=subprocess.DEVNULL, env=cenv, cwd=str(pf['test'].parent), start_new_session=True)
                                        ecnt = f"Test output:\n{tr.stdout}\n{tr.stderr}"
                                    else:
                                        ecnt = f"No test cmd for {language}"
                                except Exception as e: ecnt = f"Error: {e}"
                                efp.write_text(ecnt)
                                ff = extract_failing_files_from_output(ecnt)
                                utf = str(pf['test'])
                                if ff:
                                    td = pf['test'].parent
                                    tfn = pf['test'].name
                                    if not any(Path(f).name == tfn for f in ff):
                                        for f in ff:
                                            fp = Path(f)
                                            if fp.is_absolute() and fp.exists(): utf = str(fp); break
                                            c = td / fp.name
                                            if c.exists(): utf = str(c); break
                                            if fp.exists(): utf = str(fp.resolve()); break
                                ema = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                tfsf = [str(f) for f in pf.get('test_files', [pf['test']])]
                                res = fix_main(ctx, str(pf['prompt']), str(pf['code']), utf, str(efp), utf, str(pf['code']), f"{basename.replace('/', '_')}_fix_results.log", True, str(pf['example']), ema, br, not local, False, strength, temperature, tfsf)
                            elif op == 'update':
                                res = update_main(ctx, str(pf['prompt']), str(pf['code']), None, str(pf['prompt']), True, False, strength, temperature)
                            else: errs.append(f"Unknown op {op}"); res = {'success': False}

                            if isinstance(res, dict): suc = res.get('success', False); ccr[0] += res.get('cost', 0.0)
                            elif isinstance(res, tuple) and len(res) >= 3:
                                if op == 'test':
                                    ags = res[3] if len(res) >= 4 else None
                                    suc = ags if ags is not None else pf['test'].exists()
                                else: suc = bool(res[0])
                                ccr[0] += res[-2] if len(res) >= 2 and isinstance(res[-2], (int, float)) else 0.0
                            else: suc = res is not None

                        except click.Abort: errs.append(f"Op '{op}' cancelled"); suc = False
                        except Exception as e: errs.append(f"Exception during '{op}': {e or type(e).__name__}"); suc = False
                    
                        du = time.time() - ost
                        ac = 0.0
                        mn = "unknown"
                        if suc:
                            if isinstance(res, dict): ac = res.get('cost', 0.0); mn = res.get('model', 'unknown')
                            elif isinstance(res, tuple) and len(res) >= 3:
                                if op == 'test' and len(res) >= 4: ac = res[1] if isinstance(res[1], (int,float)) else 0.0; mn = res[2] if isinstance(res[2], str) else 'unknown'
                                else: ac = res[-2] if isinstance(res[-2], (int,float)) else 0.0; mn = res[-1] if len(res) >= 1 else 'unknown'
                            lmn = str(mn)
                            ops.append(op)
                            _save_fingerprint_atomic(basename, language, op, pf, ac, lmn, state)

                        update_log_entry(le, suc, ac, mn, du, errs[-1] if errs and not suc else None)
                        append_log_entry(basename, language, le)

                        if suc and op == 'crash':
                            if _use_agentic_path(language, agentic_mode):
                                th = calculate_sha256(pf['test']) if pf['test'].exists() else None
                                _save_run_report_atomic(asdict(RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 0, 1, 0, 0.0, th)), basename, language)
                            else:
                                try:
                                    cenv = os.environ.copy()
                                    for v in ['FORCE_COLOR', 'COLUMNS']: cenv.pop(v, None)
                                    rc, out, err = _run_example_with_error_detection([sys.executable, str(pf['example'].resolve())], cenv, 60)
                                    th = calculate_sha256(pf['test']) if pf['test'].exists() else None
                                    _save_run_report_atomic(asdict(RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), rc, 1 if rc==0 else 0, 0 if rc==0 else 1, 100.0 if rc==0 else 0.0, th)), basename, language)
                                except Exception as e: errs.append(f"Post-crash fail: {e}")
                        if suc and op == 'fix':
                            if _use_agentic_path(language, agentic_mode):
                                th = calculate_sha256(pf['test']) if pf['test'].exists() else None
                                _save_run_report_atomic(asdict(RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), 0, 1, 0, 0.0, th)), basename, language)
                            elif pf['test'].exists():
                                _execute_tests_and_create_run_report(pf['test'], basename, language, target_coverage, code_file=pf.get('code'), atomic_state=state, test_files=pf.get('test_files'))
                        if not suc:
                            if not errs: errs.append(f"Op '{op}' failed.")
                            break
        except Exception as e:
            errs.append(f"Unexpected: {type(e).__name__}: {e}")
        finally:
            try: log_event(basename, language, "lock_released", {"pid": os.getpid(), "total_cost": ccr[0]}, "sync")
            except: pass
            
        return {
            'success': not errs,
            'operations_completed': ops,
            'skipped_operations': sops,
            'total_cost': ccr[0],
            'total_time': time.time() - st,
            'final_state': {p: {'exists': f.exists(), 'path': str(f)} for p, f in pf.items() if p != 'test_files'},
            'errors': errs,
            'error': "; ".join(errs) if errs else None,
            'model_name': lmn,
        }

    hl = quiet or not sys.stdout.isatty() or os.environ.get('CI')
    if hl:
        os.environ['PDD_FORCE'] = '1'
        if not quiet: print("Running headless...")
        res = sync_worker_logic()
        we = None
    else:
        app = SyncApp(basename, budget, sync_worker_logic, cfnr, ccr, ppr, cpr, epr, tpr, pbcr, cbcr, ebcr, tbcr, stop_event, progress_callback_ref=pcr)
        app_ref[0] = app
        res = app.run()
        from .sync_tui import show_exit_animation
        show_exit_animation()
        we = app.worker_exception
    
    if not hl and we:
        print(f"\n[Error] Worker thread crashed: {we}", file=sys.stderr)
        if hasattr(we, '__traceback__'): traceback.print_exception(type(we), we, we.__traceback__, file=sys.stderr)
    
    if res is None: return {"success": False, "total_cost": ccr[0], "model_name": "", "error": "Interrupted", "operations_completed": [], "errors": ["Interrupted"]}
    return res

if __name__ == '__main__':
    Path("./prompts").mkdir(exist_ok=True)
    Path("./src").mkdir(exist_ok=True)
    Path("./examples").mkdir(exist_ok=True)
    Path("./tests").mkdir(exist_ok=True)
    Path("./prompts/my_calculator_python.prompt").write_text("Create a calculator.")
    PDD_DIR.mkdir(exist_ok=True)
    META_DIR.mkdir(exist_ok=True)
    result = sync_orchestration(basename="my_calculator", language="python", quiet=True)
    print(json.dumps(result, indent=2))