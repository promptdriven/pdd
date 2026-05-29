from __future__ import annotations

import os
import re
import shlex
import shutil
import subprocess
import sys
import time as time_module
from pathlib import Path
from typing import Any, Optional, Tuple

import requests
from rich import print as rprint
from rich.console import Console

from . import DEFAULT_TIME
from .agentic_fix import run_agentic_fix
from .core.cloud import CloudConfig, get_cloud_request_timeout
from .failure_classification import (
    FailureKind,
    classify_failure,
    extract_failure_signature,
    failure_classification_hint,
    format_signature_hint,
)
from .fix_errors_from_unit_tests import fix_errors_from_unit_tests
from .fix_focus import FocusedInputs, is_large, prepare_focused_inputs, reconstruct_code
from .get_language import get_language
from .get_test_command import TestCommand, get_test_command_for_file
from .pytest_output import run_pytest_and_capture_output
from .python_env_detector import detect_host_python_executable

console = Console()


def escape_brackets(text: str) -> str:
    """Escape Rich markup brackets in console text."""
    return text.replace("[", "\\[").replace("]", "\\]")


def _normalize_agentic_result(result: tuple[Any, ...]) -> tuple[bool, str, float, str, list[str]]:
    """
    Normalizes the return shape from the agentic fix to ensure a consistent internal state.
    Returns: (success, message, cost, model, changed_files)
    """
    if len(result) == 2:
        return bool(result[0]), str(result[1]), 0.0, "agentic-cli", []
    if len(result) == 3:
        return bool(result[0]), str(result[1]), float(result[2] or 0.0), "agentic-cli", []
    if len(result) == 4:
        return bool(result[0]), str(result[1]), float(result[2] or 0.0), str(result[3] or "agentic-cli"), []
    if len(result) >= 5:
        changed_files = result[4] if isinstance(result[4], list) else []
        return bool(result[0]), str(result[1]), float(result[2] or 0.0), str(result[3] or "agentic-cli"), changed_files
    return False, "Invalid agentic result", 0.0, "agentic-cli", []


def _safe_run_agentic_fix(
    prompt_file: str,
    code_file: str,
    unit_test_file: str,
    error_log_file: str,
    *,
    verbose: bool = False,
    protect_tests: bool = False,
) -> tuple[bool, str, float, str, list[str]]:
    """Run agentic fallback and normalize the agent return contract."""
    return _normalize_agentic_result(
        run_agentic_fix(
            prompt_file=prompt_file,
            code_file=code_file,
            unit_test_file=unit_test_file,
            error_log_file=error_log_file,
            cwd=None,
            verbose=verbose,
            protect_tests=protect_tests,
        )
    )


def _strip_ansi(text: str) -> str:
    return re.sub(r"\x1b\[[0-9;?]*[ -/]*[@-~]", "", text)


def _counts_from_output(output: str, returncode: int = 0) -> tuple[int, int, int]:
    clean = _strip_ansi(output)
    failures = len(re.findall(r"(?m)^\s*(?:FAILED|FAILURES?)\b", clean))
    errors = len(re.findall(r"(?m)^\s*(?:ERROR|ERRORS?)\b", clean))
    warnings = len(re.findall(r"(?i)\bwarning[s]?\b", clean))
    summary = re.search(r"(?i)(\d+)\s+failed", clean)
    if summary:
        failures = max(failures, int(summary.group(1)))
    summary = re.search(r"(?i)(\d+)\s+error", clean)
    if summary:
        errors = max(errors, int(summary.group(1)))
    summary = re.search(r"(?i)(\d+)\s+warning", clean)
    if summary:
        warnings = max(warnings, int(summary.group(1)))
    if returncode != 0 and failures == 0 and errors == 0:
        if re.search(r"(?i)(syntaxerror|importerror|modulenotfounderror|error collecting)", clean):
            errors = 1
        else:
            failures = 1
    return failures, errors, warnings


def run_pytest_on_file(
    test_file: str,
    verification_program: str | None = None,
    test_files: list[str] | None = None,
) -> Tuple[int, int, int, str]:
    """
    Runs pytest (or the relevant verification program) on the given test file
    and extracts failures, errors, warnings, and the output text.

    Returns: (failures, errors, warnings, output_log)
    """
    del verification_program
    # Filter the primary test file out of extra_files: run_pytest_and_capture_output
    # already prepends the primary path, so passing it again causes double-execution.
    extra = (
        [f for f in test_files if Path(f).resolve() != Path(test_file).resolve()]
        if test_files
        else None
    )
    try:
        result = run_pytest_and_capture_output(test_file, extra_files=extra or None)
    except TypeError:
        result = run_pytest_and_capture_output(test_file)
    test_results = result.get("test_results") or []
    if test_results:
        failures = sum(int(item.get("failures", 0) or 0) for item in test_results)
        errors = sum(int(item.get("errors", 0) or 0) for item in test_results)
        warnings = sum(int(item.get("warnings", 0) or 0) for item in test_results)
        logs = "\n".join(
            str(item.get("standard_output", "") or "") + "\n" + str(item.get("standard_error", "") or "")
            for item in test_results
        )
        return failures, errors, warnings, logs
    logs = str(result.get("standard_output", "") or "") + "\n" + str(result.get("standard_error", "") or "")
    return (*_counts_from_output(logs, int(result.get("returncode", 0) or 0)), logs)


def format_log_for_output(*args: Any) -> str:
    """Formats iteration logs into structured XML."""
    if len(args) == 1 and isinstance(args[0], dict):
        parts: list[str] = []
        for entry in args[0].get("iterations", []):
            number = entry.get("number", "")
            pytest_output = entry.get("initial_test_output") or entry.get("post_test_output", "")
            fix_attempt = entry.get("fix_attempt", "")
            if entry.get("model_name"):
                fix_attempt = f"Model: {entry['model_name']}\n{fix_attempt}"
            parts.append(f"<pytest_output iteration={number}>\n{pytest_output}\n</pytest_output>")
            parts.append(f"<fix_attempt iteration={number}>\n{fix_attempt}\n</fix_attempt>")
            parts.append(f"<verification_output iteration={number}>\n{entry.get('verification', '')}\n</verification_output>")
            if entry.get("post_test_output") is not None:
                parts.append(f"=== Final Pytest Run ===\n{entry.get('post_test_output', '')}")
        return "\n".join(parts) + ("\n" if parts else "")
    if len(args) not in {4, 5}:
        raise TypeError("format_log_for_output expects a log dict or iteration/test/fix/verification values")
    iteration, test_output, fix_output, verification_output = args[:4]
    model_name = args[4] if len(args) == 5 else None
    model_line = f"Model: {model_name}\n" if model_name else ""
    return (
        f"<iteration number=\"{iteration}\">\n"
        f"<pytest_output iteration={iteration}>\n{test_output}\n</pytest_output>\n"
        f"<fix_attempt iteration={iteration}>\n{model_line}{fix_output}\n</fix_attempt>\n"
        f"<verification_output iteration={iteration}>\n{verification_output}\n</verification_output>\n"
        f"</iteration>\n"
    )


def _create_backups(code_file: str, unit_test_file: str, attempt: int) -> tuple[Path, Path]:
    code_path = Path(code_file)
    test_path = Path(unit_test_file)
    backup_root = Path(".pdd") / "backups" / code_path.stem / f"{int(time_module.time() * 1000)}_{attempt}"
    backup_root.mkdir(parents=True, exist_ok=True)
    code_backup = backup_root / f"code_{attempt}_{code_path.name}"
    test_backup = backup_root / f"test_{attempt}_{test_path.name}"
    shutil.copy(code_file, code_backup)
    shutil.copy(unit_test_file, test_backup)
    return code_backup, test_backup


def _run_verification_program(verification_program: str, code_file: str) -> tuple[bool, str]:
    if not verification_program:
        return True, ""
    executable = detect_host_python_executable()
    cmd = [executable, verification_program]
    if Path(verification_program).resolve() == Path(code_file).resolve():
        cmd = [executable, "-m", "py_compile", code_file]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, check=False, timeout=120)
        return proc.returncode == 0, (proc.stdout or "") + "\n" + (proc.stderr or "")
    except Exception as exc:
        return False, f"Verification exception: {exc}"


def _run_non_python_initial_verification(unit_test_file: str, code_file: str) -> tuple[bool, str]:
    language = get_language(os.path.splitext(code_file)[1]) or "unknown"
    test_command = get_test_command_for_file(unit_test_file, language)
    if not test_command:
        return False, f"No test command found for {language}"
    if isinstance(test_command, TestCommand):
        command = test_command.command
        cwd = test_command.cwd
    else:
        command = str(test_command)
        cwd = None
    command = command.replace("{file}", shlex.quote(unit_test_file)).replace("{test}", shlex.quote(unit_test_file))
    try:
        proc = subprocess.run(
            command,
            shell=True,
            cwd=str(cwd) if cwd is not None else None,
            capture_output=True,
            text=True,
            check=False,
            timeout=120,
        )
        return proc.returncode == 0, (proc.stdout or "") + "\n" + (proc.stderr or "")
    except Exception as exc:
        return False, f"Non-Python verification exception: {exc}"


def _cloud_value(data: dict[str, Any], snake: str, camel: str, default: Any) -> Any:
    return data.get(snake, data.get(camel, default))


def cloud_fix_errors(
    unit_test: str,
    code: str,
    prompt: str,
    error: str,
    error_file: str,
    strength: float,
    temperature: float,
    verbose: bool = False,
    time: float = DEFAULT_TIME,
    code_file_ext: str = ".py",
    protect_tests: bool = False,
    failure_classification: str | None = None,
) -> Tuple[bool, bool, str, str, str, float, str]:
    """
    Call the cloud fixCode endpoint to fix errors in code and unit tests.
    """
    del error_file
    global requests
    if requests is None:
        try:
            import requests as requests_module
        except ImportError as exc:
            raise RuntimeError("The 'requests' library is required for cloud execution.") from exc
        requests = requests_module
    token = CloudConfig.get_jwt_token(verbose=verbose)
    if not token:
        raise RuntimeError("Cloud authentication failed: no JWT token available")
    if failure_classification:
        error = f"[PDD failure classification] {failure_classification}\n{error}"
    payload = {
        "unitTest": unit_test,
        "code": code,
        "prompt": prompt,
        "errors": error,
        "language": get_language(code_file_ext) or "python",
        "strength": strength,
        "temperature": temperature,
        "time": time,
        "verbose": verbose,
        "protectTests": protect_tests,
        "codeFileExt": code_file_ext,
    }
    try:
        response = requests.post(
            CloudConfig.get_endpoint_url("fixCode"),
            json=payload,
            headers={"Authorization": f"Bearer {token}", "Content-Type": "application/json"},
            timeout=get_cloud_request_timeout(),
        )
        response.raise_for_status()
    except Exception as exc:
        response = getattr(exc, "response", None)
        if getattr(response, "status_code", None) == 402:
            try:
                details = response.json()
            except Exception:
                details = {}
            raise RuntimeError(
                "Insufficient credits for cloud execution "
                f"(balance={details.get('currentBalance', 'unknown')}, "
                f"estimated={details.get('estimatedCost', 'unknown')})"
            ) from exc
        raise RuntimeError(f"Cloud execution failed: {exc}") from exc
    data = response.json()
    return (
        bool(_cloud_value(data, "update_unit_test", "updateUnitTest", False)),
        bool(_cloud_value(data, "update_code", "updateCode", False)),
        str(_cloud_value(data, "fixed_unit_test", "fixedUnitTest", unit_test)),
        str(_cloud_value(data, "fixed_code", "fixedCode", code)),
        str(data.get("analysis", "")),
        float(_cloud_value(data, "total_cost", "totalCost", 0.0) or 0.0),
        str(_cloud_value(data, "model_name", "modelName", "cloud-model")),
    )


def _best_is_better(candidate: dict[str, Any], current: dict[str, Any]) -> bool:
    return (int(candidate["errs"]), int(candidate["fails"]), int(candidate["warns"])) < (
        int(current["errs"]),
        int(current["fails"]),
        int(current["warns"]),
    )


def fix_error_loop(
    unit_test_file: str,
    code_file: str,
    prompt_file: str,
    prompt: str,
    verification_program: str,
    strength: float,
    temperature: float,
    max_attempts: int,
    budget: float,
    error_log_file: str = "error_log.txt",
    verbose: bool = False,
    time: float = DEFAULT_TIME,
    agentic_fallback: bool = True,
    protect_tests: bool = False,
    use_cloud: bool = False,
    test_files: list[str] | None = None,
    failure_aware_retries: bool = True,
    no_local_fallback: bool = False,
) -> tuple[bool, str, str, int, float, str]:
    """
    Returns: (success, final_unit_test, final_code, total_attempts, total_cost, model_name)
    """
    total_cost = 0.0
    total_attempts = 0
    model_name = ""
    unit_test_content = ""
    code_content = ""
    last_attempt = 0

    def call_agentic() -> tuple[bool, str, str, int, float, str]:
        nonlocal total_cost, model_name, unit_test_content, code_content, total_attempts
        if not agentic_fallback:
            return False, unit_test_content, code_content, total_attempts, total_cost, model_name
        success, _message, cost, agent_model, _changed = _safe_run_agentic_fix(
            prompt_file,
            code_file,
            unit_test_file,
            error_log_file,
            verbose=verbose,
            protect_tests=protect_tests,
        )
        total_cost += cost
        total_attempts = max(total_attempts, 1)
        model_name = agent_model or model_name
        for path, target in ((unit_test_file, "test"), (code_file, "code")):
            try:
                content = Path(path).read_text(encoding="utf-8")
            except Exception:
                continue
            if target == "test":
                unit_test_content = content
            else:
                code_content = content
        return success, unit_test_content, code_content, total_attempts, total_cost, model_name

    if not os.path.isfile(unit_test_file) or not os.path.isfile(code_file):
        missing = unit_test_file if not os.path.isfile(unit_test_file) else code_file
        console.print(f"[red]Missing required file: {escape_brackets(missing)}[/red]")
        return False, "", "", 0, 0.0, ""

    try:
        unit_test_content = Path(unit_test_file).read_text(encoding="utf-8")
        code_content = Path(code_file).read_text(encoding="utf-8")
    except Exception as exc:
        console.print(f"[red]Error reading files: {escape_brackets(str(exc))}[/red]")
        Path(error_log_file).write_text(f"Initial file read error: {exc}\n", encoding="utf-8")
        return call_agentic()

    ext = os.path.splitext(code_file)[1]
    if ext != ".py":
        passed, output = _run_non_python_initial_verification(unit_test_file, code_file)
        Path(error_log_file).write_text(format_log_for_output(0, output, "non-python initial verification", output, "N/A"), encoding="utf-8")
        if passed:
            return True, unit_test_content, code_content, 0, 0.0, "N/A"
        return call_agentic()

    try:
        fails, errs, warns, output_log = run_pytest_on_file(unit_test_file, verification_program, test_files)
    except Exception as exc:
        Path(error_log_file).write_text(f"Initial pytest exception: {exc}\n", encoding="utf-8")
        return call_agentic()
    if fails == 0 and errs == 0:
        return True, unit_test_content, code_content, 0, 0.0, ""
    Path(error_log_file).write_text(format_log_for_output(0, output_log, "initial pytest run", output_log), encoding="utf-8")
    best_state: dict[str, Any] = {"fails": fails, "errs": errs, "warns": warns, "code": code_content, "test": unit_test_content, "iteration": 0}
    current_state = dict(best_state)
    consecutive_timeouts_without_improvement = 0
    if failure_aware_retries and classify_failure(output_log) == FailureKind.SYNTAX_IMPORT:
        last_syntax_signature = extract_failure_signature(output_log)
    else:
        last_syntax_signature = ""
    _cloud_no_fallback_break = False

    for attempt in range(1, max_attempts + 1):
        last_attempt = attempt
        if total_cost >= budget:
            console.print("[yellow]Budget exceeded. Stopping iterative loop.[/yellow]")
            break
        total_attempts += 1
        try:
            code_backup, test_backup = _create_backups(code_file, unit_test_file, attempt)
            code_content = Path(code_file).read_text(encoding="utf-8")
            unit_test_content = Path(unit_test_file).read_text(encoding="utf-8")
        except Exception as exc:
            with open(error_log_file, "a", encoding="utf-8") as log_file:
                log_file.write(format_log_for_output(attempt, output_log, f"Preparation failed: {exc}", ""))
            break
        focused_inputs: Optional[FocusedInputs] = None
        if is_large(code_content, unit_test_content):
            try:
                focused_inputs = prepare_focused_inputs(code_content, unit_test_content, output_log, strength, temperature, time, verbose, "python")
            except Exception:
                focused_inputs = None
        target_code = focused_inputs.focused_code if focused_inputs else code_content
        target_test = focused_inputs.focused_tests if focused_inputs else unit_test_content
        classification = failure_classification_hint(classify_failure(output_log)) if failure_aware_retries else None
        effective_protect_tests = protect_tests or bool(focused_inputs)
        try:
            if use_cloud:
                update_test, update_code, fixed_test, fixed_code, analysis, cost, model_name = cloud_fix_errors(
                    target_test, target_code, prompt, output_log, error_log_file, strength, temperature, verbose, time, ext, effective_protect_tests, classification
                )
            else:
                update_test, update_code, fixed_test, fixed_code, analysis, cost, model_name = fix_errors_from_unit_tests(
                    target_test, target_code, prompt, output_log, error_log_file,
                    strength=strength,
                    temperature=temperature,
                    time=time,
                    verbose=verbose,
                    protect_tests=effective_protect_tests,
                    failure_classification=classification,
                )
        except Exception as exc:
            if use_cloud:
                if no_local_fallback:
                    with open(error_log_file, "a", encoding="utf-8") as log_file:
                        log_file.write(format_log_for_output(attempt, output_log, f"Cloud fix failed (no local fallback): {exc}", ""))
                    _cloud_no_fallback_break = True
                    break
                try:
                    update_test, update_code, fixed_test, fixed_code, analysis, cost, model_name = fix_errors_from_unit_tests(
                        unit_test=target_test,
                        code=target_code,
                        prompt=prompt,
                        error=output_log,
                        error_file=error_log_file,
                        strength=strength,
                        temperature=temperature,
                        time=time,
                        verbose=verbose,
                        protect_tests=effective_protect_tests,
                        failure_classification=classification,
                    )
                except Exception as local_exc:
                    with open(error_log_file, "a", encoding="utf-8") as log_file:
                        log_file.write(format_log_for_output(attempt, output_log, f"Fix call failed: {exc}; local fallback failed: {local_exc}", ""))
                    break
            else:
                with open(error_log_file, "a", encoding="utf-8") as log_file:
                    log_file.write(format_log_for_output(attempt, output_log, f"Fix call failed: {exc}", ""))
                break
        total_cost += cost
        if focused_inputs and update_code:
            fixed_code = reconstruct_code(code_content, fixed_code, focused_inputs.slices)
        if focused_inputs:
            # focused_tests is only a failing-test subset; never write the partial result back
            fixed_test = unit_test_content
        next_code = fixed_code if update_code else code_content
        next_test = fixed_test if update_test and not protect_tests else unit_test_content
        Path(code_file).write_text(next_code, encoding="utf-8")
        if not protect_tests:
            Path(unit_test_file).write_text(next_test, encoding="utf-8")
        verification_ok, verification_output = _run_verification_program(verification_program, code_file)
        if not verification_ok:
            shutil.copy(str(test_backup), unit_test_file)
            shutil.copy(str(code_backup), code_file)
            next_code = Path(code_file).read_text(encoding="utf-8")
            next_test = Path(unit_test_file).read_text(encoding="utf-8")
            verification_output += "\nRestored previous code/test backup after verification failure."
        try:
            new_fails, new_errs, new_warns, new_log = run_pytest_on_file(unit_test_file, verification_program, test_files)
        except Exception as exc:
            with open(error_log_file, "a", encoding="utf-8") as log_file:
                log_file.write(format_log_for_output(attempt, output_log, analysis, f"Pytest exception: {exc}", model_name))
            break
        with open(error_log_file, "a", encoding="utf-8") as log_file:
            log_file.write(format_log_for_output(attempt, output_log, analysis, verification_output + "\n" + new_log, model_name))
        if new_fails == 0 and new_errs == 0:
            return True, next_test, next_code, total_attempts, total_cost, model_name
        current_state = {"fails": new_fails, "errs": new_errs, "warns": new_warns, "code": next_code, "test": next_test, "iteration": attempt}
        improved = _best_is_better(current_state, best_state)
        if improved:
            best_state = dict(current_state)
        if failure_aware_retries:
            kind = classify_failure(new_log)
            if kind == FailureKind.TIMEOUT_FLAKY:
                consecutive_timeouts_without_improvement = 0 if improved else consecutive_timeouts_without_improvement + 1
                if consecutive_timeouts_without_improvement >= 2:
                    console.print("[yellow]Timeout/flaky failure did not improve after consecutive attempts. Isolate tests, increase timeout, or investigate manually.[/yellow]")
                    break
            else:
                consecutive_timeouts_without_improvement = 0
            if kind == FailureKind.SYNTAX_IMPORT:
                sig = extract_failure_signature(new_log)
                if attempt >= 1 and sig and sig == last_syntax_signature:
                    console.print(f"[yellow]Unchanged syntax/import failure {escape_brackets(format_signature_hint(sig))}. Imports, environment, or missing files may need manual fixes.[/yellow]")
                    break
                last_syntax_signature = sig
        output_log = new_log
        code_content = next_code
        unit_test_content = next_test

    if best_state["iteration"] != current_state.get("iteration", last_attempt):
        Path(code_file).write_text(str(best_state["code"]), encoding="utf-8")
        if not protect_tests:
            Path(unit_test_file).write_text(str(best_state["test"]), encoding="utf-8")
        code_content = str(best_state["code"])
        unit_test_content = str(best_state["test"])
    if agentic_fallback and total_cost < budget and not _cloud_no_fallback_break:
        return call_agentic()
    return False, str(best_state["test"]), str(best_state["code"]), total_attempts, total_cost, model_name


if __name__ == "__main__":
    console.print("[bold cyan]Running demonstration of pdd module functions[/bold cyan]")
    test_f, code_f, prompt_f = "test_demo.py", "demo.py", "prompt.txt"
    with open(test_f, "w", encoding="utf-8") as f:
        f.write("def test_demo(): assert True\n")
    with open(code_f, "w", encoding="utf-8") as f:
        f.write("def demo(): pass\n")
    with open(prompt_f, "w", encoding="utf-8") as f:
        f.write("Fix everything\n")
    success, _ut_final, _code_final, attempts, cost, _model = fix_error_loop(
        test_f, code_f, prompt_f, "Fix it", sys.executable, 0.7, 0.7, 1, 1.0, verbose=True, agentic_fallback=False
    )
    console.print(f"Success: {success}, Attempts: {attempts}, Cost: {cost}")
    for file in [test_f, code_f, prompt_f, "error_log.txt"]:
        if os.path.exists(file):
            os.remove(file)
