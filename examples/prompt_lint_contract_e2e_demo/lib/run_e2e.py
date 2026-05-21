#!/usr/bin/env python3
"""
End-to-end demo for ``pdd prompt lint`` and ``pdd contracts`` / ``pdd coverage``.

The demo is a **two-fixture comparison** in the same problem domain:

  * ``prompts/foo_vague_python.prompt``      — intentionally vague (negative)
  * ``prompts/foo_formalized_python.prompt`` — source-of-truth grade (positive)

Both prompts plus their two companion stories are the only hand-authored
files. Every JSON in ``reports/`` and every artifact in ``src/`` / ``tests/``
is produced by real ``pdd`` CLI invocations driven from this script.

Modes
-----
default (no API):
  Runs each deterministic command against both fixtures and writes
  per-fixture reports plus ``reports/comparison.json``::

    pdd prompt lint
    pdd contracts check --json --stories user_stories
    pdd contracts compile --json
    pdd coverage --contracts --json --stories-dir user_stories
    pdd prompt lint --contracts --json
    pdd prompt lint --report formalization --json

--live (real API keys):
  Runs ``lib/live_pipeline.sh`` (bash): **before** clarify runs generate → test →
  pytest on the codegen work copy; **clarify** applies ``--ambiguity --apply``;
  **after** runs the same stack again. Snapshots and diffs cover prompts, ``src/``,
  and ``tests/`` before vs after.
"""
from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

_REPO_ROOT = Path(__file__).resolve().parents[3]
_DEMO_DIR = Path(__file__).resolve().parent.parent

os.environ.setdefault("PDD_PATH", str(_REPO_ROOT / "pdd"))
os.environ.setdefault("PDD_SKIP_UPDATE_CHECK", "1")
os.environ.setdefault("PDD_ALLOW_DUPLICATE_RUN", "1")

from click.testing import CliRunner  # noqa: E402

from pdd import cli  # noqa: E402

_VAGUE_NAME = "foo_vague_python.prompt"
_FORMALIZED_NAME = "foo_formalized_python.prompt"
_CODEGEN_NAME = "foo_codegen_python.prompt"
_WORK_NAME = "foo_work_python.prompt"
_SRC_BEFORE = "foo_work_before.py"
_SRC_AFTER = "foo_work_after.py"
_TEST_BEFORE = "test_foo_work_before.py"
_TEST_AFTER = "test_foo_work_after.py"

# Exit code reserved for "LLM unavailable" (over quota, auth-broken, no model
# in the fallback chain answered). The pytest live test maps this to skip().
_EXIT_LLM_UNAVAILABLE = 77


class _LLMUnavailable(RuntimeError):
    """Raised when every model in the fallback chain failed to answer."""


def _paths() -> dict[str, Path]:
    root = _DEMO_DIR
    reports = root / "reports"
    return {
        "vague": root / "prompts" / _VAGUE_NAME,
        "formalized": root / "prompts" / _FORMALIZED_NAME,
        "codegen": root / "prompts" / _CODEGEN_NAME,
        "work": root / "prompts" / _WORK_NAME,
        "src_before": root / "src" / _SRC_BEFORE,
        "src_after": root / "src" / _SRC_AFTER,
        "test_before": root / "tests" / _TEST_BEFORE,
        "test_after": root / "tests" / _TEST_AFTER,
        "reports": reports,
        "artifacts": reports / "artifacts",
        "diffs": reports / "diffs",
        "stories": root / "user_stories",
        "tests_dir": root / "tests",
    }


def _llm_configured() -> bool:
    if os.environ.get("PDD_MODEL_DEFAULT"):
        return True
    return any(
        os.environ.get(name)
        for name in (
            "OPENAI_API_KEY",
            "ANTHROPIC_API_KEY",
            "GEMINI_API_KEY",
            "GOOGLE_API_KEY",
            "AZURE_API_KEY",
            "VERTEXAI_PROJECT",
        )
    )


def _llm_preflight() -> tuple[bool, str]:
    """Do a tiny live LLM round-trip; return (ok, message)."""
    try:
        from pdd.llm_invoke import llm_invoke
    except Exception as exc:  # pragma: no cover - defensive
        return False, f"could not import pdd.llm_invoke: {exc}"
    try:
        response = llm_invoke(
            prompt="Reply with the single word: ok",
            input_json={},
            strength=0.1,
            temperature=0.0,
            verbose=False,
        )
    except Exception as exc:
        return False, f"llm_invoke raised {type(exc).__name__}: {exc}"
    result = str(response.get("result", "")).strip()
    if not result:
        return False, "every model in the fallback chain returned empty output"
    return True, f"preflight ok via {response.get('model_name', '?')}"


def _parse_json_stdout(stdout: str) -> Any:
    text = stdout.strip()
    for idx, ch in enumerate(text):
        if ch in "{[":
            try:
                return json.loads(text[idx:])
            except json.JSONDecodeError:
                continue
    raise ValueError(f"no JSON in stdout (first 300 chars): {stdout[:300]!r}")


def _run_cli(
    runner: CliRunner,
    args: list[str],
    *,
    allow_warn_exit: bool = False,
) -> subprocess.CompletedProcess[str]:
    """Invoke ``pdd ...`` via CliRunner; optionally treat exit 1 as success."""
    result = runner.invoke(cli.cli, args, catch_exceptions=True)
    output = result.output or ""
    code = result.exit_code if result.exit_code is not None else 0
    if allow_warn_exit and code == 1:
        code = 0
    return subprocess.CompletedProcess(args, code, output, "")


def _hdr(title: str) -> None:
    print(f"\n{'=' * 64}\n  {title}\n{'=' * 64}")


def _sub(title: str) -> None:
    print(f"\n--- {title} ---")


def _lint_counts(stdout: str) -> tuple[int, int]:
    warn_match = re.search(r"(\d+)\s+warn", stdout)
    err_match = re.search(r"(\d+)\s+error", stdout)
    return (
        int(warn_match.group(1)) if warn_match else 0,
        int(err_match.group(1)) if err_match else 0,
    )


# ---------------------------------------------------------------------------
# Per-CLI-command helpers (deterministic; safe to run on either fixture)
# ---------------------------------------------------------------------------


def _step_prompt_lint(
    runner: CliRunner,
    prompt: Path,
    *,
    extra: list[str] | None = None,
    label: str,
) -> dict[str, Any]:
    args = ["--quiet", "prompt", "lint", *(extra or []), str(prompt.relative_to(_DEMO_DIR))]
    proc = _run_cli(runner, args, allow_warn_exit=True)
    warn, err = _lint_counts(proc.stdout)
    print(f"  pdd prompt lint {label}: {warn} warn, {err} error (exit {proc.returncode})")
    return {"exit_code": proc.returncode, "warn_count": warn, "error_count": err}


def _step_prompt_lint_json(runner: CliRunner, prompt: Path) -> dict[str, Any]:
    """JSON form of `pdd prompt lint` — used for code/section breakdowns."""
    proc = _run_cli(
        runner,
        ["--quiet", "prompt", "lint", "--json", str(prompt.relative_to(_DEMO_DIR))],
        allow_warn_exit=True,
    )
    if proc.returncode not in (0, 1):
        raise RuntimeError(f"pdd prompt lint --json failed:\n{proc.stdout}")
    payload = _parse_json_stdout(proc.stdout)
    rows = payload if isinstance(payload, list) else [payload]
    codes: dict[str, int] = {}
    sections: dict[str, int] = {}
    total = 0
    for row in rows:
        for issue in row.get("issues", []) or []:
            total += 1
            codes[issue.get("code", "?")] = codes.get(issue.get("code", "?"), 0) + 1
            sections[issue.get("section", "?")] = sections.get(issue.get("section", "?"), 0) + 1
    print(f"  pdd prompt lint --json: {total} issue(s) by code={codes} sections={sections}")
    return {"payload": payload, "issue_count": total, "by_code": codes, "by_section": sections}


def _step_contracts_check(runner: CliRunner, prompt: Path) -> dict[str, Any]:
    proc = _run_cli(
        runner,
        [
            "--quiet",
            "contracts",
            "check",
            "--json",
            "--stories",
            "user_stories",
            str(prompt.relative_to(_DEMO_DIR)),
        ],
        allow_warn_exit=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"pdd contracts check failed:\n{proc.stdout}")
    payload = _parse_json_stdout(proc.stdout)
    rows = payload if isinstance(payload, list) else [payload]
    issue_count = sum(len(r.get("issues", []) or []) for r in rows)
    print(f"  pdd contracts check: {len(rows)} target(s), {issue_count} issue(s)")
    return {"results": payload, "issue_count": issue_count, "target_count": len(rows)}


def _step_contracts_compile(runner: CliRunner, prompt: Path) -> dict[str, Any]:
    """``pdd contracts compile --json`` (exit 2 with valid JSON is normal for vague input)."""
    proc = _run_cli(
        runner,
        ["--quiet", "contracts", "compile", "--json", str(prompt.relative_to(_DEMO_DIR))],
    )
    if proc.returncode not in (0, 2):
        raise RuntimeError(f"pdd contracts compile failed (code {proc.returncode}):\n{proc.stdout}")
    payload = _parse_json_stdout(proc.stdout)
    rows = payload if isinstance(payload, list) else [payload]
    obligation_count = 0
    rule_count = 0
    error_count = 0
    for row in rows:
        error_count += int(row.get("error_count", 0) or 0)
        rules = row.get("rules", []) or []
        rule_count += len(rules)
        for rule in rules:
            obligation_count += len(rule.get("obligations", []) or [])
    print(
        f"  pdd contracts compile: {rule_count} rule(s), {obligation_count} obligation(s), "
        f"{error_count} compile error(s) (exit {proc.returncode})"
    )
    return {
        "payload": payload,
        "rule_count": rule_count,
        "obligation_count": obligation_count,
        "error_count": error_count,
    }


def _step_coverage(runner: CliRunner, prompt: Path) -> dict[str, Any]:
    proc = _run_cli(
        runner,
        [
            "--quiet",
            "coverage",
            "--contracts",
            "--json",
            "--stories-dir",
            "user_stories",
            "--tests-dir",
            "tests",
            str(prompt.relative_to(_DEMO_DIR)),
        ],
        allow_warn_exit=True,
    )
    if proc.returncode not in (0, 1):
        raise RuntimeError(f"pdd coverage failed:\n{proc.stdout}")
    payload = _parse_json_stdout(proc.stdout)
    rows = payload.get("results", []) if isinstance(payload, dict) else payload
    rules = rows[0].get("rules", []) if rows else []
    summary = rows[0].get("summary", {}) if rows else {}
    print(
        f"  pdd coverage --contracts: {len(rules)} rule(s); "
        f"checked={summary.get('checked', 0)} story_only={summary.get('story_only', 0)} "
        f"unchecked={summary.get('unchecked', 0)}"
    )
    return {"payload": payload, "rule_count": len(rules), "summary": summary}


def _step_prompt_lint_contracts_json(runner: CliRunner, prompt: Path) -> dict[str, Any]:
    proc = _run_cli(
        runner,
        [
            "--quiet",
            "prompt",
            "lint",
            "--contracts",
            "--json",
            "--stories",
            "user_stories",
            "--tests-dir",
            "tests",
            str(prompt.relative_to(_DEMO_DIR)),
        ],
        allow_warn_exit=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"prompt lint --contracts failed:\n{proc.stdout}")
    payload = _parse_json_stdout(proc.stdout)
    coverage = payload.get("coverage", []) if isinstance(payload, dict) else []
    rules = coverage[0].get("rules", []) if coverage else []
    print(f"  pdd prompt lint --contracts: {len(rules)} rule(s) in coverage matrix")
    return {"payload": payload, "rule_count": len(rules)}


def _step_formalization_report(runner: CliRunner, prompt: Path) -> dict[str, Any]:
    proc = _run_cli(
        runner,
        [
            "--quiet",
            "prompt",
            "lint",
            "--report",
            "formalization",
            "--json",
            str(prompt.relative_to(_DEMO_DIR)),
        ],
        allow_warn_exit=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"formalization report failed:\n{proc.stdout}")
    payload = _parse_json_stdout(proc.stdout)
    rows = payload if isinstance(payload, list) else payload.get("results", [])
    issue_count = sum(len(r.get("issues", []) or []) for r in rows)
    print(f"  pdd prompt lint --report formalization: {issue_count} issue(s)")
    return {"payload": payload, "file_count": len(rows), "issue_count": issue_count}


# ---------------------------------------------------------------------------
# Per-fixture orchestration
# ---------------------------------------------------------------------------


def _run_all_checks(runner: CliRunner, prompt: Path, label: str) -> dict[str, Any]:
    """Run every deterministic command against ``prompt`` and return a snapshot."""
    _sub(f"{label}: pdd prompt lint")
    text_lint = _step_prompt_lint(runner, prompt, label="(plain)")
    _sub(f"{label}: pdd prompt lint --json")
    json_lint = _step_prompt_lint_json(runner, prompt)
    _sub(f"{label}: pdd contracts check --json")
    contracts = _step_contracts_check(runner, prompt)
    _sub(f"{label}: pdd contracts compile --json")
    compiled = _step_contracts_compile(runner, prompt)
    _sub(f"{label}: pdd coverage --contracts --json")
    coverage = _step_coverage(runner, prompt)
    _sub(f"{label}: pdd prompt lint --contracts --json")
    lint_contracts = _step_prompt_lint_contracts_json(runner, prompt)
    _sub(f"{label}: pdd prompt lint --report formalization --json")
    formalization = _step_formalization_report(runner, prompt)
    return {
        "label": label,
        "prompt": str(prompt.relative_to(_DEMO_DIR)),
        "lint": text_lint,
        "lint_json": json_lint,
        "contracts_check": contracts,
        "contracts_compile": compiled,
        "coverage": coverage,
        "lint_contracts": lint_contracts,
        "formalization": formalization,
    }


def _summary_row(label: str, snap: dict[str, Any]) -> dict[str, Any]:
    return {
        "label": label,
        "prompt": snap["prompt"],
        "lint_warn_count": snap["lint"]["warn_count"],
        "lint_error_count": snap["lint"]["error_count"],
        "lint_by_code": snap["lint_json"]["by_code"],
        "contracts_check_issues": snap["contracts_check"]["issue_count"],
        "compile_rules": snap["contracts_compile"]["rule_count"],
        "compile_obligations": snap["contracts_compile"]["obligation_count"],
        "compile_errors": snap["contracts_compile"]["error_count"],
        "coverage_summary": snap["coverage"]["summary"],
        "formalization_issues": snap["formalization"]["issue_count"],
    }


def _print_comparison(rows: list[dict[str, Any]]) -> None:
    headers = (
        "fixture",
        "lint(warn/err)",
        "compile(rules/oblig/errs)",
        "coverage(checked/story_only/unchecked)",
        "formal_issues",
    )

    def fmt(row: dict[str, Any]) -> tuple[str, ...]:
        s = row["coverage_summary"] or {}
        return (
            row["label"],
            f"{row['lint_warn_count']}/{row['lint_error_count']}",
            f"{row['compile_rules']}/{row['compile_obligations']}/{row['compile_errors']}",
            f"{s.get('checked', 0)}/{s.get('story_only', 0)}/{s.get('unchecked', 0)}",
            str(row["formalization_issues"]),
        )

    table = [headers, *[fmt(r) for r in rows]]
    widths = [max(len(c) for c in col) for col in zip(*table)]
    for i, line in enumerate(table):
        print("  " + "  ".join(c.ljust(w) for c, w in zip(line, widths)))
        if i == 0:
            print("  " + "  ".join("-" * w for w in widths))


# ---------------------------------------------------------------------------
# Cleanup / artifacts
# ---------------------------------------------------------------------------


def _cleanup(paths: dict[str, Path]) -> None:
    for key in ("work", "src_before", "src_after", "test_before", "test_after"):
        if key in paths and paths[key].exists():
            paths[key].unlink()
    for legacy in (
        _DEMO_DIR / "src" / "foo_work.py",
        _DEMO_DIR / "tests" / "test_foo_work.py",
    ):
        if legacy.exists():
            legacy.unlink()
    for sub in ("src", "tests"):
        d = _DEMO_DIR / sub
        if not d.exists():
            continue
        for cache in d.rglob("__pycache__"):
            shutil.rmtree(cache, ignore_errors=True)
        if not any(d.iterdir()):
            d.rmdir()


def _write_report(report_dir: Path, name: str, payload: Any) -> None:
    report_dir.mkdir(exist_ok=True)
    (report_dir / f"{name}.json").write_text(
        json.dumps(payload, indent=2) + "\n",
        encoding="utf-8",
    )


def _save_artifact(
    src: Path,
    artifacts_dir: Path,
    rel_dst: str,
) -> Path:
    """Copy ``src`` into ``artifacts_dir / rel_dst``, creating parents."""
    dst = artifacts_dir / rel_dst
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)
    return dst


def _write_diff(
    a_path: Path,
    b_path: Path,
    diffs_dir: Path,
    name: str,
    *,
    label_a: str | None = None,
    label_b: str | None = None,
) -> tuple[Path, int]:
    """Write a unified diff of two files; return (path, hunk_count)."""
    diffs_dir.mkdir(parents=True, exist_ok=True)
    a_text = a_path.read_text(encoding="utf-8").splitlines(keepends=True)
    b_text = b_path.read_text(encoding="utf-8").splitlines(keepends=True)
    lines = list(
        difflib.unified_diff(
            a_text,
            b_text,
            fromfile=label_a or str(a_path.name),
            tofile=label_b or str(b_path.name),
            n=3,
        )
    )
    dst = diffs_dir / name
    dst.write_text("".join(lines), encoding="utf-8")
    hunks = sum(1 for line in lines if line.startswith("@@"))
    return dst, hunks


# ---------------------------------------------------------------------------
# Deterministic mode
# ---------------------------------------------------------------------------


def run_deterministic() -> int:
    paths = _paths()
    for key, label in (("vague", _VAGUE_NAME), ("formalized", _FORMALIZED_NAME)):
        if not paths[key].is_file():
            print(f"ERROR: missing input prompt {paths[key]}", file=sys.stderr)
            return 1

    os.chdir(_DEMO_DIR)
    runner = CliRunner()
    paths["reports"].mkdir(exist_ok=True)

    _hdr("① VAGUE fixture (negative): prompts/foo_vague_python.prompt")
    vague = _run_all_checks(runner, paths["vague"], label="vague")

    _hdr("② FORMALIZED fixture (positive): prompts/foo_formalized_python.prompt")
    formalized = _run_all_checks(runner, paths["formalized"], label="formalized")

    _write_report(paths["reports"], "vague", vague)
    _write_report(paths["reports"], "formalized", formalized)

    # Deterministic pair: vague → formalized (separate names from live codegen snapshots).
    _save_artifact(paths["vague"], paths["artifacts"], "prompt_vague.prompt")
    _save_artifact(paths["formalized"], paths["artifacts"], "prompt_formalized.prompt")
    diff_path, hunks = _write_diff(
        paths["vague"],
        paths["formalized"],
        paths["diffs"],
        "prompt_vague_vs_formalized.diff",
        label_a="prompts/foo_vague_python.prompt",
        label_b="prompts/foo_formalized_python.prompt",
    )
    print(
        f"\n  artifacts: reports/artifacts/prompt_vague.prompt, "
        f"reports/artifacts/prompt_formalized.prompt"
    )
    print(
        f"  diff: {diff_path.relative_to(_DEMO_DIR)} ({hunks} hunk(s))"
    )

    vague_row = _summary_row("vague", vague)
    formalized_row = _summary_row("formalized", formalized)
    comparison = {
        "mode": "deterministic",
        "commands": [
            "pdd prompt lint",
            "pdd prompt lint --json",
            "pdd contracts check --json --stories user_stories",
            "pdd contracts compile --json",
            "pdd coverage --contracts --json --stories-dir user_stories --tests-dir tests",
            "pdd prompt lint --contracts --json",
            "pdd prompt lint --report formalization --json",
        ],
        "rows": [vague_row, formalized_row],
    }
    _write_report(paths["reports"], "comparison", comparison)

    _hdr("③ Side-by-side")
    _print_comparison([vague_row, formalized_row])

    # Success criteria: the demo *must* show the expected contrast between the
    # vague and formalized fixtures. If either fails, fail the demo.
    failures: list[str] = []
    if vague_row["lint_warn_count"] < 10:
        failures.append(
            f"vague fixture expected >=10 lint warnings, got {vague_row['lint_warn_count']}"
        )
    if vague_row["compile_errors"] < 1:
        failures.append(
            f"vague fixture expected >=1 compile error, got {vague_row['compile_errors']}"
        )
    if vague_row["coverage_summary"].get("unchecked", 0) < 1:
        failures.append("vague fixture expected >=1 unchecked rule in coverage")
    if formalized_row["compile_errors"] != 0:
        failures.append(
            f"formalized fixture expected 0 compile errors, got {formalized_row['compile_errors']}"
        )
    if formalized_row["compile_obligations"] < 6:
        failures.append(
            f"formalized fixture expected >=6 obligations, got "
            f"{formalized_row['compile_obligations']}"
        )
    if formalized_row["coverage_summary"].get("unchecked", 0) != 0:
        failures.append("formalized fixture expected 0 unchecked rules in coverage")
    if "VAGUE_TERM_UNDEFINED" in formalized_row["lint_by_code"]:
        failures.append(
            "formalized fixture must not raise VAGUE_TERM_UNDEFINED — vocabulary should cover it"
        )
    if "VAGUE_NO_OBSERVABLE_OUTCOME" in formalized_row["lint_by_code"]:
        failures.append(
            "formalized fixture must not raise VAGUE_NO_OBSERVABLE_OUTCOME"
        )
    if formalized_row["lint_warn_count"] > 5:
        failures.append(
            f"formalized fixture lint warnings too high ({formalized_row['lint_warn_count']})"
        )

    if failures:
        print("\n  Deterministic FAILED:", file=sys.stderr)
        for f in failures:
            print(f"    - {f}", file=sys.stderr)
        return 1
    print(
        "\n  Deterministic E2E passed: vague fixture trips every check, "
        "formalized fixture passes the structural ones."
    )
    return 0


# ---------------------------------------------------------------------------
# Live mode (real LLM)
# ---------------------------------------------------------------------------


def _step_clarify_apply(runner: CliRunner, prompt: Path) -> dict[str, Any]:
    """Real LLM: pdd prompt lint --ambiguity --non-interactive --apply --contracts --json."""
    proc = _run_cli(
        runner,
        [
            "--quiet",
            "prompt",
            "lint",
            "--ambiguity",
            "--non-interactive",
            "--apply",
            "--contracts",
            "--json",
            "--stories",
            "user_stories",
            "--tests-dir",
            "tests",
            str(prompt.relative_to(_DEMO_DIR)),
        ],
        allow_warn_exit=True,
    )
    if proc.returncode not in (0, 1):
        raise RuntimeError(f"pdd prompt lint --apply failed:\n{proc.stdout}")
    if not proc.stdout.strip():
        raise _LLMUnavailable(
            "pdd prompt lint --apply returned no JSON — every LLM provider "
            "in the fallback chain failed (rate limit, auth, or unsupported "
            "model). Check Gemini quota and PDD_MODEL_DEFAULT."
        )
    payload = _parse_json_stdout(proc.stdout)
    guidance = payload.get("guidance", []) if isinstance(payload, dict) else []
    ambiguities = guidance[0].get("ambiguities", []) if guidance else []
    rejected = guidance[0].get("formalization_rejected", []) if guidance else []
    print(
        f"  pdd prompt lint --apply: {len(ambiguities)} ambiguity(ies), "
        f"{len(rejected)} formalization candidate(s) rejected"
    )
    return {
        "payload": payload,
        "ambiguity_count": len(ambiguities),
        "formalization_rejected_count": len(rejected),
    }


def _step_generate(runner: CliRunner, prompt: Path, output: Path) -> dict[str, Any]:
    output.parent.mkdir(exist_ok=True)
    proc = _run_cli(
        runner,
        [
            "--quiet",
            "--force",
            "generate",
            str(prompt.relative_to(_DEMO_DIR)),
            "--output",
            str(output.relative_to(_DEMO_DIR)),
        ],
    )
    if proc.returncode != 0:
        raise RuntimeError(f"pdd generate failed:\n{proc.stdout}")
    if not output.is_file():
        raise RuntimeError(f"pdd generate did not produce {output}")
    size = output.stat().st_size
    if size == 0:
        raise _LLMUnavailable(
            "pdd generate produced a 0-byte file — every model in the "
            "fallback chain failed to answer."
        )
    print(f"  pdd generate → {output.relative_to(_DEMO_DIR)} ({size} bytes)")
    return {"path": str(output.relative_to(_DEMO_DIR)), "byte_size": size}


def _step_test(
    runner: CliRunner,
    prompt: Path,
    source: Path,
    output: Path,
) -> dict[str, Any]:
    output.parent.mkdir(exist_ok=True)
    proc = _run_cli(
        runner,
        [
            "--quiet",
            "test",
            "--manual",
            str(prompt.relative_to(_DEMO_DIR)),
            str(source.relative_to(_DEMO_DIR)),
            "--output",
            str(output.relative_to(_DEMO_DIR)),
        ],
    )
    if proc.returncode != 0:
        raise RuntimeError(f"pdd test failed:\n{proc.stdout}")
    if not output.is_file():
        raise RuntimeError(f"pdd test did not produce {output}")
    size = output.stat().st_size
    if size == 0:
        raise _LLMUnavailable("pdd test produced a 0-byte file — LLM unavailable.")
    print(f"  pdd test --manual → {output.relative_to(_DEMO_DIR)} ({size} bytes)")
    return {"path": str(output.relative_to(_DEMO_DIR)), "byte_size": size}


def _step_pytest(test_file: Path) -> dict[str, Any]:
    proc = subprocess.run(
        [sys.executable, "-m", "pytest", str(test_file.relative_to(_DEMO_DIR)), "-q"],
        cwd=_DEMO_DIR,
        capture_output=True,
        text=True,
        check=False,
    )
    passed = proc.returncode == 0
    print(f"  pytest {test_file.name}: {'PASS' if passed else 'FAIL'}")
    if not passed:
        print(proc.stdout)
        print(proc.stderr, file=sys.stderr)
    return {"passed": passed, "exit_code": proc.returncode}


def run_live(*, keep_artifacts: bool = False) -> int:
    """Delegate to the bash live pipeline (real ``pdd`` CLI + artifact snapshots)."""
    live_script = _DEMO_DIR / "lib" / "live_pipeline.sh"
    if not live_script.is_file():
        print(f"ERROR: missing {live_script}", file=sys.stderr)
        return 1

    env = {**os.environ, "KEEP_ARTIFACTS": "1" if keep_artifacts else "0"}
    proc = subprocess.run(
        ["bash", str(live_script)],
        cwd=_DEMO_DIR,
        env=env,
        check=False,
    )
    return proc.returncode


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "End-to-end demo of pdd prompt lint / pdd contracts / pdd coverage "
            "on a paired vague + formalized fixture."
        ),
    )
    parser.add_argument(
        "--live",
        action="store_true",
        help="Real LLM chain on foo_codegen work copy: clarify + generate + test + pytest.",
    )
    parser.add_argument(
        "--keep-artifacts",
        action="store_true",
        help="Keep work copy, generated src/, and tests/ after --live.",
    )
    parser.add_argument(
        "--cleanup",
        action="store_true",
        help="Remove work copy and generated artifacts, then exit.",
    )
    args = parser.parse_args()

    if args.cleanup:
        _cleanup(_paths())
        print("Cleaned up demo artifacts.")
        return 0
    if args.live:
        return run_live(keep_artifacts=args.keep_artifacts)
    return run_deterministic()


if __name__ == "__main__":
    raise SystemExit(main())
