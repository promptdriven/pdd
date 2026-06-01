#!/usr/bin/env python3
"""A0→A1 formalization via PDD Cloud CLI (``pdd generate``, ``pdd checkup lint --llm``).

A0 corpus files stay handcrafted. A1 is produced by ``pdd generate`` (cloud by default,
no ``--local``) using the benchmark formalizer meta-prompt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

_PIPELINE_DIR = Path(__file__).resolve().parent
_BENCHMARK_ROOT = _PIPELINE_DIR.parent
_REPO_ROOT = _BENCHMARK_ROOT.parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
if str(_PIPELINE_DIR) not in sys.path:
    sys.path.insert(0, str(_PIPELINE_DIR))

from command_log import pdd_subprocess_env, run_logged_command  # noqa: E402

SCRIPT_VERSION = "cloud_formalize_v1"
FORMALIZER_META = _PIPELINE_DIR / "templates" / "benchmark_a1_formalizer_prompt.prompt"
INPUT_A0_NAME = "INPUT_A0.prompt"


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _find_pdd() -> str:
    import shutil as sh

    found = sh.which("pdd")
    if found:
        return found
    return sys.executable


def _pdd_base_cmd() -> list[str]:
    """PDD CLI without ``--local`` so cloud routing is used when configured."""
    pdd = _find_pdd()
    if Path(pdd).name in {"python", "python3"}:
        return [pdd, "-m", "pdd"]
    return [pdd]


def _with_strength(command: list[str], pdd_strength: Optional[float]) -> list[str]:
    if pdd_strength is None:
        return command
    return command + ["--strength", str(pdd_strength)]


def _run_lint_llm(
    a0_path: Path,
    *,
    project_root: Path,
    commands_log: Optional[Path],
    pdd_strength: Optional[float] = None,
    subprocess_env: Optional[dict[str, str]] = None,
) -> tuple[int, list[dict[str, Any]]]:
    """Run ``pdd checkup lint --llm --json`` (PDD Cloud advisory)."""
    entry = run_logged_command(
        _with_strength(
            _pdd_base_cmd() + ["checkup", "lint", str(a0_path), "--llm", "--json"],
            pdd_strength,
        ),
        cwd=project_root,
        log_path=commands_log,
        capture_stdout=True,
        env=subprocess_env,
    )
    issues: list[dict[str, Any]] = []
    if entry.get("exit_code") in (0, 1) and entry.get("stdout"):
        try:
            payload = json.loads(entry["stdout"])
            if isinstance(payload, list):
                for result in payload:
                    issues.extend(result.get("issues") or [])
        except json.JSONDecodeError:
            pass
    return int(entry.get("exit_code") or 1), issues


def _write_generate_workspace(
    workspace: Path,
    a0_path: Path,
    lint_issues: list[dict[str, Any]],
) -> Path:
    """Build per-run meta-prompt with embedded A0 include and lint guidance."""
    shutil.copy2(a0_path, workspace / INPUT_A0_NAME)
    template = FORMALIZER_META.read_text(encoding="utf-8")
    guidance_block = json.dumps(
        [i for i in lint_issues[:40]],
        indent=2,
    ) if lint_issues else "[]"
    filled = template.replace("{guidance_block}", guidance_block)
    meta_path = workspace / "benchmark_a1_formalizer.prompt"
    meta_path.write_text(filled, encoding="utf-8")
    return meta_path


def _run_cloud_generate(
    meta_prompt: Path,
    output_path: Path,
    *,
    project_root: Path,
    commands_log: Optional[Path],
    pdd_strength: Optional[float] = None,
    subprocess_env: Optional[dict[str, str]] = None,
) -> dict[str, Any]:
    """Run ``pdd generate`` to write formalized A1 (PDD Cloud)."""
    output_path.parent.mkdir(parents=True, exist_ok=True)
    return run_logged_command(
        _with_strength(
            _pdd_base_cmd()
            + [
                "--force",
                "generate",
                str(meta_prompt),
                "--output",
                str(output_path),
                "--evidence",
            ],
            pdd_strength,
        ),
        cwd=project_root,
        log_path=commands_log,
        env=subprocess_env,
    )


def _checkup_pass_summary(
    prompt_path: Path,
    *,
    project_root: Path,
    stories_dir: Optional[Path],
) -> dict[str, Any]:
    """Read-only checkup metrics on generated A1 (no write-back)."""
    from pdd.contract_check import check_prompt  # pylint: disable=import-outside-toplevel
    from pdd.coverage_contracts import build_coverage  # pylint: disable=import-outside-toplevel
    from pdd.prompt_lint import scan_prompt  # pylint: disable=import-outside-toplevel

    lint = scan_prompt(prompt_path)
    contract = check_prompt(prompt_path, strict=False)
    coverage = build_coverage(prompt_path, stories_dir=stories_dir)
    unchecked = sum(1 for r in coverage.rules if r.status in ("unchecked", "failed"))
    return {
        "lint_exit_code": 1 if lint.warn_count or lint.error_count else 0,
        "contract_exit_code": 2 if contract.error_count else (1 if contract.warn_count else 0),
        "coverage_exit_code": 1 if unchecked else 0,
        "lint_warnings": lint.warn_count,
        "lint_errors": lint.error_count,
        "contract_errors": contract.error_count,
        "contract_warnings": contract.warn_count,
        "coverage_unchecked": unchecked,
        "checkup_pass": (
            lint.error_count == 0
            and contract.error_count == 0
            and unchecked == 0
        ),
    }


def formalize(
    *,
    input_path: Path,
    output_path: Path,
    commands_log: Optional[Path],
    dry_run: bool,
    verbose: bool,  # pylint: disable=unused-argument
    project_root: Path,
    stories_dir: Optional[Path] = None,
    skip_lint_llm: bool = False,
    pdd_strength: Optional[float] = None,
    pdd_model: Optional[str] = None,
    pdd_force_local: bool = False,
    pdd_cloud_only: bool = False,
) -> dict[str, Any]:
    """Produce A1 via PDD Cloud; return manifest dict."""
    if not input_path.is_file():
        raise FileNotFoundError(f"Input not found: {input_path}")

    manifest: dict[str, Any] = {
        "script_version": SCRIPT_VERSION,
        "formalizer": "pdd_cloud",
        "started_at": datetime.now(timezone.utc).isoformat(),
        "input": str(input_path),
        "output": str(output_path),
        "input_sha256": _sha256(input_path),
        "dry_run": dry_run,
        "stories_dir": str(stories_dir) if stories_dir else None,
        "iterations": [],
    }

    if dry_run:
        manifest["finished_at"] = datetime.now(timezone.utc).isoformat()
        manifest["summary"] = {
            "cloud_generate": False,
            "note": "dry-run: A0 only; no pdd generate",
        }
        return manifest

    subprocess_env = pdd_subprocess_env(
        model=pdd_model if pdd_force_local else None,
        force_local=pdd_force_local,
        cloud_only=pdd_cloud_only,
    )

    lint_code = 0
    lint_issues: list[dict[str, Any]] = []
    if not skip_lint_llm:
        lint_code, lint_issues = _run_lint_llm(
            input_path,
            project_root=project_root,
            commands_log=commands_log,
            pdd_strength=pdd_strength,
            subprocess_env=subprocess_env,
        )
        manifest["iterations"].append(
            {"stage": "checkup_lint_llm", "exit_code": lint_code, "issues": len(lint_issues)},
        )

    with tempfile.TemporaryDirectory(prefix="pdd_cloud_formalize_") as tmp:
        workspace = Path(tmp)
        meta_prompt = _write_generate_workspace(workspace, input_path, lint_issues)
        gen_entry = _run_cloud_generate(
            meta_prompt,
            output_path,
            project_root=project_root,
            commands_log=commands_log,
            pdd_strength=pdd_strength,
            subprocess_env=subprocess_env,
        )
        manifest["iterations"].append(
            {
                "stage": "pdd_generate",
                "exit_code": gen_entry.get("exit_code"),
                "cost_usd": gen_entry.get("cost_usd"),
                "wall_clock_s": gen_entry.get("wall_clock_s"),
                "model_hint": _model_from_tail(gen_entry.get("stderr_tail", "")),
            },
        )

    if gen_entry.get("exit_code") != 0:
        manifest["finished_at"] = datetime.now(timezone.utc).isoformat()
        manifest["summary"] = {
            "cloud_generate": False,
            "generate_exit_code": gen_entry.get("exit_code"),
            "error": "pdd generate failed",
        }
        return manifest

    checkup = _checkup_pass_summary(
        output_path, project_root=project_root, stories_dir=stories_dir,
    )
    manifest["finished_at"] = datetime.now(timezone.utc).isoformat()
    manifest["output_sha256"] = _sha256(output_path)
    text = output_path.read_text(encoding="utf-8")
    manifest["summary"] = {
        "cloud_generate": True,
        "generate_exit_code": 0,
        "lint_llm_issues": len(lint_issues),
        "code_source": "pdd_cloud_generate",
        "has_vocabulary": "<vocabulary>" in text,
        "has_contract_rules": "<contract_rules>" in text,
        "has_coverage": "<coverage>" in text,
        **checkup,
    }
    return manifest


def replay_a1(*, recorded_a1: Path, output_path: Path) -> dict[str, Any]:
    """Copy a previously recorded cloud A1 (CI replay without API keys)."""
    if not recorded_a1.is_file():
        raise FileNotFoundError(f"Recorded A1 not found: {recorded_a1}")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(recorded_a1, output_path)
    return {
        "script_version": SCRIPT_VERSION,
        "formalizer": "replay",
        "input": str(recorded_a1),
        "output": str(output_path),
        "summary": {
            "cloud_generate": False,
            "replay": True,
            "code_source": "pdd_generated_fixture",
        },
    }


def _model_from_tail(stderr: str) -> str:
    match = re.search(r"Model:\s*(\S+)", stderr)
    return match.group(1) if match else ""


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="A0→A1 via PDD Cloud (pdd generate)")
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--commands-log", type=Path, default=None)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--stories-dir", type=Path, default=None)
    parser.add_argument("--skip-lint-llm", action="store_true")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--project-root", type=Path, default=_REPO_ROOT)
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    manifest = formalize(
        input_path=args.input.resolve(),
        output_path=args.output.resolve(),
        commands_log=args.commands_log.resolve() if args.commands_log else None,
        dry_run=args.dry_run,
        verbose=args.verbose,
        project_root=args.project_root.resolve(),
        stories_dir=args.stories_dir.resolve() if args.stories_dir else None,
        skip_lint_llm=args.skip_lint_llm,
    )
    if args.as_json:
        print(json.dumps(manifest, indent=2))
    else:
        print(f"Wrote A1: {args.output}")
        print(f"  summary: {manifest.get('summary')}")
    return 0 if (
        manifest.get("summary", {}).get("cloud_generate")
        or manifest.get("dry_run")
        or manifest.get("summary", {}).get("replay")
    ) else 1


if __name__ == "__main__":
    raise SystemExit(main())
