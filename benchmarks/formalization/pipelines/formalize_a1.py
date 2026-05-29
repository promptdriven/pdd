#!/usr/bin/env python3
"""Pinned A0→A1 formalization pipeline for the formalization benchmark.

Deterministic vocabulary writeback works without network access.
Pass ``--allow-llm`` for ambiguity + formalize LLM stages (requires credentials).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import sys
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

from pdd.prompt_lint import LintIssue, scan_prompt  # noqa: E402

import writeback  # noqa: E402

SCRIPT_VERSION = "formalize_a1_v1"
DEFAULT_TEMPLATE = Path(__file__).resolve().parent / "templates" / "formalize_a1.prompt"
DEFAULT_MAX_ITERS = 5


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _append_command_log(log_path: Optional[Path], entry: dict[str, Any]) -> None:
    if log_path is None:
        return
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(entry, sort_keys=True) + "\n")


def _concrete_suggestions(issues: list[LintIssue]) -> list[str]:
    return [
        issue.suggestion.strip()
        for issue in issues
        if issue.suggestion.strip() and "<add a precise" not in issue.suggestion
    ]


def _bootstrap_suggestions(issues: list[LintIssue]) -> list[str]:
    """Turn vague-term lint hits into minimal observable vocabulary lines."""
    suggestions = _concrete_suggestions(issues)
    seen = {s.split(":", 1)[0].strip().lower() for s in suggestions if ":" in s}
    for issue in issues:
        term = issue.term.strip().lower()
        if not term or term in seen:
            continue
        line = issue.line.lower()
        verb = "returns"
        for candidate in (
            "returns", "raises", "rejects", "writes", "emits", "logs", "stores",
        ):
            if candidate in line:
                verb = candidate
                break
        suggestions.append(
            f"{issue.term}: {verb} an observable outcome defined by this prompt's rules"
        )
        seen.add(term)
    return suggestions


def _deterministic_pass(path: Path) -> tuple[int, int]:
    """Apply vocabulary from deterministic lint scan; return (written, remaining warnings)."""
    result = scan_prompt(path)
    suggestions = _bootstrap_suggestions(result.issues)
    written = writeback.append_vocabulary_definitions(path, suggestions)
    after = scan_prompt(path)
    return written, after.warn_count


def _run_llm_ambiguity(path: Path, *, verbose: bool) -> list[LintIssue]:
    from pdd.prompt_lint import run_llm_ambiguity_pass  # pylint: disable=import-outside-toplevel

    return run_llm_ambiguity_pass(
        path,
        strength=0.5,
        temperature=0.0,
        verbose=verbose,
    )


def _run_llm_formalize(
    path: Path,
    template_path: Path,
    guidance: dict[str, Any],
    *,
    verbose: bool,
) -> dict[str, Any]:
    """Call pinned template via llm_invoke; return parsed bundle or error dict."""
    from pdd.llm_invoke import llm_invoke  # pylint: disable=import-outside-toplevel
    from pdd.preprocess import preprocess  # pylint: disable=import-outside-toplevel

    template = template_path.read_text(encoding="utf-8")
    filled = (
        template.replace("{prompt_content}", path.read_text(encoding="utf-8"))
        .replace("{guidance_json}", json.dumps(guidance, indent=2))
    )
    filled = preprocess(filled, recursive=False, double_curly_brackets=False)
    result = llm_invoke(
        messages=[{"role": "user", "content": filled}],
        strength=0.5,
        temperature=0.0,
        verbose=verbose,
        use_cloud=True,
    )
    response_text = result.get("result", "")
    json_match = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", response_text, re.DOTALL)
    raw_json = json_match.group(1) if json_match else response_text.strip()
    bundle = json.loads(raw_json)
    if not isinstance(bundle, dict):
        raise ValueError("formalize response was not a JSON object")
    bundle["_meta"] = {"cost": result.get("cost", 0.0), "model": result.get("model", "")}
    return bundle


def formalize(
    *,
    input_path: Path,
    output_path: Path,
    commands_log: Optional[Path],
    template_path: Path,
    max_iters: int,
    allow_llm: bool,
    dry_run: bool,
    verbose: bool,
    project_root: Path,  # pylint: disable=unused-argument
) -> dict[str, Any]:
    """Run the full A0→A1 pipeline; return summary dict."""
    if not input_path.is_file():
        raise FileNotFoundError(f"Input not found: {input_path}")

    output_path.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(input_path, output_path)

    input_hash = _sha256(input_path)
    template_hash = _sha256(template_path) if template_path.is_file() else ""

    manifest: dict[str, Any] = {
        "script_version": SCRIPT_VERSION,
        "started_at": datetime.now(timezone.utc).isoformat(),
        "input": str(input_path),
        "output": str(output_path),
        "input_sha256": input_hash,
        "template_sha256": template_hash,
        "allow_llm": allow_llm,
        "dry_run": dry_run,
        "iterations": [],
    }

    total_vocab_written = 0
    if not dry_run:
        for iteration in range(1, max_iters + 1):
            written, warn_count = _deterministic_pass(output_path)
            total_vocab_written += written
            step = {
                "iteration": iteration,
                "stage": "deterministic_vocabulary",
                "vocabulary_written": written,
                "lint_warnings": warn_count,
            }
            manifest["iterations"].append(step)
            _append_command_log(commands_log, step)
            if written == 0:
                break

        rules_written = writeback.bootstrap_contract_rules_from_requirements(output_path)
        if rules_written:
            bootstrap_step = {
                "stage": "deterministic_contract_rules",
                "contract_rules_written": rules_written,
            }
            manifest["iterations"].append(bootstrap_step)
            _append_command_log(commands_log, bootstrap_step)

    if allow_llm and not dry_run:
        llm_issues = _run_llm_ambiguity(output_path, verbose=verbose)
        llm_suggestions = _concrete_suggestions(llm_issues)
        llm_written = writeback.append_vocabulary_definitions(output_path, llm_suggestions)
        total_vocab_written += llm_written
        guidance = {
            "lint_issues": [issue.as_dict() for issue in llm_issues],
            "path": str(output_path),
        }
        ambiguity_step = {
            "stage": "llm_ambiguity",
            "issues": len(llm_issues),
            "vocabulary_written": llm_written,
        }
        manifest["iterations"].append(ambiguity_step)
        _append_command_log(commands_log, ambiguity_step)

        try:
            bundle = _run_llm_formalize(
                output_path, template_path, guidance, verbose=verbose,
            )
            bundle_counts = writeback.merge_formalize_bundle(output_path, bundle)
            formalize_step = {
                "stage": "llm_formalize",
                "bundle_counts": bundle_counts,
                "model": bundle.get("_meta", {}).get("model"),
                "cost_usd": bundle.get("_meta", {}).get("cost"),
            }
            manifest["iterations"].append(formalize_step)
            _append_command_log(commands_log, formalize_step)
        except Exception as exc:  # pylint: disable=broad-exception-caught
            err = {"stage": "llm_formalize", "error": str(exc)}
            manifest["iterations"].append(err)
            _append_command_log(commands_log, err)

    lint_after = scan_prompt(output_path)
    from pdd.contract_check import check_prompt as check_contract_prompt  # pylint: disable=import-outside-toplevel

    contract_result = check_contract_prompt(output_path, strict=False)
    contract_check = {
        "stage": "contract_check",
        "exit_code": 1 if contract_result.error_count else 0,
        "errors": contract_result.error_count,
        "warnings": contract_result.warn_count,
    }
    _append_command_log(commands_log, contract_check)

    sections = writeback.extract_sections(output_path.read_text(encoding="utf-8"))
    manifest["finished_at"] = datetime.now(timezone.utc).isoformat()
    manifest["output_sha256"] = _sha256(output_path)
    manifest["summary"] = {
        "vocabulary_written_total": total_vocab_written,
        "lint_warnings": lint_after.warn_count,
        "lint_errors": lint_after.error_count,
        "has_vocabulary": "vocabulary" in sections,
        "has_contract_rules": "contract_rules" in sections,
        "has_formalization": "formalization" in sections,
        "contract_check_exit_code": contract_check.get("exit_code"),
    }
    return manifest


def main(argv: Optional[list[str]] = None) -> int:
    """CLI entrypoint."""
    parser = argparse.ArgumentParser(description="Benchmark A0→A1 formalization pipeline")
    parser.add_argument("--input", type=Path, required=True, help="Handwritten A0 prompt")
    parser.add_argument("--output", type=Path, required=True, help="Generated A1 prompt path")
    parser.add_argument(
        "--commands-log",
        type=Path,
        default=None,
        help="Append JSONL audit log (one object per line)",
    )
    parser.add_argument(
        "--template",
        type=Path,
        default=DEFAULT_TEMPLATE,
        help="Pinned formalize LLM template",
    )
    parser.add_argument("--max-iters", type=int, default=DEFAULT_MAX_ITERS)
    parser.add_argument(
        "--allow-llm",
        action="store_true",
        help="Run LLM ambiguity + formalize stages (requires API credentials)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Copy input only; run deterministic lint metrics without writeback mutations",
    )
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument(
        "--project-root",
        type=Path,
        default=_REPO_ROOT,
        help="Repo root for subprocess checkup commands",
    )
    parser.add_argument("--json", action="store_true", dest="as_json", help="Print manifest JSON")
    args = parser.parse_args(argv)

    if args.dry_run and args.allow_llm:
        parser.error("--dry-run cannot be combined with --allow-llm")

    manifest = formalize(
        input_path=args.input.resolve(),
        output_path=args.output.resolve(),
        commands_log=args.commands_log.resolve() if args.commands_log else None,
        template_path=args.template.resolve(),
        max_iters=args.max_iters,
        allow_llm=args.allow_llm,
        dry_run=args.dry_run,
        verbose=args.verbose,
        project_root=args.project_root.resolve(),
    )

    if args.as_json:
        print(json.dumps(manifest, indent=2))
    else:
        summary = manifest["summary"]
        print(f"Wrote A1: {args.output}")
        print(f"  vocabulary entries added: {summary['vocabulary_written_total']}")
        print(f"  lint warnings: {summary['lint_warnings']}")
        print(f"  has_vocabulary: {summary['has_vocabulary']}")
        print(f"  has_contract_rules: {summary['has_contract_rules']}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
