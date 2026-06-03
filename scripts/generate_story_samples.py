#!/usr/bin/env python3
"""Generate sample user stories from real prompt files (issue #1356 demo)."""
from __future__ import annotations

import argparse
import shutil
from pathlib import Path

from pdd.user_story_tests import generate_user_story

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = REPO_ROOT / "context" / "generated_user_stories"

SCENARIOS: list[dict[str, object]] = [
    {
        "slug": "01_simple_greeting",
        "prompts": [REPO_ROOT / "examples/context_snapshot_demo/prompts/foo_python.prompt"],
    },
    {
        "slug": "02_refund_contract_demo",
        "prompts": [
            REPO_ROOT
            / "examples/architecture_contract_summary_demo/prompts/refund_python.prompt"
        ],
    },
    {
        "slug": "03_refund_policy_fixture",
        "prompts": [REPO_ROOT / "tests/fixtures/test_generation/refund_policy_python.prompt"],
    },
    {
        "slug": "04_contract_rules_fixture",
        "prompts": [REPO_ROOT / "tests/fixtures/contract_rules_python.prompt"],
    },
    {
        "slug": "05_snapshot_dynamic",
        "prompts": [REPO_ROOT / "examples/context_snapshot_demo/prompts/dynamic_python.prompt"],
    },
    {
        "slug": "06_csv_report_inline",
        "prompts": [],  # filled at runtime
        "inline_prompts": {
            "csv_report_python.prompt": (
                "Build a CSV report workflow.\n"
                "- Accept only .csv uploads with a header row.\n"
                "- Return row_count and column_names in the summary.\n"
                "- MUST NOT log raw uploaded cell values."
            ),
        },
    },
    {
        "slug": "07_multi_refund_and_greeting",
        "prompts": [
            REPO_ROOT
            / "examples/architecture_contract_summary_demo/prompts/refund_python.prompt",
            REPO_ROOT / "examples/context_snapshot_demo/prompts/foo_python.prompt",
        ],
    },
    {
        "slug": "08_multi_upload_notify_inline",
        "prompts": [],
        "inline_prompts": {
            "upload_python.prompt": (
                "Handle file uploads.\n"
                "- Accept PDF and CSV files up to 10 MB.\n"
                "- Return an upload_id on success."
            ),
            "notify_python.prompt": (
                "Send notifications when upload completes.\n"
                "- Email the uploader with the upload_id.\n"
                "- MUST NOT send notifications for failed uploads."
            ),
        },
    },
    {
        "slug": "09_code_generator_module",
        "prompts": [REPO_ROOT / "pdd/prompts/code_generator_python.prompt"],
    },
    {
        "slug": "10_generate_command",
        "prompts": [REPO_ROOT / "pdd/prompts/commands/generate_python.prompt"],
    },
]


def _prepare_prompts(
    scenario: dict[str, object],
    staging_dir: Path,
) -> tuple[list[str], Path | None]:
    """Copy repo prompts or write inline prompts into a staging directory."""
    staging_dir.mkdir(parents=True, exist_ok=True)
    prompt_paths: list[str] = []

    for src in scenario.get("prompts", []):
        src_path = Path(str(src))
        if not src_path.exists():
            raise FileNotFoundError(f"Prompt not found: {src_path}")
        dest = staging_dir / src_path.name
        shutil.copy2(src_path, dest)
        prompt_paths.append(str(dest))

    inline = scenario.get("inline_prompts")
    if isinstance(inline, dict):
        for name, content in inline.items():
            dest = staging_dir / str(name)
            dest.write_text(str(content), encoding="utf-8")
            prompt_paths.append(str(dest))

    if not prompt_paths:
        raise ValueError(f"No prompts configured for scenario: {scenario.get('slug')}")

    prompts_root = staging_dir if len(prompt_paths) > 1 or inline else None
    return prompt_paths, prompts_root


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=DEFAULT_OUT,
        help=f"Directory for generated story__*.md files (default: {DEFAULT_OUT})",
    )
    parser.add_argument(
        "--offline-only",
        action="store_true",
        help="Force deterministic fallback (skip LLM even if a provider key exists).",
    )
    args = parser.parse_args()

    out_dir = args.output_dir.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    summary_lines: list[str] = []
    summary_lines.append("# Generated user story samples (issue #1356)\n")
    summary_lines.append(
        "Stories produced by `generate_user_story()` from real or inline prompts.\n"
    )
    summary_lines.append(
        "When a provider key is available, the LLM path may be used; otherwise "
        "the deterministic fallback is used automatically.\n"
    )

    for scenario in SCENARIOS:
        slug = str(scenario["slug"])
        staging = out_dir / f".staging_{slug}"
        if staging.exists():
            shutil.rmtree(staging)

        prompt_paths, prompts_root = _prepare_prompts(scenario, staging)
        stories_dir = out_dir
        target = stories_dir / f"story__{slug}.md"

        kwargs: dict[str, object] = {
            "prompt_files": prompt_paths,
            "output": str(target),
            "stories_dir": str(stories_dir),
        }
        if prompts_root is not None:
            kwargs["prompts_dir"] = str(prompts_root)

        if args.offline_only:
            from unittest.mock import patch

            with patch(
                "pdd.user_story_tests._llm_generate_story_markdown",
                return_value=(None, 0.0, ""),
            ):
                success, message, cost, model, story_file, linked = generate_user_story(
                    **kwargs  # type: ignore[arg-type]
                )
        else:
            success, message, cost, model, story_file, linked = generate_user_story(
                **kwargs  # type: ignore[arg-type]
            )

        path_used = Path(str(story_file))
        mode = "offline-fallback" if (cost == 0.0 and model == "") else f"llm ({model})"
        summary_lines.append(f"\n## {slug}\n")
        summary_lines.append(f"- **Success:** {success}\n")
        summary_lines.append(f"- **Mode:** {mode}\n")
        summary_lines.append(f"- **Cost:** {cost}\n")
        summary_lines.append(f"- **Linked prompts:** {', '.join(linked)}\n")
        summary_lines.append(f"- **Output:** `{path_used.name}`\n")
        summary_lines.append(f"- **Message:** {message}\n")

        if staging.exists():
            shutil.rmtree(staging)

        print(f"[{'OK' if success else 'FAIL'}] {slug} -> {path_used.name} ({mode})")

    index_path = out_dir / "README.md"
    index_path.write_text("".join(summary_lines), encoding="utf-8")
    print(f"\nWrote index: {index_path}")
    print(f"Stories in:  {out_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
