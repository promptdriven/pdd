#!/usr/bin/env python3
"""Manual CLI validation for PR #1875 story-failure diagnostics.

Run from the PR worktree with the ``pdd`` conda environment active::

    conda run -n pdd python scripts/manual_validate_pr_1875.py

The first scenario makes a live Vertex AI call through this checkout's actual
``python -m pdd.cli`` entry point.  The second scenario is deterministic: it
exercises metadata-resolution output and must not call an LLM.
"""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


REPO_ROOT = Path(__file__).resolve().parents[1]
PROJECT = os.environ.get("GOOGLE_CLOUD_PROJECT", "prompt-driven-development-stg2")
MODEL = os.environ.get("PDD_MODEL_DEFAULT", "vertex_ai/gemini-3.5-flash")


def write_fixture(root: Path, *, broken_metadata: bool = False) -> None:
    prompts = root / "prompts"
    stories = root / "user_stories"
    contracts = stories / "contracts"
    prompts.mkdir(parents=True)
    contracts.mkdir(parents=True)

    (prompts / "purchase_email_python.prompt").write_text(
        """% Module: purchase email notifications
Implement email notifications for completed purchases.
Requirements:
- Send a purchase confirmation after checkout.
- Include the order number and purchased item names.
- Do not handle refunds or refund receipts.
""",
        encoding="utf-8",
    )
    (prompts / "refund_audit_python.prompt").write_text(
        """% Module: refund audit records
Implement internal audit logging for refunds.
Requirements:
- Record the refunded order identifier and refund amount.
- Do not require a reason code.
- Do not send customer email or refund receipts.
""",
        encoding="utf-8",
    )

    links = (
        "missing_python.prompt"
        if broken_metadata
        else "purchase_email_python.prompt, refund_audit_python.prompt"
    )
    (stories / "story__refund_receipts.md").write_text(
        f"""<!-- pdd-story-prompts: {links} -->

## Story

As a support agent, I can issue a refund with a required reason code and
automatically send the customer a refund receipt, so the customer has a clear
record of the refund.
""",
        encoding="utf-8",
    )
    (contracts / "refund_receipts.contract.md").write_text(
        """# Contract: Refund receipts

## Acceptance Criteria

- Refunds require a reason code before completion.
- Completing a refund sends the customer a refund receipt email.

## Oracle

- The linked prompts must explicitly cover required refund reason codes.
- The linked prompts must explicitly cover refund receipt emails.

## Non-Goals

- Purchase-confirmation behavior does not satisfy this story.
""",
        encoding="utf-8",
    )


def cli_environment(*, isolated_home: Path) -> dict[str, str]:
    env = os.environ.copy()
    adc = Path.home() / ".config" / "gcloud" / "application_default_credentials.json"
    isolated_home.mkdir(parents=True, exist_ok=True)
    env.pop("VERTEX_CREDENTIALS", None)
    env.update(
        {
            # Keep machine-level PDD catalog/config overrides out of this branch test.
            "HOME": str(isolated_home),
            "GOOGLE_CLOUD_PROJECT": PROJECT,
            "VERTEXAI_PROJECT": PROJECT,
            "VERTEXAI_LOCATION": env.get("VERTEXAI_LOCATION", "global"),
            "PDD_MODEL_DEFAULT": MODEL,
            "PDD_FORCE": "1",
            "PDD_FORCE_LOCAL": "1",
            "PYTHONPATH": os.pathsep.join(
                part for part in (str(REPO_ROOT), env.get("PYTHONPATH", "")) if part
            ),
        }
    )
    if not env.get("GOOGLE_APPLICATION_CREDENTIALS") and adc.is_file():
        env["GOOGLE_APPLICATION_CREDENTIALS"] = str(adc)
    return env


def run_cli(root: Path, *, live: bool) -> subprocess.CompletedProcess[str]:
    command = [
        sys.executable,
        "-m",
        "pdd.cli",
        "--force",
        "--strength",
        "0.5",
        "--temperature",
        "0",
        "--time",
        "0.25",
        "detect",
        "--stories",
        "--stories-dir",
        "user_stories",
        "--prompts-dir",
        "prompts",
        "--no-fail-fast",
        "--non-interactive",
    ]
    env = cli_environment(isolated_home=root / ".home")
    if not live:
        # A wholly unresolved metadata link must terminate before model selection.
        env["PDD_MODEL_DEFAULT"] = "this-model-must-never-be-invoked"
    return subprocess.run(
        command,
        cwd=root,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
        timeout=600,
    )


def assert_contains(output: str, *needles: str) -> None:
    flattened = " ".join(output.split())
    for needle in needles:
        assert needle in flattened, f"missing {needle!r} in output:\n{output}"


def validate_branch_import(env: dict[str, str], cwd: Path) -> None:
    imported = subprocess.check_output(
        [
            sys.executable,
            "-c",
            "import pathlib,pdd; print(pathlib.Path(pdd.__file__).resolve())",
        ],
        cwd=cwd,
        env=env,
        text=True,
    ).strip()
    imported_path = Path(imported)
    assert imported_path.is_relative_to(REPO_ROOT), (
        f"expected branch CLI from {REPO_ROOT}, imported {imported_path}"
    )
    print(f"Branch package: {imported_path}")


def main() -> None:
    keep = os.environ.get("PDD_KEEP_PR1875_FIXTURE") == "1"
    fixture_root = Path(tempfile.mkdtemp(prefix="pdd-pr1875-manual-"))
    try:
        validate_branch_import(
            cli_environment(isolated_home=fixture_root / ".import-home"), fixture_root
        )

        semantic = fixture_root / "semantic-failure"
        write_fixture(semantic)
        result = run_cli(semantic, live=True)
        print("\n=== Live semantic-failure CLI output ===")
        print(result.stdout)
        assert result.returncode == 1, result.stdout
        assert_contains(
            result.stdout,
            "FAIL user_stories/story__refund_receipts.md",
            "Evaluated prompts:",
            "prompts/purchase_email_python.prompt",
            "prompts/refund_audit_python.prompt",
            "Missing or stale behavior:",
            "Next step: pdd fix user_stories/story__refund_receipts.md",
        )
        explanation = " ".join(result.stdout.lower().split())
        assert "refund" in explanation
        assert "receipt" in explanation or "reason code" in explanation

        unresolved = fixture_root / "unresolved-link"
        write_fixture(unresolved, broken_metadata=True)
        result = run_cli(unresolved, live=False)
        print("\n=== Deterministic unresolved-link CLI output ===")
        print(result.stdout)
        assert result.returncode == 3, result.stdout
        assert_contains(
            result.stdout,
            "UNKNOWN user_stories/story__refund_receipts.md",
            "Evaluated prompts:",
            "- none",
            "Unresolved prompt references:",
            "missing_python.prompt",
            "repair the pdd-story-prompts metadata, then retry",
        )
        assert "Missing or stale behavior:" not in result.stdout
        assert "pdd fix" not in result.stdout

        print("\nPR #1875 manual CLI validation passed.")
    finally:
        if keep:
            print(f"Fixture retained at: {fixture_root}")
        else:
            shutil.rmtree(fixture_root)


if __name__ == "__main__":
    main()
