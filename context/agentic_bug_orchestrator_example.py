"""Runnable example for the agentic bug orchestrator (issue #964).

Mirrors the pattern used by `context/agentic_common_example.py`:
    * Insert the repo root at the FRONT of `sys.path` so the local worktree
      shadows any installed `pdd` package (the installed package may pre-date
      the PR symbols this example patches).
    * Mock every external side effect — worktree creation, state load/save,
      preprocess, subprocess (git/gh), `post_step_comment`, and the per-step
      LLM call — so the example can run hermetically with no network, no
      GitHub, and no git operations on a real working tree.
    * Use the current 12-step flow labels (`step1` .. `step12`) and emit a
      `<step_report>` block on every step so the orchestrator's
      `_maybe_post_step_comment` extracts a body to post via the (mocked)
      trusted-credentials helper.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

PROJECT_ROOT = Path(__file__).resolve().parent.parent
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

try:
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator
except ImportError as exc:  # pragma: no cover - guidance only
    print(f"Error: Could not import 'pdd.agentic_bug_orchestrator': {exc}")
    print("Run this example from the repository root with PDD installed in editable mode.")
    sys.exit(1)


_STEP_BODIES = {
    1: "Step 1: Duplicate Check — no duplicate issues found.",
    2: "Step 2: Docs Check — behavior is not documented; treat as bug.",
    3: "Step 3: Triage — sufficient info to proceed.",
    4: "Step 4: API Research — no external API constraints.",
    5: "Step 5: Reproduce — ZeroDivisionError reproduced with input (10, 0).",
    6: "Step 6: Root Cause — `divide` lacks denominator==0 guard.",
    7: "Step 7: Prompt Classification — DEFECT_TYPE: code (code bug, not prompt defect).",
    8: "Step 8: Test Plan — add `test_divide_zero` asserting ValueError.",
    9: "Step 9: Generate — created tests/test_calculator_bug.py.",
    10: "Step 10: Verify — new test fails against current code as expected.",
    11: "Step 11: E2E — created tests/e2e/test_calculator_e2e.py.",
    12: "Step 12: PR — opened draft PR #101 linked to issue #42.",
}

_STEP_TRAILERS = {
    5: "\nREPRO_FILES_CREATED: tests/test_calculator_repro.py",
    6: (
        "\nFIX_LOCATIONS: pdd/calculator.py"
        "\nEXPANSION_ITEMS: none"
    ),
    7: "\nDEFECT_TYPE: code",
    8: "\nPLANNED_TEST_COUNT: 1",
    9: "\nFILES_CREATED: tests/test_calculator_bug.py",
    10: "\nE2E_NEEDED: no",
    11: "\nE2E_SKIP: not required (E2E_NEEDED: no)",
}


def mock_load_prompt_template(template_name: str) -> str:
    return f"MOCK PROMPT FOR: {template_name}\nContext: {{issue_content}}"


def mock_preprocess(prompt_text: str, *args, **kwargs) -> str:
    return prompt_text


def mock_run_agentic_task(*args, **kwargs):
    """Simulate one step of the orchestrator's LLM call.

    The orchestrator wraps the visible body in `<step_report>...</step_report>`;
    markers like `FILES_CREATED` stay outside that block so the orchestrator's
    downstream parsing still sees them.
    """
    label = kwargs.get("label", "")
    try:
        step_num = int(label.replace("step", ""))
    except ValueError:
        step_num = 0
    body = _STEP_BODIES.get(step_num, f"{label}: mock body")
    trailer = _STEP_TRAILERS.get(step_num, "")
    output = f"<step_report>{body}</step_report>{trailer}"
    return True, output, 0.05, "gpt-4-mock"


def mock_subprocess_run(*args, **kwargs):
    """Stub out all `git`/`gh`/`pytest` calls inside the orchestrator."""
    return subprocess.CompletedProcess(
        args=args[0] if args else [],
        returncode=0,
        stdout="",
        stderr="",
    )


def main() -> None:
    cwd = Path("/tmp/agentic_bug_orchestrator_example_cwd")
    worktree = Path("/tmp/agentic_bug_orchestrator_example_worktree")

    issue = dict(
        issue_url="https://github.com/example/calculator/issues/42",
        issue_content="Dividing by zero crashes instead of raising a clean error.",
        repo_owner="example",
        repo_name="calculator",
        issue_number=42,
        issue_author="bug_hunter_99",
        issue_title="Crash on division by zero",
        cwd=cwd,
        verbose=False,
        quiet=True,
    )

    print("Starting Agentic Bug Orchestrator simulation (fully mocked)…")
    print("-" * 60)

    # All side-effecting helpers the orchestrator calls in
    # `pdd.agentic_bug_orchestrator` are patched at the import site (where the
    # names are bound inside the module). `subprocess.run` is patched at the
    # module level too so the orchestrator's many internal git/gh calls become
    # no-ops.
    patches = [
        patch("pdd.agentic_bug_orchestrator.load_prompt_template", side_effect=mock_load_prompt_template),
        patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=mock_preprocess),
        patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task),
        patch("pdd.agentic_bug_orchestrator.post_step_comment", return_value=True),
        patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)),
        patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None),
        patch("pdd.agentic_bug_orchestrator.clear_workflow_state", return_value=None),
        patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(worktree, None)),
        patch("pdd.agentic_bug_orchestrator.clear_agentic_progress", return_value=None),
        patch("pdd.agentic_bug_orchestrator.set_agentic_progress", return_value=None),
        # `_verify_e2e_tests` ultimately invokes pytest on real files in the
        # worktree. Replace it with a no-op success so the hermetic example
        # does not error on missing test files for steps 9/11.
        patch(
            "pdd.agentic_bug_orchestrator._verify_e2e_tests",
            return_value=(True, "mocked: all tests passed"),
        ),
        patch("pdd.agentic_bug_orchestrator.subprocess.run", side_effect=mock_subprocess_run),
    ]

    try:
        for p in patches:
            p.start()
        result = run_agentic_bug_orchestrator(**issue)
    finally:
        for p in patches:
            p.stop()

    success, final_msg, total_cost, model, changed_files = result

    print("-" * 60)
    print("Simulation complete.")
    print(f"Success: {success}")
    print(f"Final Message: {final_msg}")
    print(f"Total Cost: ${total_cost:.2f}")
    print(f"Model Used: {model}")
    print(f"Changed Files: {changed_files}")


if __name__ == "__main__":
    main()
