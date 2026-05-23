"""Runnable example for ``pdd.setup_tool``.

Demonstrates the public ``run_setup()`` entry point with all external
boundaries mocked so the example runs to completion non-interactively.

What you see when you run this example:

  - The PDD ASCII banner (tagline + positioning).
  - Phase 1 banner ("Agentic CLI Bootstrap") + a fake CLI detection result
    that triggers no warning (api_key_configured=True, OAuth absent).
  - Phase 2:
      Step 1 -> finds ANTHROPIC_API_KEY in the shell environment
      Step 2 -> writes a single Anthropic row to the user CSV under
                a temporary HOME, .pddrc is pre-created so no prompt fires
      Step 3 -> "responded OK" via a fake model tester
  - Post-success "Press Enter" defaults to "" (finish) so the options menu
    is skipped.
  - Exit summary writes ``PDD-SETUP-SUMMARY.txt`` and
    ``success_python.prompt`` into the temporary project directory.
"""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

# Make the local pdd package importable regardless of working directory.
_THIS_DIR = os.path.dirname(__file__)
sys.path.insert(0, os.path.join(_THIS_DIR, ".."))

from pdd import setup_tool  # noqa: E402


def _write_ref_csv(path: Path) -> None:
    """Write a tiny reference llm_model.csv with one Anthropic row."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "provider,model,input,output,coding_arena_elo,base_url,api_key,"
        "max_reasoning_tokens,structured_output,reasoning_type,location\n"
        "Anthropic,claude-sonnet-demo,3,15,1200,,ANTHROPIC_API_KEY,,,,\n",
        encoding="utf-8",
    )


def main() -> int:
    """Run ``setup_tool.run_setup()`` end-to-end with everything mocked.

    Returns:
        Exit code 0 on success.
    """
    workdir = tempfile.mkdtemp(prefix="pdd_setup_demo_")
    home_dir = Path(workdir) / "home"
    pdd_dir = home_dir / ".pdd"
    pdd_dir.mkdir(parents=True, exist_ok=True)
    project_dir = Path(workdir) / "project"
    project_dir.mkdir(parents=True, exist_ok=True)
    (project_dir / ".pddrc").write_text("version: '1.0'\n", encoding="utf-8")

    fake_pdd_dir = Path(workdir) / "fake_pdd"
    fake_pdd_dir.mkdir(parents=True, exist_ok=True)
    _write_ref_csv(fake_pdd_dir / "data" / "llm_model.csv")

    fake_cli_result = SimpleNamespace(
        cli_name="claude",
        provider="anthropic",
        cli_path="/usr/local/bin/claude",
        api_key_configured=True,
        skipped=False,
    )

    fake_test_result = {
        "success": True,
        "duration_s": 0.3,
        "cost": 0.0,
        "error": None,
        "tokens": {"input": 10, "output": 20},
    }

    # Input sequence:
    #   1) Enter — continue from step 1 to step 2
    #   2) Enter — continue from step 2 to step 3
    #   3) Enter — post-success "press Enter to finish" (no menu)
    inputs = iter(["", "", ""])

    def fake_input(prompt: str = "") -> str:
        sys.stdout.write(prompt)
        sys.stdout.write("\n")
        try:
            return next(inputs)
        except StopIteration:
            return ""

    original_cwd = os.getcwd()
    original_home = os.path.expanduser("~")
    try:
        os.chdir(project_dir)
        os.environ["HOME"] = str(home_dir)
        os.environ["SHELL"] = "/bin/bash"
        os.environ["ANTHROPIC_API_KEY"] = "sk-demo-key"

        with mock.patch.object(Path, "home", staticmethod(lambda: home_dir)), \
                mock.patch.object(setup_tool, "__file__",
                                  str(fake_pdd_dir / "setup_tool.py")), \
                mock.patch("pdd.cli_detector.detect_and_bootstrap_cli",
                           return_value=[fake_cli_result]), \
                mock.patch("pdd.cli_detector._has_provider_oauth",
                           return_value=False), \
                mock.patch("pdd.provider_manager._get_user_csv_path",
                           lambda: pdd_dir / "llm_model.csv"), \
                mock.patch("pdd.provider_manager._get_shell_rc_path",
                           lambda: None), \
                mock.patch("pdd.model_tester._run_test",
                           return_value=fake_test_result), \
                mock.patch("builtins.input", side_effect=fake_input):
            setup_tool.run_setup()
    finally:
        os.chdir(original_cwd)
        os.environ["HOME"] = original_home
        os.environ.pop("ANTHROPIC_API_KEY", None)

    print()
    print("=" * 60)
    print("Demo complete.")
    print(f"Temporary project dir: {project_dir}")
    print(f"  Summary file: {(project_dir / 'PDD-SETUP-SUMMARY.txt').exists()}")
    print(f"  Sample prompt: {(project_dir / 'success_python.prompt').exists()}")
    print("=" * 60)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
