"""
E2E Test for Issue #493: pdd update --output crashes with NameError when
code file is in a subdirectory.

This test exercises the full update_main() → resolve_prompt_code_pair() path
that a user triggers via `pdd update <code_file> --output <path>`. It mocks
only the LLM call (update_prompt) and agent availability at the system boundary,
but exercises all real path resolution logic including .pddrc context detection,
git repo discovery, and subdirectory structure preservation.

Bug: resolve_prompt_code_pair() defines context_config only in the else branch
(when --output is NOT provided) but references it unconditionally at line 91.
When --output IS provided and the code file is in a subdirectory (rel_dir != "."),
this causes an UnboundLocalError.
"""

import os
import pytest
import git
import click
from pathlib import Path
from unittest.mock import patch

from pdd.update_main import update_main


def test_e2e_update_output_flag_with_subdirectory_code_file(tmp_path, monkeypatch):
    """
    E2E regression test: `pdd update backend/src/module.py --output /tmp/output/`
    should NOT crash with NameError when the code file is in a subdirectory.

    Exercises: update_main → resolve_prompt_code_pair → path resolution with --output.
    Mocks: LLM call (update_prompt), agent availability (get_available_agents).
    """
    # Setup: realistic repo structure matching the issue reproduction
    repo_path = tmp_path / "pdd-test"
    repo_path.mkdir()
    sub_dir = repo_path / "backend" / "src"
    sub_dir.mkdir(parents=True)
    code_file = sub_dir / "module.py"
    code_file.write_text("def hello(): return 'world'")

    output_dir = tmp_path / "output"
    output_dir.mkdir()

    # Initialize git repo (required for repo root detection)
    repo = git.Repo.init(repo_path)
    repo.index.add([str(code_file)])
    repo.index.commit("init")

    monkeypatch.chdir(repo_path)

    # Build a real Click context like the CLI would
    ctx = click.Context(click.Command("update"))
    ctx.obj = {
        "strength": 0.5,
        "temperature": 0.0,
        "verbose": False,
        "quiet": True,
    }

    with patch("pdd.update_main.update_prompt") as mock_up, \
         patch("pdd.update_main.get_available_agents", return_value=[]), \
         patch("pdd.update_main.get_language", return_value="python"):

        mock_up.return_value = ("generated prompt content", 0.01, "mock-model")

        # Act: This is what `pdd update backend/src/module.py --output /tmp/output/` does
        result = update_main(
            ctx=ctx,
            input_prompt_file=None,
            modified_code_file=str(code_file),
            input_code_file=None,
            output=str(output_dir),
            use_git=False,
        )

    # Assert: should succeed, not crash with NameError
    assert result is not None, "update_main returned None, indicating a crash or error"
    assert result[0] == "generated prompt content"

    # The prompt file should exist somewhere under the output directory
    prompt_files = list(output_dir.rglob("*_python.prompt"))
    assert len(prompt_files) >= 1, f"No prompt file created in {output_dir}"
