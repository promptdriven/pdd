"""
Tests for utils/mcp/pdd_mcp_server/tools/runner.py subprocess command building.

Issue #1648: run_pdd_command() uses shutil.which('pdd') to locate the executable,
which resolves to the installed site-packages binary rather than the current Python
interpreter.  The fix is to always use [sys.executable, "-m", "pdd"] for interpreter parity.

# Scope addition: covers expansion item "utils/mcp/pdd_mcp_server/tools/runner.py:
# run_pdd_command() at line 66 uses shutil.which('pdd')" identified by Step 6.
"""
from __future__ import annotations

import asyncio
import sys
from pathlib import Path
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

# Add utils/mcp to sys.path so that pdd_mcp_server is importable as a package.
# utils/mcp has no __init__.py but pdd_mcp_server/ does.
_MCP_ROOT = Path(__file__).parent.parent / "utils" / "mcp"
if str(_MCP_ROOT) not in sys.path:
    sys.path.insert(0, str(_MCP_ROOT))


# ---------------------------------------------------------------------------
# Issue #1648: run_pdd_command must use sys.executable -m pdd, not PATH pdd
# ---------------------------------------------------------------------------

class TestRunPddCommandInterpreterParity:
    """Tests that run_pdd_command() always uses the current Python interpreter.

    Issue #1648: run_pdd_command() calls shutil.which('pdd') and replaces
    cmd_list[0] with the PATH-resolved binary path, so the subprocess ends up
    executing the installed (older) binary instead of the current checkout.
    """

    @pytest.mark.asyncio
    async def test_run_pdd_command_ignores_path_pdd_binary(self):
        """Test 4: run_pdd_command uses sys.executable -m pdd, not the PATH binary.

        Simulates a developer machine where shutil.which('pdd') returns the
        installed binary /opt/anaconda3/bin/pdd (version 0.0.276) while the
        checkout is 0.0.278.dev0.

        Fails on buggy code: asyncio.create_subprocess_exec is called with
        "/opt/anaconda3/bin/pdd" as the first argument (after cmd_list[0] is
        replaced with the shutil.which result).
        """
        from pdd_mcp_server.tools.runner import run_pdd_command

        mock_process = MagicMock()
        mock_process.communicate = AsyncMock(return_value=(b"output\n", b""))
        mock_process.returncode = 0

        with patch("shutil.which", return_value="/opt/anaconda3/bin/pdd"):
            with patch("asyncio.create_subprocess_exec", new_callable=AsyncMock,
                       return_value=mock_process) as mock_exec:
                result = await run_pdd_command(["pdd", "sync", "mymodule"])

        mock_exec.assert_called_once()
        actual_args = mock_exec.call_args[0]  # positional args passed to create_subprocess_exec

        assert actual_args[0] == sys.executable, (
            f"Expected sys.executable ({sys.executable!r}) as first arg to "
            f"create_subprocess_exec, got {actual_args[0]!r}. "
            "Bug: run_pdd_command() passed the PATH binary instead of the current interpreter."
        )
        assert "-m" in actual_args, f"Expected '-m' in subprocess args, got: {actual_args}"
        assert "pdd" in actual_args, f"Expected 'pdd' in subprocess args, got: {actual_args}"
        assert "/opt/anaconda3/bin/pdd" not in actual_args, (
            f"PATH binary must not appear in subprocess args: {actual_args}"
        )


# ---------------------------------------------------------------------------
# Scope addition: covers expansion item "utils/mcp/prompts/runner_python.prompt:
# code generation spec specifies shutil.which('pdd') at lines 34 and 80 —
# regenerating runner.py from this spec would reintroduce the bug even after
# the executable code is fixed" identified by Step 6.
#
# The prompt was fixed in Step 7; these tests guard against regression (i.e.,
# if the prompt is reverted to the buggy shutil.which-first specification,
# regenerating runner.py would silently reintroduce issue #1648).
# ---------------------------------------------------------------------------

class TestRunnerPromptSpecification:
    """Verify utils/mcp/prompts/runner_python.prompt mandates interpreter parity.

    Issue #1648: The original prompt (lines 34 and 80) prescribed
    ``shutil.which('pdd')`` as the executable lookup mechanism.  If the prompt
    specification is not corrected, regenerating runner.py from it will silently
    reintroduce the bug even after the runtime code is patched.

    The corrected prompt must:
    - mandate ``[sys.executable, '-m', 'pdd']`` for subprocess invocations
    - explicitly prohibit ``shutil.which('pdd')``
    """

    _PROMPT_PATH = _MCP_ROOT / "prompts" / "runner_python.prompt"

    def _read_prompt(self) -> str:
        return self._PROMPT_PATH.read_text(encoding="utf-8")

    # Scope addition: regression guard for the prompt fix.
    def test_prompt_does_not_prescribe_shutil_which_pdd(self):
        """Prompt must not contain a prescriptive 'use shutil.which' instruction.

        Before fix (original buggy prompt at line 34):
            'Use `shutil.which('pdd')` to find the absolute path to the pdd
            executable.  If not found, log an error and raise FileNotFoundError.'

        Before fix (code example at line 80):
            'pdd_executable = shutil.which('pdd')'

        After fix: ``shutil.which`` appears only in prohibition contexts
        (e.g., 'Do NOT use shutil.which(...)').

        Fails on the original buggy prompt; passes on the corrected prompt.
        """
        content = self._read_prompt()

        prescriptive_lines = []
        for line in content.splitlines():
            if "shutil.which" not in line:
                continue
            lower_line = line.lower()
            is_prohibition = any(
                kw in lower_line
                for kw in ("not", "don't", "don\u2019t", "avoid", "must not", "do not")
            )
            if not is_prohibition:
                prescriptive_lines.append(line.strip())

        assert not prescriptive_lines, (
            "utils/mcp/prompts/runner_python.prompt still prescribes shutil.which('pdd').\n"
            "Prescriptive lines found:\n"
            + "\n".join(f"  {ln!r}" for ln in prescriptive_lines)
            + "\n\nIssue #1648: regenerating runner.py from this prompt would reintroduce "
            "the installed-binary-over-checkout bug.  The prompt must mandate "
            "[sys.executable, '-m', 'pdd'] instead."
        )

    # Scope addition: regression guard for the prompt fix.
    def test_prompt_mandates_sys_executable_parity(self):
        """Prompt must instruct generated code to use sys.executable -m pdd.

        Before fix: the prompt specified shutil.which('pdd') as the lookup.
        After fix: the prompt contains an explicit interpreter-parity instruction
        such as 'Build the subprocess command as [sys.executable, '-m', 'pdd'] + ...'

        Fails on the original buggy prompt; passes on the corrected prompt.
        """
        content = self._read_prompt()

        assert "sys.executable" in content, (
            "utils/mcp/prompts/runner_python.prompt does not mention sys.executable.\n"
            "Issue #1648: the prompt must mandate [sys.executable, '-m', 'pdd'] so that "
            "regenerated runner.py uses the calling interpreter rather than any PATH binary."
        )

        parity_phrases = (
            "sys.executable, '-m', 'pdd'",
            'sys.executable, "-m", "pdd"',
            "sys.executable + '-m'",
            "sys.executable -m pdd",
            "[sys.executable, '-m', 'pdd']",
        )
        assert any(phrase in content for phrase in parity_phrases), (
            "utils/mcp/prompts/runner_python.prompt mentions sys.executable but does not "
            "show the interpreter-parity invocation pattern.\n"
            "Expected one of:\n"
            + "\n".join(f"  {p!r}" for p in parity_phrases)
            + "\n\nIssue #1648: the prompt must include a concrete example so that "
            "regenerated code passes the same interpreter to the subprocess."
        )
