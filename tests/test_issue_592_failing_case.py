import subprocess
from unittest.mock import patch

from pdd.preprocess import preprocess


def test_shell_command_timeout(monkeypatch):
    """
    Regression test for issue #592.

    A <shell> tag that times out should be replaced with a clear timeout message
    and preprocess should not hang. Uses a mock so the test is deterministic
    and cross-platform (no real sleep/shell).
    """
    monkeypatch.setenv("PDD_SHELL_TIMEOUT", "1")

    with patch("pdd.preprocess.subprocess.run") as mock_run:
        mock_run.side_effect = subprocess.TimeoutExpired(cmd="sleep 5", timeout=1)

        prompt = "Test prompt\n<shell>sleep 5</shell>\n"
        output = preprocess(prompt, recursive=False, double_curly_brackets=False)

    assert "Command 'sleep 5' timed out after 1 seconds." in output
    assert mock_run.call_count == 1
    _, kwargs = mock_run.call_args
    assert kwargs.get("timeout") == 1

