import os

from pdd.preprocess import preprocess


def test_shell_command_timeout(tmp_path, monkeypatch):
    """
    Regression test for issue #592.

    A <shell> tag that runs a long command should not hang preprocess forever.
    Instead, it should time out based on PDD_SHELL_TIMEOUT and surface
    a clear timeout message in the output.
    """
    # Force a very short timeout so the test runs quickly.
    monkeypatch.setenv("PDD_SHELL_TIMEOUT", "1")

    prompt = "Test prompt\n<shell>sleep 5</shell>\n"

    output = preprocess(prompt, recursive=False, double_curly_brackets=False)

    assert "Command 'sleep 5' timed out after 1 seconds." in output

