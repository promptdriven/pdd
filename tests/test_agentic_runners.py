import os
import shutil
from pathlib import Path
from pdd.agentic_runners import sanitized_env_common, sanitized_env_openai, which_or_skip

def test_sanitized_env_common_min_keys():
    env = sanitized_env_common()
    assert env["TERM"] == "dumb"
    assert env["CI"] == "1"
    assert env["NO_COLOR"] == "1"

def test_sanitized_env_openai_flags():
    env = sanitized_env_openai()
    assert env["OPENAI_CLI_NO_TTY"] == "1"
    assert env["OPENAI_CLI_NO_COLOR"] == "1"

def test_which_or_skip_handles_missing_binary():
    # simulate a binary that won't be found
    assert which_or_skip("openai", ["totally_not_real_binary", "exec"]) is None

def test_which_or_skip_known_name_but_may_not_exist():
    # returns None or "codex" depending on the machine — both are okay
    res = which_or_skip("openai", ["codex", "exec"])
    assert res in (None, "codex")
