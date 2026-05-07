import os
import subprocess
import sys
from pathlib import Path

from pdd.generation_completion import (
    completion_check_tail,
    provider_finished_structurally,
)

PROJECT_ROOT = Path(__file__).resolve().parents[1]


def test_provider_stop_requires_structurally_complete_python():
    assert provider_finished_structurally(
        "```python\ndef add(a, b):\n    return a + b\n```\n",
        "stop",
        "python",
    )
    assert not provider_finished_structurally(
        "```python\ndef add(a, b):\n    return\n```\n",
        "length",
        "python",
    )
    assert not provider_finished_structurally(
        "```python\ndef add(a, b):\n    return (\n```\n",
        "stop",
        "python",
    )


def test_provider_completed_status_supports_responses_api():
    assert provider_finished_structurally(
        "```typescript\nexport const value = 1;\n```\n",
        "completed",
        "typescript",
    )


def test_provider_stop_with_json_requires_valid_json():
    assert provider_finished_structurally('{"ok": true}', "stop", "json")
    assert not provider_finished_structurally('{"ok": ', "stop", "json")


def test_completion_check_tail_starts_on_line_boundary_when_possible():
    text = "prefix-" + ("a" * 20) + "\nline-one\nline-two\nline-three"

    tail = completion_check_tail(text, max_chars=25)

    assert tail == "line-two\nline-three"


def test_generation_completion_example_runs_standalone_without_path_env(tmp_path):
    env = os.environ.copy()
    env.pop("PDD_PATH", None)
    env.pop("PYTHONPATH", None)

    result = subprocess.run(
        [sys.executable, str(PROJECT_ROOT / "context/generation_completion_example.py")],
        cwd=tmp_path,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )

    assert result.returncode == 0, result.stderr
    assert "Python completion valid: True" in result.stdout


def test_generation_completion_artifacts_are_clean_text():
    for relative_path in (
        "context/generation_completion_example.py",
        "pdd/prompts/generation_completion_python.prompt",
    ):
        path = PROJECT_ROOT / relative_path
        text = path.read_text(encoding="utf-8")

        assert text.endswith("\n"), f"{relative_path} must end with a newline"
        assert not any(
            line.rstrip() != line for line in text.splitlines()
        ), f"{relative_path} must not contain trailing whitespace"
