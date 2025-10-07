import os
from pathlib import Path
import types
import subprocess
import pytest

# Module under test
import pdd.agentic_fix as agentic_fix


@pytest.fixture
def pyproj(tmp_path: Path, monkeypatch):
    # Layout:
    #   src/main.py (buggy)
    #   tests/test_main.py (expects fixed behavior)
    proj = tmp_path
    (proj / "src").mkdir(parents=True, exist_ok=True)
    (proj / "tests").mkdir(parents=True, exist_ok=True)

    # buggy main.py
    (proj / "src" / "main.py").write_text(
        "from utils import get_greeting\n"
        "def create_user_greeting():\n"
        "    # wrong kw name triggers failure\n"
        "    return get_greeting(name='John', last_name='Doe')\n",
        encoding="utf-8",
    )
    # correct utils.py signature
    (proj / "src" / "utils.py").write_text(
        "def get_greeting(first_name: str, last_name: str) -> str:\n"
        "    return f'Hello, {first_name} {last_name}!'\n",
        encoding="utf-8",
    )
    # unit test focuses only on importability and call success
    (proj / "tests" / "test_main.py").write_text(
        "from src.main import create_user_greeting\n"
        "def test_runs():\n"
        "    assert 'John Doe' in create_user_greeting()\n",
        encoding="utf-8",
    )

    # minimal error log and prompt
    (proj / "error.log").write_text("", encoding="utf-8")
    (proj / "prompt.txt").write_text("Create function; import utils.get_greeting", encoding="utf-8")

    monkeypatch.chdir(proj)
    return {
        "prompt": str(proj / "prompt.txt"),
        "code": str(proj / "src" / "main.py"),
        "test": str(proj / "tests" / "test_main.py"),
        "errlog": str(proj / "error.log"),
        "proj": proj,
    }


def _completed(stdout="", stderr="", returncode=0):
    # Helper: mimic subprocess.CompletedProcess
    cp = types.SimpleNamespace()
    cp.stdout = stdout
    cp.stderr = stderr
    cp.returncode = returncode
    return cp


def _fixed_main_py():
    return (
        "from utils import get_greeting\n"
        "def create_user_greeting():\n"
        "    return get_greeting(first_name='John', last_name='Doe')\n"
    )


def test_gemini_harvest_code_fence_applies_and_verifies(pyproj, monkeypatch):
    # Simulate Gemini returning a python fenced block (no markers)
    def fake_google_variants(prompt_text, cwd, total_timeout, label):
        return _completed(stdout=f"```python\n{_fixed_main_py()}\n```")

    # Force verify to True and make it pass (simulate pytest OK)
    def fake_verify(unit_test_file, cwd, verify_cmd=None, enabled=True):
        return True

    # Disable Anthropic/OpenAI, only google path taken
    monkeypatch.setenv("GEMINI_API_KEY", "x")
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)

    # Inject fakes
    monkeypatch.setattr(agentic_fix, "_run_google_variants", fake_google_variants)
    monkeypatch.setattr(agentic_fix, "_verify_and_log", fake_verify)

    ok, msg, cost, model = agentic_fix.run_agentic_fix(
        pyproj["prompt"], pyproj["code"], pyproj["test"], pyproj["errlog"]
    )

    assert ok is True
    assert "agentic-google" in model
    assert Path(pyproj["code"]).read_text(encoding="utf-8") == _fixed_main_py()


def test_openai_harvest_markers_single_file_applies(pyproj, monkeypatch):
    code_path = Path(pyproj["code"]).resolve()
    begin = f"<<<BEGIN_FILE:{code_path}>>>"
    end = f"<<<END_FILE:{code_path}>>>"

    def fake_openai_variants(prompt_text, cwd, total_timeout, label):
        # Return correct content inside our markers
        return _completed(stdout=f"{begin}\n{_fixed_main_py()}\n{end}\n")

    def fake_verify(unit_test_file, cwd, verify_cmd=None, enabled=True):
        return True

    # Enable openai only
    monkeypatch.setenv("OPENAI_API_KEY", "x")
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)

    monkeypatch.setattr(agentic_fix, "_run_openai_variants", fake_openai_variants)
    monkeypatch.setattr(agentic_fix, "_verify_and_log", fake_verify)

    ok, msg, cost, model = agentic_fix.run_agentic_fix(
        pyproj["prompt"], pyproj["code"], pyproj["test"], pyproj["errlog"]
    )

    assert ok is True
    assert "agentic-openai" in model
    assert Path(pyproj["code"]).read_text(encoding="utf-8") == _fixed_main_py()


def test_openai_primary_after_harvest_miss(pyproj, monkeypatch):
    code_path = Path(pyproj["code"]).resolve()
    begin = f"<<<BEGIN_FILE:{code_path}>>>"
    end = f"<<<END_FILE:{code_path}>>>"

    # First (harvest) returns nothing usable; second (primary) returns markers
    harvest_calls = {"n": 0}
    primary_calls = {"n": 0}

    def fake_openai_variants(prompt_text, cwd, total_timeout, label):
        if label == "harvest":
            harvest_calls["n"] += 1
            return _completed(stdout="(no markers here)")
        else:
            primary_calls["n"] += 1
            return _completed(stdout=f"{begin}\n{_fixed_main_py()}\n{end}\n")

    def fake_verify(unit_test_file, cwd, verify_cmd=None, enabled=True):
        return True

    monkeypatch.setenv("OPENAI_API_KEY", "x")
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)

    monkeypatch.setattr(agentic_fix, "_run_openai_variants", fake_openai_variants)
    monkeypatch.setattr(agentic_fix, "_verify_and_log", fake_verify)

    ok, msg, cost, model = agentic_fix.run_agentic_fix(
        pyproj["prompt"], pyproj["code"], pyproj["test"], pyproj["errlog"]
    )

    assert ok is True
    assert harvest_calls["n"] >= 1
    assert primary_calls["n"] >= 1
    assert Path(pyproj["code"]).read_text(encoding="utf-8") == _fixed_main_py()


def test_gemini_timeout_then_next_provider(pyproj, monkeypatch):
    # Simulate gemini timing out; OpenAI succeeds via markers
    code_path = Path(pyproj["code"]).resolve()
    begin = f"<<<BEGIN_FILE:{code_path}>>>"
    end = f"<<<END_FILE:{code_path}>>>"

    def fake_google_variants(prompt_text, cwd, total_timeout, label):
        raise subprocess.TimeoutExpired(cmd="gemini -p", timeout=total_timeout)

    def fake_openai_variants(prompt_text, cwd, total_timeout, label):
        return _completed(stdout=f"{begin}\n{_fixed_main_py()}\n{end}\n")

    def fake_verify(unit_test_file, cwd, verify_cmd=None, enabled=True):
        return True

    # Make both keys present so both providers are considered
    monkeypatch.setenv("GEMINI_API_KEY", "x")
    monkeypatch.setenv("OPENAI_API_KEY", "y")
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

    monkeypatch.setattr(agentic_fix, "_run_google_variants", fake_google_variants)
    monkeypatch.setattr(agentic_fix, "_run_openai_variants", fake_openai_variants)
    monkeypatch.setattr(agentic_fix, "_verify_and_log", fake_verify)

    ok, msg, cost, model = agentic_fix.run_agentic_fix(
        pyproj["prompt"], pyproj["code"], pyproj["test"], pyproj["errlog"]
    )

    assert ok is True
    assert "agentic-openai" in model
    assert Path(pyproj["code"]).read_text(encoding="utf-8") == _fixed_main_py()


def test_verify_must_pass_to_succeed(pyproj, monkeypatch):
    # Agent returns corrected content, but we force verify to fail => overall False
    code_path = Path(pyproj["code"]).resolve()
    begin = f"<<<BEGIN_FILE:{code_path}>>>"
    end = f"<<<END_FILE:{code_path}>>>"

    def fake_openai_variants(prompt_text, cwd, total_timeout, label):
        return _completed(stdout=f"{begin}\n{_fixed_main_py()}\n{end}\n")

    def fake_verify(unit_test_file, cwd, verify_cmd=None, enabled=True):
        return False

    monkeypatch.setenv("OPENAI_API_KEY", "x")
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)

    monkeypatch.setattr(agentic_fix, "_run_openai_variants", fake_openai_variants)
    monkeypatch.setattr(agentic_fix, "_verify_and_log", fake_verify)

    ok, msg, cost, model = agentic_fix.run_agentic_fix(
        pyproj["prompt"], pyproj["code"], pyproj["test"], pyproj["errlog"]
    )

    assert ok is False
    # Also ensure the file still got written (we applied patch), but success gated by verify
    assert Path(pyproj["code"]).read_text(encoding="utf-8") == _fixed_main_py()
