import json
import os
from pathlib import Path
import shutil
import pytest

# Module under test
from pdd.agentic_langtest import (
    detect_language,
    default_verify_cmd_for,
    missing_tool_hints,
)

# ---------- helpers ----------

def _fake_which_map(monkeypatch, mapping):
    """
    mapping: dict[name -> path or None]; if name not in mapping, return None.
    """
    def _fake_which(name):
        return mapping.get(name)
    monkeypatch.setattr(shutil, "which", _fake_which)


# ---------- detect_language ----------

@pytest.mark.parametrize(
    "ext,expected",
    [
        (".py", "python"),
        (".ts", "typescript"),
        (".tsx", "typescript"),
        (".js", "javascript"),
        (".mjs", "javascript"),
        (".cjs", "javascript"),
        (".java", "java"),
        (".kt", "kotlin"),           # if your implementation maps it; else adjust/remove
        (".cpp", "cpp"),
        (".cc", "cpp"),
        (".cxx", "cpp"),
        (".hpp", "cpp"),
    ],
)
def test_detect_language_basic(ext, expected):
    # detect_language should be tolerant to case
    assert detect_language(ext) == expected
    assert detect_language(ext.upper()) == expected


# ---------- default_verify_cmd_for (pure strings, tool presence mocked) ----------

def test_default_verify_cmd_for_python_returns_none_or_pytest(tmp_path):
    # For Python, module typically relies on pytest default when cmd is None.
    # Accept either None or a command that includes 'pytest'.
    test_file = tmp_path / "tests" / "test_something.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text("def test_ok(): assert True\n", encoding="utf-8")

    cmd = default_verify_cmd_for("python", tmp_path, str(test_file))
    if cmd is not None:
        assert "pytest" in cmd


def test_default_verify_cmd_for_java_builds_command(tmp_path, monkeypatch):
    # project skeleton
    (tmp_path / "src").mkdir()
    (tmp_path / "tests").mkdir()
    (tmp_path / "src" / "Main.java").write_text("class Main {}", encoding="utf-8")
    (tmp_path / "tests" / "TestMain.java").write_text("class TestMain {}", encoding="utf-8")

    # Pretend javac/java exist; junit jar may be downloaded/assumed by the command
    _fake_which_map(monkeypatch, {"javac": "/usr/bin/javac", "java": "/usr/bin/java"})

    cmd = default_verify_cmd_for("java", tmp_path, str(tmp_path / "tests" / "TestMain.java"))
    assert isinstance(cmd, str)
    assert "javac" in cmd
    # many implementations reference either ConsoleLauncher or a standalone jar:
    assert ("ConsoleLauncher" in cmd) or ("junit-platform-console-standalone" in cmd) or ("-jar" in cmd)


def test_default_verify_cmd_for_typescript_prefers_npm_or_npx(tmp_path, monkeypatch):
    # minimal package.json to signal a node project
    pkg = {"name": "demo", "version": "0.0.0", "scripts": {"test": "echo ok"}}
    (tmp_path / "package.json").write_text(json.dumps(pkg), encoding="utf-8")
    (tmp_path / "tests").mkdir()
    (tmp_path / "tests" / "sum.test.ts").write_text("test('x', ()=>{})", encoding="utf-8")

    # Node toolchain present; TypeScript runner often 'npm test' or 'npx' with a test runner
    _fake_which_map(monkeypatch, {"node": "/usr/bin/node", "npm": "/usr/bin/npm", "npx": "/usr/bin/npx", "tsc": "/usr/bin/tsc"})

    cmd = default_verify_cmd_for("typescript", tmp_path, str(tmp_path / "tests" / "sum.test.ts"))
    assert isinstance(cmd, str)
    assert ("npm" in cmd) or ("npx" in cmd)


def test_default_verify_cmd_for_javascript_uses_npm_or_npx(tmp_path, monkeypatch):
    (tmp_path / "package.json").write_text(json.dumps({"name": "demo", "version": "0.0.0"}), encoding="utf-8")
    (tmp_path / "tests").mkdir()
    (tmp_path / "tests" / "sum.test.js").write_text("test('x', ()=>{})", encoding="utf-8")

    _fake_which_map(monkeypatch, {"node": "/usr/bin/node", "npm": "/usr/bin/npm", "npx": "/usr/bin/npx"})

    cmd = default_verify_cmd_for("javascript", tmp_path, str(tmp_path / "tests" / "sum.test.js"))
    assert isinstance(cmd, str)
    assert ("npm" in cmd) or ("npx" in cmd)


@pytest.mark.parametrize("compiler", ["g++", "clang++"])
def test_default_verify_cmd_for_cpp_contains_compiler(tmp_path, monkeypatch, compiler):
    (tmp_path / "src").mkdir()
    (tmp_path / "tests").mkdir()
    (tmp_path / "src" / "main.cpp").write_text("int main(){return 0;}", encoding="utf-8")
    (tmp_path / "tests" / "test_main.cpp").write_text("// pretend test", encoding="utf-8")

    # one compiler present, the other absent
    which_map = {compiler: f"/usr/bin/{compiler}"}
    _fake_which_map(monkeypatch, which_map)

    cmd = default_verify_cmd_for("cpp", tmp_path, str(tmp_path / "tests" / "test_main.cpp"))
    assert isinstance(cmd, str)
    assert compiler in cmd


# ---------- missing_tool_hints ----------

def test_missing_tool_hints_java_when_tools_absent(tmp_path, monkeypatch):
    (tmp_path / "src").mkdir(exist_ok=True)
    (tmp_path / "src" / "Main.java").write_text("class Main {}", encoding="utf-8")
    (tmp_path / "tests").mkdir(exist_ok=True)
    (tmp_path / "tests" / "TestMain.java").write_text("class TestMain {}", encoding="utf-8")

    # No javac/java available
    _fake_which_map(monkeypatch, {"javac": None, "java": None})
    cmd = default_verify_cmd_for("java", tmp_path, str(tmp_path / "tests" / "TestMain.java"))
    hint = missing_tool_hints("java", cmd, tmp_path)
    # Should guide user how to install JDK / junit console
    assert isinstance(hint, str) and hint.strip()
    assert ("java" in hint.lower()) or ("jdk" in hint.lower())


def test_missing_tool_hints_js_when_node_absent(tmp_path, monkeypatch):
    (tmp_path / "package.json").write_text(json.dumps({"name": "x"}), encoding="utf-8")
    _fake_which_map(monkeypatch, {"node": None, "npm": None, "npx": None})
    cmd = default_verify_cmd_for("javascript", tmp_path, "tests/sum.test.js")
    hint = missing_tool_hints("javascript", cmd, tmp_path)
    assert isinstance(hint, str) and hint.strip()
    assert "node" in hint.lower() or "npm" in hint.lower()


def test_missing_tool_hints_cpp_when_compiler_absent(tmp_path, monkeypatch):
    _fake_which_map(monkeypatch, {"g++": None, "clang++": None})
    cmd = default_verify_cmd_for("cpp", tmp_path, "tests/test_main.cpp")
    hint = missing_tool_hints("cpp", cmd, tmp_path)
    assert isinstance(hint, str) and hint.strip()
    assert ("g++" in hint.lower()) or ("clang++" in hint.lower())
