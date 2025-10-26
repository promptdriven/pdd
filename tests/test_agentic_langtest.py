import json
import os
from pathlib import Path
import shutil
import pytest

# Module under test
from pdd.agentic_langtest import (
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


# ---------- default_verify_cmd_for (pure strings, tool presence mocked) ----------

def test_default_verify_cmd_for_python_returns_none_or_pytest(tmp_path):
    # For Python, module typically relies on pytest default when cmd is None.
    # Accept either None or a command that includes 'pytest'.
    test_file = tmp_path / "tests" / "test_something.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text("def test_ok(): assert True\n", encoding="utf-8")

    cmd = default_verify_cmd_for("python", str(test_file))
    if cmd is not None:
        assert "pytest" in cmd


def test_default_verify_cmd_for_java_builds_command(tmp_path, monkeypatch):
    # project skeleton
    (tmp_path / "pom.xml").write_text("<project></project>", encoding="utf-8")
    (tmp_path / "src/main/java").mkdir(parents=True, exist_ok=True)
    (tmp_path / "src/test/java").mkdir(parents=True, exist_ok=True)

    # Pretend mvn exists
    _fake_which_map(monkeypatch, {"mvn": "/usr/bin/mvn"})

    cmd = default_verify_cmd_for("java", str(tmp_path / "src/test/java/TestMain.java"))
    assert  "mvn test" in cmd


def test_default_verify_cmd_for_typescript_prefers_npm_or_npx(tmp_path, monkeypatch):
    # minimal package.json to signal a node project
    pkg = {"name": "demo", "version": "0.0.0", "scripts": {"test": "echo ok"}}
    (tmp_path / "package.json").write_text(json.dumps(pkg), encoding="utf-8")
    (tmp_path / "tests").mkdir()
    (tmp_path / "tests" / "sum.test.ts").write_text("test('x', ()=>{})", encoding="utf-8")

    # Node toolchain present; TypeScript runner often 'npm test' or 'npx' with a test runner
    _fake_which_map(monkeypatch, {"node": "/usr/bin/node", "npm": "/usr/bin/npm", "npx": "/usr/bin/npx", "tsc": "/usr/bin/tsc"})

    cmd = default_verify_cmd_for("typescript", str(tmp_path / "tests" / "sum.test.ts"))
    assert isinstance(cmd, str)
    assert ("npm" in cmd) or ("npx" in cmd)


def test_default_verify_cmd_for_javascript_uses_npm_or_npx(tmp_path, monkeypatch):
    (tmp_path / "package.json").write_text(json.dumps({"name": "demo", "version": "0.0.0"}), encoding="utf-8")
    (tmp_path / "tests").mkdir()
    (tmp_path / "tests" / "sum.test.js").write_text("test('x', ()=>{})", encoding="utf-8")

    _fake_which_map(monkeypatch, {"node": "/usr/bin/node", "npm": "/usr/bin/npm", "npx": "/usr/bin/npx"})

    cmd = default_verify_cmd_for("javascript", str(tmp_path / "tests" / "sum.test.js"))
    assert isinstance(cmd, str)
    assert ("npm" in cmd) or ("npx" in cmd)





# ---------- missing_tool_hints ----------

def test_missing_tool_hints_java_when_tools_absent(tmp_path, monkeypatch):
    (tmp_path / "pom.xml").write_text("<project></project>", encoding="utf-8")
    (tmp_path / "src").mkdir(exist_ok=True)
    (tmp_path / "src" / "Main.java").write_text("class Main {}", encoding="utf-8")
    (tmp_path / "tests").mkdir(exist_ok=True)
    (tmp_path / "tests" / "TestMain.java").write_text("class TestMain {}", encoding="utf-8")

    # No javac/java available
    _fake_which_map(monkeypatch, {"javac": None, "java": None})
    cmd = default_verify_cmd_for("java", str(tmp_path / "tests" / "TestMain.java"))
    hint = missing_tool_hints("java", cmd, tmp_path)
    # Should guide user how to install JDK / junit console
    assert isinstance(hint, str) and hint.strip()
    assert ("java" in hint.lower()) or ("jdk" in hint.lower())


def test_missing_tool_hints_js_when_node_absent(tmp_path, monkeypatch):
    (tmp_path / "package.json").write_text(json.dumps({"name": "x"}), encoding="utf-8")
    _fake_which_map(monkeypatch, {"node": None, "npm": None, "npx": None})
    cmd = default_verify_cmd_for("javascript", "tests/sum.test.js")
    hint = missing_tool_hints("javascript", cmd, tmp_path)
    assert isinstance(hint, str) and hint.strip()
    assert "node" in hint.lower() or "npm" in hint.lower()


