import json
import os
from pathlib import Path
import shutil
import pytest

# Module under test
from pdd.agentic_langtest import (
    default_verify_cmd_for,
    missing_tool_hints,
    _find_project_root,
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

    # Set CWD to tmp_path so _find_project_root can search within it
    monkeypatch.setattr(os, "getcwd", lambda: str(tmp_path))

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

    # Set CWD to tmp_path so _find_project_root can search within it
    monkeypatch.setattr(os, "getcwd", lambda: str(tmp_path))

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


# ---------- _find_project_root boundary tests ----------

def test_find_project_root_does_not_escape_to_parent_package_json(tmp_path):
    """
    Regression test: _find_project_root() should not escape to a parent directory's
    package.json when the test file is in a nested subdirectory without its own package.json.

    This bug caused sync regression tests to run `npm test` in the wrong directory
    (the parent pdd_cloud project instead of the regression test directory), hanging
    the test suite for hours.

    Directory structure:
        tmp_path/
            package.json  <-- parent project (should NOT be found)
            subproject/
                staging/
                    regression_test/
                        test_calculator.js  <-- test file here

    Expected: _find_project_root should return regression_test/ or staging/,
              NOT tmp_path/ (the parent with package.json)
    """
    # Create parent project with package.json (simulates pdd_cloud)
    parent_pkg = {"name": "parent-project", "version": "1.0.0", "scripts": {"test": "jest"}}
    (tmp_path / "package.json").write_text(json.dumps(parent_pkg), encoding="utf-8")

    # Create nested regression test directory WITHOUT package.json
    regression_dir = tmp_path / "subproject" / "staging" / "regression_test"
    regression_dir.mkdir(parents=True, exist_ok=True)

    # Create test file in the regression directory
    test_file = regression_dir / "test_calculator.js"
    test_file.write_text("// test file\ntest('add', () => expect(1+1).toBe(2));", encoding="utf-8")

    # Call _find_project_root with the test file path
    found_root = _find_project_root(str(test_file))

    # BUG: Currently _find_project_root walks up and finds tmp_path/package.json
    # This assertion will FAIL with the current buggy implementation
    assert found_root != tmp_path, (
        f"_find_project_root() escaped to parent directory {tmp_path} which has package.json. "
        f"This causes 'npm test' to run in the wrong project! "
        f"Expected to stay within {regression_dir} or return the test file's directory."
    )


def test_find_project_root_uses_local_package_json_when_present(tmp_path):
    """
    When the test file's directory (or a close ancestor) has its own package.json,
    _find_project_root should return that directory, not a more distant parent.
    """
    # Create parent project with package.json
    parent_pkg = {"name": "parent-project", "version": "1.0.0"}
    (tmp_path / "package.json").write_text(json.dumps(parent_pkg), encoding="utf-8")

    # Create nested project with its OWN package.json
    nested_project = tmp_path / "nested" / "project"
    nested_project.mkdir(parents=True, exist_ok=True)
    nested_pkg = {"name": "nested-project", "version": "1.0.0"}
    (nested_project / "package.json").write_text(json.dumps(nested_pkg), encoding="utf-8")

    # Create test file in nested project
    test_file = nested_project / "tests" / "test_something.js"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text("// test", encoding="utf-8")

    # Should find the nested project's package.json, not the parent's
    # Pass tmp_path as boundary to allow searching within the test structure
    found_root = _find_project_root(str(test_file), boundary=tmp_path)

    assert found_root == nested_project, (
        f"Expected to find {nested_project} but got {found_root}. "
        f"_find_project_root should use the closest package.json."
    )


def test_default_verify_cmd_does_not_escape_to_parent_project(tmp_path, monkeypatch):
    """
    Integration test: default_verify_cmd_for() should not generate a command
    that runs npm test in a parent project directory.

    This is the end-to-end manifestation of the _find_project_root bug.
    """
    # Create parent project with package.json
    parent_pkg = {"name": "parent-project", "scripts": {"test": "jest --all"}}
    (tmp_path / "package.json").write_text(json.dumps(parent_pkg), encoding="utf-8")

    # Create nested regression directory WITHOUT package.json
    regression_dir = tmp_path / "pdd" / "staging" / "sync_regression_case_4"
    regression_dir.mkdir(parents=True, exist_ok=True)

    test_file = regression_dir / "test_calculator.js"
    test_file.write_text("test('x', () => {});", encoding="utf-8")

    _fake_which_map(monkeypatch, {"node": "/usr/bin/node", "npm": "/usr/bin/npm"})

    cmd = default_verify_cmd_for("javascript", str(test_file))

    # The command should NOT cd to tmp_path (the parent project with package.json)
    # It should cd to the regression_dir or test file's directory instead
    # Check for exact cd target - the parent should not be the cd destination
    import re
    cd_match = re.search(r'cd "([^"]+)"', cmd)
    assert cd_match, f"Could not find cd command in: {cmd}"
    cd_target = cd_match.group(1)

    # The cd target should NOT be the parent directory (which has package.json)
    assert cd_target != str(tmp_path), (
        f"Generated command cd's to parent project directory!\n"
        f"cd target: {cd_target}\n"
        f"Parent (should not be target): {tmp_path}\n"
        f"This causes npm test to run in the wrong project."
    )

    # Additionally verify it's going somewhere within the regression structure
    assert str(regression_dir) in cd_target or cd_target == str(regression_dir), (
        f"cd target should be within or equal to regression_dir.\n"
        f"cd target: {cd_target}\n"
        f"regression_dir: {regression_dir}"
    )


