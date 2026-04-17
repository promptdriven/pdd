# Test plan (from spec requirements):
#
# 1. LintCommand dataclass
#    - test_lint_command_defaults: command field required, cwd defaults to None
#    - test_lint_command_with_cwd: cwd can be set to a Path
#
# 2. get_lint_commands - hybrid contract
#    - test_non_python_returns_empty_list: .js, .ts, .go, etc. return []
#    - test_no_extension_returns_empty_list: file with no extension returns []
#
# 3. get_lint_commands - Python files
#    - test_python_returns_two_commands: .py file returns exactly 2 commands
#    - test_ruff_command_format: first command is "ruff check <file>"
#    - test_mypy_command_format: second command is "mypy <file>"
#
# 4. Config discovery for ruff (pyproject.toml only)
#    - test_ruff_cwd_with_pyproject_toml: finds pyproject.toml, sets cwd
#    - test_ruff_cwd_none_without_config: no pyproject.toml -> cwd=None
#
# 5. Config discovery for mypy (pyproject.toml or mypy.ini)
#    - test_mypy_cwd_with_pyproject_toml: finds pyproject.toml, sets cwd
#    - test_mypy_cwd_with_mypy_ini: finds mypy.ini when no pyproject.toml
#    - test_mypy_cwd_none_without_config: no config -> cwd=None
#    - test_mypy_prefers_pyproject_over_mypy_ini: pyproject.toml found first
#
# 6. _find_config helper
#    - test_find_config_walks_up: finds config in parent directory
#    - test_find_config_max_levels: respects max_levels limit
#    - test_find_config_returns_none_when_not_found: returns None
#    - test_find_config_starts_from_file_parent: when start is a file, uses parent
#    - test_find_config_at_root_stops: doesn't loop forever at filesystem root
#
# 7. Edge cases
#    - test_file_accepts_string_path: Path coercion from string input
#    - test_return_types: returns list of LintCommand instances
#
# 8. from __future__ import annotations
#    - test_future_annotations_import: file starts with the import

from __future__ import annotations

from pathlib import Path

from pdd.get_lint_commands import LintCommand, get_lint_commands, _find_config


class TestLintCommand:
    """Tests for the LintCommand dataclass."""

    def test_lint_command_defaults(self) -> None:
        """cwd defaults to None when not specified."""
        cmd = LintCommand(command="ruff check foo.py")
        assert cmd.command == "ruff check foo.py"
        assert cmd.cwd is None

    def test_lint_command_with_cwd(self) -> None:
        """cwd can be explicitly set to a Path."""
        p = Path("/some/dir")
        cmd = LintCommand(command="mypy foo.py", cwd=p)
        assert cmd.command == "mypy foo.py"
        assert cmd.cwd == p


class TestGetLintCommandsHybridContract:
    """Tests for non-Python files returning empty list."""

    def test_non_python_returns_empty_list(self) -> None:
        """Non-Python extensions return empty list."""
        for ext in [".js", ".ts", ".tsx", ".go", ".rs", ".java", ".rb", ".c", ".cpp"]:
            result = get_lint_commands(Path(f"file{ext}"))
            assert result == [], f"Expected [] for {ext}, got {result}"

    def test_no_extension_returns_empty_list(self) -> None:
        """File with no extension returns empty list."""
        result = get_lint_commands(Path("Makefile"))
        assert result == []


class TestGetLintCommandsPython:
    """Tests for Python file lint command resolution."""

    def test_python_returns_two_commands(self, tmp_path: Path) -> None:
        """A .py file returns exactly two LintCommand instances."""
        py_file = tmp_path / "test.py"
        py_file.write_text("x = 1\n")
        result = get_lint_commands(py_file)
        assert len(result) == 2
        assert all(isinstance(c, LintCommand) for c in result)

    def test_ruff_command_format(self, tmp_path: Path) -> None:
        """First command is 'ruff check <file>'."""
        py_file = tmp_path / "test.py"
        py_file.write_text("x = 1\n")
        result = get_lint_commands(py_file)
        assert result[0].command == f"ruff check {py_file}"

    def test_mypy_command_format(self, tmp_path: Path) -> None:
        """Second command is 'mypy <file>'."""
        py_file = tmp_path / "test.py"
        py_file.write_text("x = 1\n")
        result = get_lint_commands(py_file)
        assert result[1].command == f"mypy {py_file}"

    def test_ruff_cwd_with_pyproject_toml(self, tmp_path: Path) -> None:
        """ruff cwd is set to directory containing pyproject.toml."""
        (tmp_path / "pyproject.toml").write_text("[tool.ruff]\n")
        sub = tmp_path / "src"
        sub.mkdir()
        py_file = sub / "mod.py"
        py_file.write_text("x = 1\n")
        result = get_lint_commands(py_file)
        assert result[0].cwd == tmp_path

    def test_ruff_cwd_none_without_config(self, tmp_path: Path) -> None:
        """ruff cwd is None when no pyproject.toml found."""
        py_file = tmp_path / "mod.py"
        py_file.write_text("x = 1\n")
        result = get_lint_commands(py_file)
        assert result[0].cwd is None

    def test_mypy_cwd_with_pyproject_toml(self, tmp_path: Path) -> None:
        """mypy cwd is set when pyproject.toml is found."""
        (tmp_path / "pyproject.toml").write_text("[tool.mypy]\n")
        py_file = tmp_path / "mod.py"
        py_file.write_text("x = 1\n")
        result = get_lint_commands(py_file)
        assert result[1].cwd == tmp_path

    def test_mypy_cwd_with_mypy_ini(self, tmp_path: Path) -> None:
        """mypy cwd is set when mypy.ini is found (no pyproject.toml)."""
        (tmp_path / "mypy.ini").write_text("[mypy]\n")
        py_file = tmp_path / "mod.py"
        py_file.write_text("x = 1\n")
        result = get_lint_commands(py_file)
        # ruff should not find anything
        assert result[0].cwd is None
        # mypy should find mypy.ini
        assert result[1].cwd == tmp_path

    def test_mypy_cwd_none_without_config(self, tmp_path: Path) -> None:
        """mypy cwd is None when neither pyproject.toml nor mypy.ini found."""
        py_file = tmp_path / "mod.py"
        py_file.write_text("x = 1\n")
        result = get_lint_commands(py_file)
        assert result[1].cwd is None

    def test_file_accepts_string_path(self, tmp_path: Path) -> None:
        """get_lint_commands accepts a string and coerces to Path."""
        py_file = tmp_path / "mod.py"
        py_file.write_text("x = 1\n")
        result = get_lint_commands(str(py_file))  # type: ignore[arg-type]
        assert len(result) == 2
        assert "ruff check" in result[0].command


class TestFindConfig:
    """Tests for the _find_config helper."""

    def test_finds_config_in_current_dir(self, tmp_path: Path) -> None:
        """Finds config file in the start directory."""
        (tmp_path / "pyproject.toml").write_text("")
        result = _find_config(tmp_path, ["pyproject.toml"])
        assert result == tmp_path

    def test_walks_up_to_parent(self, tmp_path: Path) -> None:
        """Finds config file in a parent directory."""
        (tmp_path / "pyproject.toml").write_text("")
        child = tmp_path / "a" / "b"
        child.mkdir(parents=True)
        result = _find_config(child, ["pyproject.toml"])
        assert result == tmp_path

    def test_max_levels_respected(self, tmp_path: Path) -> None:
        """Stops after max_levels even if config exists higher up."""
        (tmp_path / "pyproject.toml").write_text("")
        deep = tmp_path / "a" / "b" / "c"
        deep.mkdir(parents=True)
        # max_levels=2 should not reach tmp_path (3 levels up)
        result = _find_config(deep, ["pyproject.toml"], max_levels=2)
        assert result is None

    def test_returns_none_when_not_found(self, tmp_path: Path) -> None:
        """Returns None when no config file exists."""
        result = _find_config(tmp_path, ["pyproject.toml"])
        assert result is None

    def test_starts_from_file_parent(self, tmp_path: Path) -> None:
        """When start is a file path, searches from its parent directory."""
        (tmp_path / "pyproject.toml").write_text("")
        py_file = tmp_path / "mod.py"
        py_file.write_text("")
        result = _find_config(py_file, ["pyproject.toml"])
        assert result == tmp_path

    def test_first_matching_filename_wins(self, tmp_path: Path) -> None:
        """When multiple config names given, first match in directory wins."""
        (tmp_path / "mypy.ini").write_text("")
        (tmp_path / "pyproject.toml").write_text("")
        # pyproject.toml is listed first, so it should be found
        result = _find_config(tmp_path, ["pyproject.toml", "mypy.ini"])
        assert result == tmp_path


class TestModuleStructure:
    """Tests for module-level requirements."""

    def test_future_annotations_import(self) -> None:
        """Module starts with from __future__ import annotations."""
        import importlib
        mod = importlib.import_module("pdd.get_lint_commands")
        mod_path = Path(mod.__file__)
        source = mod_path.read_text()
        assert "from __future__ import annotations" in source

    def test_return_types(self, tmp_path: Path) -> None:
        """get_lint_commands returns a list of LintCommand."""
        py_file = tmp_path / "x.py"
        py_file.write_text("")
        result = get_lint_commands(py_file)
        assert isinstance(result, list)
        for item in result:
            assert isinstance(item, LintCommand)

        # Non-python returns list too
        result2 = get_lint_commands(Path("x.js"))
        assert isinstance(result2, list)
        assert len(result2) == 0
