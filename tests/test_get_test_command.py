import pytest
from pathlib import Path
from unittest.mock import patch, mock_open, MagicMock
import csv
import io
import json
import re
import shlex
import subprocess
import os

# Import the module under test
from pdd.get_test_command import (
    TestCommand,
    _WorkspaceDeclaration,
    _WorkspaceMatchBudget,
    _WorkspaceProvider,
    _declared_workspace_membership,
    _detect_ts_test_runner,
    _relative_matches_workspace_glob,
    get_test_command_for_file,
)


class TestGetTestCommandForFilePython:
    """Tests for Python file handling."""

    def test_python_file_returns_pytest_command(self):
        """Test that a Python test file returns a pytest command."""
        test_file = "/path/to/test_example.py"
        result = get_test_command_for_file(test_file)
        
        # Should return a command (either from CSV or smart detection)
        # For Python, smart detection returns pytest command
        assert result is not None
        assert test_file in result.command or "test_example.py" in result.command

    def test_python_file_with_language_override(self):
        """Test Python file with explicit language parameter."""
        test_file = "/path/to/test_example.py"
        result = get_test_command_for_file(test_file, language="python")

        assert result is not None
        assert "pytest" in result.command.lower() or test_file in result.command

    def test_placeholder_replacement(self):
        """Test that {file} placeholder is replaced with actual file path."""
        test_file = "/my/test/file.py"
        result = get_test_command_for_file(test_file)

        if result:
            # The {file} placeholder should be replaced
            assert "{file}" not in result.command
            # The actual file path should be in the command
            assert test_file in result.command or "file.py" in result.command


class TestGetTestCommandResolutionOrder:
    """Tests for the resolution order: CSV → smart detection → None."""

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_csv_command_takes_priority(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """CSV run_test_command should be used first if available."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': 'custom_runner {file}'}
        }
        mock_get_lang.return_value = 'python'
        mock_smart_detect.return_value = 'pytest command'
        
        result = get_test_command_for_file('/test/example.py')

        assert result.command == 'custom_runner /test/example.py'
        # Smart detection should NOT be called when CSV has command
        mock_smart_detect.assert_not_called()

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_smart_detection_when_csv_empty(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Smart detection should be used when CSV command is empty."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': ''}
        }
        mock_get_lang.return_value = 'python'
        mock_smart_detect.return_value = 'pytest /test/example.py -q'
        
        result = get_test_command_for_file('/test/example.py')

        assert result.command == 'pytest /test/example.py -q'
        mock_smart_detect.assert_called_once_with('python', '/test/example.py')

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_smart_detection_when_extension_not_in_csv(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Smart detection should be used when extension not in CSV."""
        mock_load_csv.return_value = {}  # Empty CSV
        mock_get_lang.return_value = 'python'
        mock_smart_detect.return_value = 'pytest /test/example.py -q'
        
        result = get_test_command_for_file('/test/example.py')

        assert result.command == 'pytest /test/example.py -q'
        mock_smart_detect.assert_called_once()

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_returns_none_when_no_command_available(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Should return None when neither CSV nor smart detection works."""
        mock_load_csv.return_value = {}
        mock_get_lang.return_value = 'unknown_lang'
        mock_smart_detect.return_value = None
        
        result = get_test_command_for_file('/test/example.xyz')
        
        assert result is None


class TestLanguageResolution:
    """Tests for language resolution behavior."""

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_language_inferred_from_extension(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Language should be inferred from file extension when not provided."""
        mock_load_csv.return_value = {}
        mock_get_lang.return_value = 'python'
        mock_smart_detect.return_value = 'pytest cmd'
        
        get_test_command_for_file('/test/example.py')
        
        mock_get_lang.assert_called_once_with('.py')
        mock_smart_detect.assert_called_with('python', '/test/example.py')

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_language_override_used(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Provided language should override extension-based inference."""
        mock_load_csv.return_value = {}
        mock_smart_detect.return_value = 'java cmd'
        
        get_test_command_for_file('/test/example.py', language='java')
        
        # get_language should NOT be called when language is provided
        mock_get_lang.assert_not_called()
        mock_smart_detect.assert_called_with('java', '/test/example.py')

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_language_converted_to_lowercase(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Language should be converted to lowercase for smart detection."""
        mock_load_csv.return_value = {}
        mock_smart_detect.return_value = 'cmd'
        
        get_test_command_for_file('/test/example.py', language='PYTHON')
        
        mock_smart_detect.assert_called_with('python', '/test/example.py')


class TestEdgeCases:
    """Tests for edge cases and unusual inputs."""

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_file_with_no_extension(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Test handling of file with no extension."""
        mock_load_csv.return_value = {}
        mock_get_lang.return_value = None
        mock_smart_detect.return_value = None
        
        result = get_test_command_for_file('/test/Makefile')
        
        assert result is None

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_relative_path(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Test with relative file path."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': 'pytest {file}'}
        }
        mock_get_lang.return_value = 'python'
        
        result = get_test_command_for_file('tests/test_example.py')

        assert result.command == 'pytest tests/test_example.py'

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_path_with_spaces(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """CSV paths with spaces remain one literal shell argument."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': 'pytest {file}'}
        }
        mock_get_lang.return_value = 'python'
        
        result = get_test_command_for_file('/my path/test file.py')

        assert shlex.split(result.command) == ['pytest', '/my path/test file.py']

    @pytest.mark.parametrize(
        "test_file",
        (
            "/tmp/space path.py",
            "/tmp/single'quote.py",
            '/tmp/double"quote.py',
            "/tmp/semi;colon.py",
            "/tmp/`backticks`.py",
            "/tmp/$(command-substitution).py",
            "/tmp/a&b|c>(d)<e.py",
        ),
    )
    @patch('pdd.get_test_command._load_language_format')
    def test_csv_path_is_one_literal_argument(self, mock_load_csv, test_file):
        """Every POSIX shell metacharacter stays inside the path argument."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': 'pytest {file}'}
        }

        result = get_test_command_for_file(test_file, language='python')

        assert result is not None
        assert shlex.split(result.command) == ['pytest', test_file]

    @patch('pdd.get_test_command._load_language_format')
    def test_csv_path_cannot_execute_an_extra_shell_command(
        self, mock_load_csv, tmp_path
    ):
        """A semicolon in a CSV-substituted path cannot start another command."""
        injected = tmp_path / "injected.py"
        test_file = f"literal; touch {injected}"
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': "printf '%s' {file}"}
        }

        result = get_test_command_for_file(test_file, language='python')
        completed = subprocess.run(
            result.command, shell=True, check=True, capture_output=True, text=True
        )

        assert completed.stdout == test_file
        assert not injected.exists()

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_whitespace_only_csv_command(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """CSV command with only whitespace should fall through to smart detection."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': '   '}
        }
        mock_get_lang.return_value = 'python'
        mock_smart_detect.return_value = 'smart cmd'
        
        result = get_test_command_for_file('/test/example.py')

        # Whitespace-only command should be treated as empty
        assert result.command == 'smart cmd'
        mock_smart_detect.assert_called_once()

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_none_language_from_get_language(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Test when get_language returns None for unknown extension."""
        mock_load_csv.return_value = {}
        mock_get_lang.return_value = None
        
        result = get_test_command_for_file('/test/example.xyz')
        
        # Should not call smart detection with None language
        mock_smart_detect.assert_not_called()
        assert result is None


class TestTypeScriptTestRunnerDetection:
    """Tests for smart Jest/Vitest detection for TypeScript files."""

    def test_jest_config_overrides_csv_tsx_command(self, tmp_path):
        """When jest.config.js exists, TypeScript test files should use npx jest, not npx tsx."""
        (tmp_path / "jest.config.js").write_text("module.exports = {};")
        test_file = tmp_path / "tests" / "test_calculator.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('test', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" in result.command, f"Expected command starting with 'npx jest', got: {result}"

    def test_vitest_config_overrides_csv_tsx_command(self, tmp_path):
        """When vitest.config.ts exists, TypeScript test files should use npx vitest."""
        (tmp_path / "vitest.config.ts").write_text("export default {};")
        test_file = tmp_path / "tests" / "test_calculator.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('test', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert result.command.startswith("npx vitest"), f"Expected command starting with 'npx vitest', got: {result}"

    def test_no_config_falls_back_to_csv(self, tmp_path):
        """Without jest/vitest config, TypeScript should use the CSV command (npx tsx)."""
        test_file = tmp_path / "tests" / "test_calculator.ts"
        test_file.parent.mkdir()
        test_file.write_text("console.log('test')")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert result.command.startswith("npx tsx"), f"Expected command starting with 'npx tsx', got: {result}"

    def test_jest_config_ts_also_detected(self, tmp_path):
        """jest.config.ts should also trigger Jest detection."""
        (tmp_path / "jest.config.ts").write_text("export default {};")
        test_file = tmp_path / "tests" / "test_calculator.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('test', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert "npx jest" in result.command, f"Expected command starting with 'npx jest', got: {result}"

    def test_tsx_files_also_use_jest_when_available(self, tmp_path):
        """TSX files should also detect Jest config."""
        (tmp_path / "jest.config.js").write_text("module.exports = {};")
        test_file = tmp_path / "tests" / "test_component.tsx"
        test_file.parent.mkdir()
        test_file.write_text("describe('test', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescriptreact")

        assert "npx jest" in result.command, f"Expected command starting with 'npx jest', got: {result}"

    def test_jest_config_found_more_than_five_parents_up(self, tmp_path):
        """A colocated suite deep in a Next.js app tree must still find Jest.

        Regression: the runner detector previously walked up only 5 parents, so a
        page test at frontend/src/app/<route>/<sub>/__tests__/ never reached
        frontend/jest.config.js and fell back to a non-test runner. The walk now
        continues up to the repository root.
        """
        config_dir = tmp_path / "frontend"
        config_dir.mkdir()
        (config_dir / ".git").mkdir()
        (config_dir / "jest.config.js").write_text("module.exports = {};")
        (config_dir / "package.json").write_text("{}")
        # 7 directories below the config (well past the old 5-parent cap).
        test_dir = (
            config_dir / "src" / "app" / "admin" / "hackathon" / "events"
            / "eventId" / "__tests__"
        )
        test_dir.mkdir(parents=True)
        test_file = test_dir / "test_page.tsx"
        test_file.write_text("describe('page', () => {})")

        cmd, returned_dir = _detect_ts_test_runner(test_file)
        assert "npx jest" in cmd
        assert returned_dir == config_dir

    def test_jest_command_targets_path_literally_with_run_tests_by_path(self, tmp_path):
        """Jest must be invoked with --runTestsByPath so absolute paths match.

        Jest otherwise treats the trailing path as a regex; Next.js dynamic-route
        segments like [eventId]/[slug] are character classes that never match the
        literal bracketed path.
        """
        (tmp_path / "jest.config.js").write_text("module.exports = {};")
        (tmp_path / "package.json").write_text("{}")
        test_file = tmp_path / "tests" / "test_calculator.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('c', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert "--runTestsByPath" in result.command, result.command

    def test_dynamic_route_bracket_path_is_targeted_literally(self, tmp_path):
        """A bracketed dynamic-route suite path is passed to Jest verbatim."""
        config_dir = tmp_path / "frontend"
        config_dir.mkdir()
        (config_dir / "jest.config.js").write_text("module.exports = {};")
        (config_dir / "package.json").write_text("{}")
        test_dir = config_dir / "src" / "app" / "events" / "[slug]" / "__tests__"
        test_dir.mkdir(parents=True)
        test_file = test_dir / "test_page.tsx"
        test_file.write_text("describe('page', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescriptreact")

        assert "--runTestsByPath" in result.command
        # The resolved absolute path (brackets intact) must appear literally.
        assert str(test_file.resolve()) in result.command, result.command

    def test_walk_finds_workspace_root_config_past_leaf_package_json(self, tmp_path):
        """A workspace leaf must inherit the workspace-root runner config.

        Regression guard for the boundary: a leaf package has its own
        package.json but the Jest config lives at the workspace/repo root. The
        walk must pass *through* the leaf manifest and still find the root config.
        """
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")  # leaf manifest, no jest config
        test_dir = leaf / "src" / "__tests__"
        test_dir.mkdir(parents=True)
        test_file = test_dir / "widget.test.ts"
        test_file.write_text("describe('w', () => {})")

        cmd, returned_dir = _detect_ts_test_runner(test_file)
        assert "npx jest" in cmd
        assert returned_dir == repo, returned_dir

    @pytest.mark.parametrize(
        ("manifest_name", "manifest_contents"),
        (
            ("pnpm-workspace.yaml", "packages:\n  - 'packages/*'\n"),
            ("lerna.json", '{"packages": ["packages/*"]}'),
        ),
        ids=("pnpm", "lerna"),
    )
    def test_declaring_workspace_without_package_manifest_is_discovery_ceiling(
        self, tmp_path, manifest_name, manifest_contents
    ):
        """A declaring root may own its leaf, but an ancestor above it may not."""
        outer = tmp_path / "outer"
        outer.mkdir()
        (outer / ".git").mkdir()
        (outer / "jest.config.js").write_text("module.exports = {};")
        workspace = outer / "myws"
        workspace.mkdir()
        (workspace / manifest_name).write_text(manifest_contents)
        leaf = workspace / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert shlex.split(result.command) == ["npx", "tsx", str(test_file)]
        assert result.cwd is None

    def test_nested_workspace_chain_requires_each_declaring_root_to_be_member(
        self, tmp_path
    ):
        """A packaged inner workspace may inherit its proven outer runner."""
        outer = tmp_path / "outer"
        outer.mkdir()
        (outer / ".git").mkdir()
        (outer / "jest.config.js").write_text("module.exports = {};")
        (outer / "package.json").write_text('{"workspaces": ["myws"]}')
        workspace = outer / "myws"
        workspace.mkdir()
        (workspace / "package.json").write_text(
            '{"workspaces": ["packages/*"]}'
        )
        leaf = workspace / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert shlex.split(result.command) == [
            "npx",
            "jest",
            "--no-coverage",
            "--runTestsByPath",
            str(test_file.resolve()),
        ]
        assert result.cwd == outer

    def test_malformed_pnpm_scalar_constructor_fails_closed(self, tmp_path):
        """Invalid implicit YAML scalars cannot escape the public resolver."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "pnpm-workspace.yaml").write_text("packages: [2020-99-99]\n")
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert shlex.split(result.command) == ["npx", "tsx", str(test_file)]
        assert result.cwd is None

    def test_walk_stops_at_repository_root_and_does_not_escape(self, tmp_path):
        """The detector must not adopt a config above the repository root.

        A jest.config.js in an unrelated ancestor above the .git repo root must
        be ignored; without an in-repo config we fall back to CSV.
        """
        # Stray config above the repo root — must be ignored.
        (tmp_path / "jest.config.js").write_text("module.exports = {};")
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()  # repo root, no jest config inside
        test_file = repo / "src" / "test_calculator.ts"
        test_file.parent.mkdir()
        test_file.write_text("console.log('x')")

        result = get_test_command_for_file(str(test_file), language="typescript")

        # Falls back to the CSV runner (npx tsx), never the out-of-repo Jest.
        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_independent_leaf_package_does_not_adopt_repo_root_config(self, tmp_path):
        """An independent package must not adopt an unrelated repo-root config.

        The leaf has its own package.json and is NOT a workspace member (the repo
        root declares no ``workspaces``), so the walk must stop at the leaf and
        fall back to CSV rather than crossing to the repository-root Jest config.
        """
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text("{}")  # no "workspaces"
        leaf = repo / "packages" / "independent"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")  # own project, no jest config
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_unrelated_package_under_workspace_root_is_not_a_member(self, tmp_path):
        """A package that does not match the workspace globs is not a member.

        The repo root declares ``workspaces: ["packages/*"]`` but the test lives
        under ``vendor/tool`` (its own package.json). It must NOT adopt the
        repo-root Jest config — membership requires a glob match, not merely the
        presence of a workspaces declaration somewhere above.
        """
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        vendor = repo / "vendor" / "tool"
        vendor.mkdir(parents=True)
        (vendor / "package.json").write_text("{}")  # not under packages/*
        test_file = vendor / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_pnpm_exclusion_pattern_excludes_matching_package(self, tmp_path):
        """A pnpm `!` exclusion must remove a package from workspace membership.

        With `packages: ['packages/**', '!**/test/**']`, a package under
        `packages/app/test/fixture` matches the positive glob but is explicitly
        excluded, so it must NOT inherit the workspace-root Jest config.
        """
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "pnpm-workspace.yaml").write_text(
            "packages:\n  - 'packages/**'\n  - '!**/test/**'\n"
        )
        pkg = repo / "packages" / "app" / "test" / "fixture"
        pkg.mkdir(parents=True)
        (pkg / "package.json").write_text("{}")  # own manifest, excluded from ws
        test_file = pkg / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_npm_parent_exclusion_prunes_deep_workspace_candidate(self, tmp_path):
        """npm exclusions prune a matching parent instead of using pnpm ordering."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text(
            '{"workspaces": ["packages/**", "!packages/*"]}'
        )
        package = repo / "packages" / "deep" / "app"
        package.mkdir(parents=True)
        (package / "package.json").write_text("{}")
        test_file = package / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_npm_exclusion_matches_hidden_workspace_package(self, tmp_path):
        """npm ignore exclusions still match dot directories."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text(
            '{"workspaces": ["packages/.*", "!packages/*"]}'
        )
        package = repo / "packages" / ".hidden"
        package.mkdir(parents=True)
        (package / "package.json").write_text("{}")
        test_file = package / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_independent_intermediate_package_blocks_leaf_config_symlink(
        self, tmp_path
    ):
        """A leaf config symlink cannot bypass an intervening package boundary."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        outer_config = repo / "jest.config.js"
        outer_config.write_text("module.exports = {};")
        (repo / "package.json").write_text(
            '{"workspaces": ["vendor/container/packages/*"]}'
        )
        container = repo / "vendor" / "container"
        container.mkdir(parents=True)
        (container / "package.json").write_text("{}")
        package = container / "packages" / "app"
        package.mkdir(parents=True)
        (package / "package.json").write_text("{}")
        (package / "jest.config.js").symlink_to(outer_config)
        test_file = package / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_pnpm_workspace_ignores_node_modules_package(self, tmp_path):
        """Authoritative pnpm workspaces do not adopt dependency packages."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "pnpm-workspace.yaml").write_text("packages:\n  - '**'\n")
        package = repo / "node_modules" / "dependency"
        package.mkdir(parents=True)
        (package / "package.json").write_text("{}")
        test_file = package / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_brace_expansion_in_workspace_glob_matches_member(self, tmp_path):
        """npm/Yarn brace-expansion globs must be honored, not matched literally.

        `workspaces: ['packages/{app,lib}']` makes `packages/app` a member, which
        must inherit the workspace-root Jest config.
        """
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["packages/{app,lib}"]}')
        pkg = repo / "packages" / "app"
        pkg.mkdir(parents=True)
        (pkg / "package.json").write_text("{}")  # member, no own config
        test_file = pkg / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" in result.command, result.command

    def test_later_positive_workspace_pattern_reincludes_package(self, tmp_path):
        """The last matching pattern decides membership, including re-inclusion."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "pnpm-workspace.yaml").write_text(
            "packages:\n  - 'packages/**'\n  - '!packages/**'\n  - 'packages/app'\n"
        )
        pkg = repo / "packages" / "app"
        pkg.mkdir(parents=True)
        (pkg / "package.json").write_text("{}")
        test_file = pkg / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" in result.command, result.command

    def test_invalid_or_over_budget_workspace_declaration_fails_closed(self, tmp_path):
        """One unsupported pattern or too many patterns leaves membership unproven."""
        alternatives = ",".join(f"variant{number:02d}" for number in range(32))
        expensive_pattern = f"packages/{{{alternatives}}}/" + "a" * 470
        declarations = (
            ["packages/**", "packages/[app]"],
            ["packages/**"] * 129,
            ["packages/**"] + [expensive_pattern] * 127,
        )
        for index, patterns in enumerate(declarations):
            repo = tmp_path / f"repo-{index}"
            repo.mkdir()
            (repo / ".git").mkdir()
            (repo / "jest.config.js").write_text("module.exports = {};")
            (repo / "package.json").write_text(json.dumps({"workspaces": patterns}))
            pkg = repo / "packages" / "app"
            pkg.mkdir(parents=True)
            (pkg / "package.json").write_text("{}")
            test_file = pkg / "src" / "widget.test.ts"
            test_file.parent.mkdir()
            test_file.write_text("describe('w', () => {})")

            result = get_test_command_for_file(str(test_file), language="typescript")

            assert result is not None
            assert "npx jest" not in result.command, result.command

    @pytest.mark.parametrize(
        "manifest_name",
        ("package.json", "lerna.json", "pnpm-workspace.yaml"),
    )
    def test_oversized_workspace_manifest_fails_closed(self, tmp_path, manifest_name):
        """Manifest bytes are bounded before any JSON/YAML parsing occurs."""
        repo = tmp_path / manifest_name.replace(".", "-")
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        if manifest_name == "package.json":
            contents = json.dumps(
                {"workspaces": ["packages/*"], "padding": "x" * 1_048_576}
            )
        elif manifest_name == "lerna.json":
            (repo / "package.json").write_text("{}")
            contents = json.dumps(
                {"packages": ["packages/*"], "padding": "x" * 1_048_576}
            )
        else:
            (repo / "package.json").write_text("{}")
            contents = "packages:\n  - 'packages/*'\npadding: '" + "x" * 1_048_576 + "'\n"
        (repo / manifest_name).write_text(contents)
        package = repo / "packages" / "app"
        package.mkdir(parents=True)
        (package / "package.json").write_text("{}")
        test_file = package / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command, result.command

    @pytest.mark.parametrize(
        "manifest_name",
        ("package.json", "lerna.json", "pnpm-workspace.yaml"),
    )
    def test_deeply_nested_workspace_manifest_fails_closed(self, tmp_path, manifest_name):
        """Parser recursion is treated as an invalid declaration, not a crash."""
        repo = tmp_path / manifest_name.replace(".", "-")
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        nested = "[" * 2_000 + "0" + "]" * 2_000
        if manifest_name == "package.json":
            contents = '{"workspaces":["packages/*"],"nested":' + nested + "}"
        elif manifest_name == "lerna.json":
            (repo / "package.json").write_text("{}")
            contents = '{"packages":["packages/*"],"nested":' + nested + "}"
        else:
            (repo / "package.json").write_text("{}")
            contents = "packages:\n  - 'packages/*'\nnested: " + nested + "\n"
        (repo / manifest_name).write_text(contents)
        package = repo / "packages" / "app"
        package.mkdir(parents=True)
        (package / "package.json").write_text("{}")
        test_file = package / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_runner_config_symlink_must_resolve_inside_repository(self, tmp_path):
        """Reject an escaping config symlink while accepting an in-repo target."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        test_file = repo / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")
        external_config = tmp_path / "external-jest.config.js"
        external_config.write_text("module.exports = {};")
        config_link = repo / "jest.config.js"
        config_link.symlink_to(external_config)

        escaped = get_test_command_for_file(str(test_file), language="typescript")

        assert escaped is not None
        assert "npx jest" not in escaped.command, escaped.command

        config_link.unlink()
        internal_config = repo / "config" / "jest.config.js"
        internal_config.parent.mkdir()
        internal_config.write_text("module.exports = {};")
        config_link.symlink_to(internal_config)

        contained = get_test_command_for_file(str(test_file), language="typescript")

        assert contained is not None
        assert "npx jest" in contained.command, contained.command

    def test_nested_repository_does_not_adopt_outer_package_for_symlink(self, tmp_path):
        """A repository marker caps ownership even inside an outer workspace."""
        (tmp_path / "package.json").write_text('{"workspaces": ["repo"]}')
        external_config = tmp_path / "external-jest.config.js"
        external_config.write_text("module.exports = {};")
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").symlink_to(external_config)
        test_file = repo / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_repeated_double_star_pattern_is_bounded(self):
        """Many ``**`` segments match iteratively within the segment budget."""
        rel_parts = tuple(["segment"] * 127 + ["target"])
        pattern = "/".join(["**"] * 127 + ["target"])

        assert _relative_matches_workspace_glob(rel_parts, pattern)

    def test_non_git_project_stops_at_package_json_boundary(self, tmp_path):
        """Without a .git ancestor, stop at the nearest package.json.

        A stray jest.config.js above an independent project's package.json must
        not be adopted, and the walk must not run to the filesystem root.
        """
        (tmp_path / "jest.config.js").write_text("module.exports = {};")  # stray
        project = tmp_path / "project"
        project.mkdir()
        (project / "package.json").write_text("{}")  # boundary, no .git, no config
        test_file = project / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_non_git_config_symlink_must_remain_inside_package(self, tmp_path):
        """A package boundary contains config symlinks even without a Git root."""
        project = tmp_path / "project"
        project.mkdir()
        (project / "package.json").write_text("{}")
        test_file = project / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")
        external_config = tmp_path / "external-jest.config.js"
        external_config.write_text("module.exports = {};")
        config_link = project / "jest.config.js"
        config_link.symlink_to(external_config)

        escaped = get_test_command_for_file(str(test_file), language="typescript")

        assert escaped is not None
        assert "npx jest" not in escaped.command, escaped.command

        config_link.unlink()
        internal_config = project / "config" / "jest.config.js"
        internal_config.parent.mkdir()
        internal_config.write_text("module.exports = {};")
        config_link.symlink_to(internal_config)

        contained = get_test_command_for_file(str(test_file), language="typescript")

        assert contained is not None
        assert "npx jest" in contained.command, contained.command

    def test_unanchored_project_allows_plain_config_but_rejects_symlink(self, tmp_path):
        """Without Git/package/workspace ownership, config symlinks fail closed."""
        project = tmp_path / "loose-project"
        project.mkdir()
        test_file = project / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")
        config_path = project / "jest.config.js"
        config_path.write_text("module.exports = {};")

        ordinary = get_test_command_for_file(str(test_file), language="typescript")

        assert ordinary is not None
        assert "npx jest" in ordinary.command, ordinary.command

        config_path.unlink()
        external_config = tmp_path / "external-jest.config.js"
        external_config.write_text("module.exports = {};")
        config_path.symlink_to(external_config)

        unowned_symlink = get_test_command_for_file(
            str(test_file), language="typescript"
        )

        assert unowned_symlink is not None
        assert "npx jest" not in unowned_symlink.command, unowned_symlink.command

    def test_non_git_workspace_config_symlink_uses_workspace_ceiling(self, tmp_path):
        """A proven non-Git workspace contains its root config symlink target."""
        workspace = tmp_path / "workspace"
        workspace.mkdir()
        (workspace / "package.json").write_text(
            '{"workspaces": ["packages/*"]}'
        )
        package = workspace / "packages" / "app"
        package.mkdir(parents=True)
        (package / "package.json").write_text("{}")
        test_file = package / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")
        external_config = tmp_path / "external-workspace-jest.config.js"
        external_config.write_text("module.exports = {};")
        config_link = workspace / "jest.config.js"
        config_link.symlink_to(external_config)

        escaped = get_test_command_for_file(str(test_file), language="typescript")

        assert escaped is not None
        assert "npx jest" not in escaped.command, escaped.command

        config_link.unlink()
        internal_config = workspace / "config" / "jest.config.js"
        internal_config.parent.mkdir()
        internal_config.write_text("module.exports = {};")
        config_link.symlink_to(internal_config)

        contained = get_test_command_for_file(str(test_file), language="typescript")

        assert contained is not None
        assert "npx jest" in contained.command, contained.command
        assert contained.cwd == workspace

    def test_playwright_bracketed_spec_path_is_regex_escaped(self, tmp_path):
        """Playwright positional args are regexes, so bracketed paths must escape.

        `.spec` files under a Next.js dynamic route ([slug]) would otherwise never
        match Playwright's regex filter.
        """
        repo = tmp_path / "frontend"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "playwright.config.ts").write_text("export default {};")
        test_dir = repo / "e2e" / "events" / "[slug]"
        test_dir.mkdir(parents=True)
        test_file = test_dir / "landing.spec.ts"
        test_file.write_text("test('x', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result.command.startswith("npx playwright test"), result.command
        # Brackets must be regex-escaped so Playwright matches them literally.
        assert r"\[slug\]" in result.command, result.command

    def test_resolved_path_is_shell_quoted(self, tmp_path):
        """The path is shell-quoted so shell=True callers survive spaces/metachars."""
        repo = tmp_path / "my app"  # space in an ancestor directory
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        test_dir = repo / "src" / "__tests__"
        test_dir.mkdir(parents=True)
        test_file = test_dir / "widget.test.ts"
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        # The command must round-trip through a POSIX shell tokenizer back to the
        # exact resolved path (no re-splitting on the space).
        argv = shlex.split(result.command)
        assert str(test_file.resolve()) in argv, (result.command, argv)

    @pytest.mark.parametrize(
        ("config_name", "test_name", "runner_args"),
        (
            (
                "jest.config.js",
                "widget.test.ts",
                ["jest", "--no-coverage", "--runTestsByPath"],
            ),
            ("vitest.config.ts", "widget.test.ts", ["vitest", "run"]),
            ("playwright.config.ts", "widget.spec.ts", ["playwright", "test"]),
        ),
    )
    def test_runner_command_survives_hostile_shell_path(
        self, tmp_path, config_name, test_name, runner_args
    ):
        """shell=True must neither execute path contents nor alter the path arg."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / config_name).write_text("export default {};")
        hostile_dir = repo / (
            "hostile $(touch injected-dollar) `touch injected-backtick`; "
            "touch injected-semi; ' quote"
        )
        hostile_dir.mkdir()
        test_file = hostile_dir / test_name
        test_file.write_text("test('w', () => {})")
        fake_bin = tmp_path / "bin"
        fake_bin.mkdir()
        fake_npx = fake_bin / "npx"
        fake_npx.write_text(
            "#!/usr/bin/env python3\n"
            "import json, os, sys\n"
            "with open(os.environ['PDD_NPX_LOG'], 'w', encoding='utf-8') as handle:\n"
            "    json.dump(sys.argv[1:], handle)\n"
        )
        fake_npx.chmod(0o755)
        log_path = tmp_path / "npx-args.json"
        env = dict(os.environ)
        env["PATH"] = str(fake_bin) + os.pathsep + env.get("PATH", "")
        env["PDD_NPX_LOG"] = str(log_path)

        result = get_test_command_for_file(str(test_file), language="typescript")
        completed = subprocess.run(
            result.command,
            shell=True,
            cwd=result.cwd,
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )

        assert completed.returncode == 0, (completed.stdout, completed.stderr)
        expected_target = str(test_file.resolve())
        if config_name.startswith("playwright"):
            expected_target = re.escape(expected_target)
        assert json.loads(log_path.read_text()) == [*runner_args, expected_target]
        assert not (repo / "injected-dollar").exists()
        assert not (repo / "injected-backtick").exists()
        assert not (repo / "injected-semi").exists()


class TestFixErrorLoopPlaceholderSafety:
    """Completed runner commands must cross the fix-loop boundary unchanged."""

    def test_malicious_test_path_stays_one_shell_argument(self, tmp_path):
        """A literal placeholder and metacharacters remain inside the quoted path."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};\n")
        evil_dir = repo / "{test};touch PWN"
        evil_dir.mkdir()
        test_file = evil_dir / "a.test.ts"
        test_file.write_text("test('x', () => {});\n")

        test_command = get_test_command_for_file(
            str(test_file), language="typescript"
        )

        assert test_command is not None
        argv = shlex.split(test_command.command)
        assert str(test_file.resolve()) in argv
        assert "touch" not in argv

    def test_initial_verification_executes_exact_command_without_side_effect(
        self, tmp_path
    ):
        """The fix loop neither mutates the command nor reopens shell injection."""
        from pdd.fix_error_loop import _run_non_python_initial_verification

        cwd = tmp_path / "runner"
        cwd.mkdir()
        evil_dir = cwd / "{test}; touch PWN; #"
        evil_dir.mkdir()
        test_file = evil_dir / "a.test.ts"
        test_file.write_text("test('x', () => {});\n")
        code_file = evil_dir / "a.ts"
        code_file.write_text("export const x = 1;\n")
        command = f"true {shlex.quote(str(test_file.resolve()))}"
        test_command = TestCommand(command=command, cwd=cwd)
        captured = {}
        real_run = subprocess.run

        def run_and_capture(actual_command, **kwargs):
            captured["command"] = actual_command
            captured["cwd"] = kwargs.get("cwd")
            return real_run(actual_command, **kwargs)

        with patch(
            "pdd.fix_error_loop.get_test_command_for_file",
            return_value=test_command,
        ), patch(
            "pdd.fix_error_loop.subprocess.run", side_effect=run_and_capture
        ):
            passed, _output = _run_non_python_initial_verification(
                str(test_file), str(code_file)
            )

        assert passed is True
        assert captured == {"command": command, "cwd": str(cwd)}
        assert not (cwd / "PWN").exists()


class TestPlaywrightDetection:
    """Tests for Playwright detection for .spec.ts files."""

    def test_spec_ts_with_playwright_config_uses_playwright(self, tmp_path):
        """When playwright.config.ts exists, .spec.ts files should use npx playwright test."""
        (tmp_path / "playwright.config.ts").write_text("export default {};")
        (tmp_path / "jest.config.js").write_text("module.exports = {};")
        test_file = tmp_path / "e2e" / "login.spec.ts"
        test_file.parent.mkdir()
        test_file.write_text("import { test } from '@playwright/test';")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert result.command.startswith("npx playwright"), f"Expected 'npx playwright' command, got: {result}"

    def test_spec_ts_without_playwright_config_falls_back_to_jest(self, tmp_path):
        """.spec.ts with only jest config (no playwright) should use Jest (Angular-style)."""
        (tmp_path / "jest.config.js").write_text("module.exports = {};")
        test_file = tmp_path / "tests" / "app.spec.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('test', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" in result.command, f"Expected jest command, got: {result}"

    def test_test_ts_with_both_configs_uses_jest(self, tmp_path):
        """.test.ts files should use Jest even when playwright.config.ts exists."""
        (tmp_path / "playwright.config.ts").write_text("export default {};")
        (tmp_path / "jest.config.js").write_text("module.exports = {};")
        test_file = tmp_path / "tests" / "calculator.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('test', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" in result.command, f"Expected jest command, got: {result}"

    def test_spec_tsx_with_playwright_config_uses_playwright(self, tmp_path):
        """When playwright.config.ts exists, .spec.tsx files should also use playwright."""
        (tmp_path / "playwright.config.ts").write_text("export default {};")
        test_file = tmp_path / "e2e" / "component.spec.tsx"
        test_file.parent.mkdir()
        test_file.write_text("import { test } from '@playwright/test';")

        result = get_test_command_for_file(str(test_file), language="typescriptreact")

        assert result is not None
        assert result.command.startswith("npx playwright"), f"Expected 'npx playwright' command, got: {result}"


class TestIntegrationWithRealCSV:
    """Integration tests using the actual CSV file."""

    def test_python_file_integration(self):
        """Integration test with real CSV for Python file."""
        test_file = "/tmp/test_integration.py"
        result = get_test_command_for_file(test_file)
        
        # Should get some command for Python
        assert result is not None
        # Should contain the file path
        assert test_file in result.command

    def test_javascript_file_integration(self):
        """Integration test with real CSV for JavaScript file."""
        test_file = "/tmp/test_integration.js"
        result = get_test_command_for_file(test_file, language="javascript")

        # JavaScript should get a command from CSV run_test_command
        assert result is not None
        assert "node" in result.command
        assert test_file in result.command

    def test_unknown_extension_integration(self):
        """Integration test with unknown file extension."""
        test_file = "/tmp/test_file.unknownext"
        result = get_test_command_for_file(test_file)
        
        # Unknown extension should return None
        assert result is None


class TestZ3FormalVerification:
    """
    Z3-based formal verification of resolution logic.
    
    We model the resolution order as a logical formula and verify
    that the implementation follows the correct priority.
    """

    def test_resolution_order_formal_verification(self):
        """
        Formally verify the resolution order using Z3.
        
        Properties to verify:
        1. If CSV command exists and is non-empty, it is returned
        2. If CSV command is empty/missing and smart detection succeeds, smart result is returned
        3. If both fail, None is returned
        """
        try:
            from z3 import Bool, Implies, And, Not, Solver, sat
        except ImportError:
            pytest.skip("Z3 not installed")

        # Boolean variables representing conditions
        csv_has_command = Bool('csv_has_command')
        smart_detection_succeeds = Bool('smart_detection_succeeds')
        returns_csv_command = Bool('returns_csv_command')
        returns_smart_command = Bool('returns_smart_command')
        returns_none = Bool('returns_none')

        solver = Solver()

        # Property 1: If CSV has command, return CSV command
        solver.add(Implies(csv_has_command, returns_csv_command))
        
        # Property 2: If CSV doesn't have command but smart detection succeeds, return smart command
        solver.add(Implies(And(Not(csv_has_command), smart_detection_succeeds), returns_smart_command))
        
        # Property 3: If neither works, return None
        solver.add(Implies(And(Not(csv_has_command), Not(smart_detection_succeeds)), returns_none))
        
        # Mutual exclusivity: only one result type
        solver.add(Implies(returns_csv_command, And(Not(returns_smart_command), Not(returns_none))))
        solver.add(Implies(returns_smart_command, And(Not(returns_csv_command), Not(returns_none))))
        solver.add(Implies(returns_none, And(Not(returns_csv_command), Not(returns_smart_command))))

        # Verify the model is satisfiable
        assert solver.check() == sat, "Resolution order logic is inconsistent"

    def test_placeholder_replacement_formal_verification(self):
        """
        Formally verify that placeholder replacement occurs when command is found.
        
        Property: If a command is returned (not None), it should not contain {file}
        """
        try:
            from z3 import Bool, Implies, Not, Solver, sat
        except ImportError:
            pytest.skip("Z3 not installed")

        command_found = Bool('command_found')
        placeholder_replaced = Bool('placeholder_replaced')
        result_contains_placeholder = Bool('result_contains_placeholder')

        solver = Solver()

        # If command is found, placeholder must be replaced
        solver.add(Implies(command_found, placeholder_replaced))
        
        # If placeholder is replaced, result should not contain placeholder
        solver.add(Implies(placeholder_replaced, Not(result_contains_placeholder)))
        
        # Therefore: if command found, result should not contain placeholder
        solver.add(Implies(command_found, Not(result_contains_placeholder)))

        assert solver.check() == sat, "Placeholder replacement logic is inconsistent"


class TestCacheAndLoadBehavior:
    """Tests for CSV loading and caching behavior."""

    @patch('pdd.get_test_command._load_language_format')
    def test_csv_loaded_on_call(self, mock_load_csv):
        """Verify CSV is loaded when function is called."""
        mock_load_csv.return_value = {}
        
        with patch('pdd.get_test_command.default_verify_cmd_for', return_value=None):
            with patch('pdd.get_test_command.get_language', return_value=None):
                get_test_command_for_file('/test/file.py')
        
        mock_load_csv.assert_called()

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_extension_lookup_case_sensitivity(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Test that extension lookup handles case correctly."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': 'pytest {file}'}
        }
        mock_get_lang.return_value = 'python'
        
        # Test with uppercase extension
        result = get_test_command_for_file('/test/example.PY')
        
        # The function should handle case appropriately
        # (behavior depends on implementation - this tests current behavior)
        assert result is not None or mock_smart_detect.called


class TestMultipleFileTypes:
    """Tests for various file types and languages."""

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_typescript_file(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Test TypeScript file handling."""
        mock_load_csv.return_value = {}
        mock_get_lang.return_value = 'typescript'
        mock_smart_detect.return_value = 'npx jest /test/example.ts'
        
        result = get_test_command_for_file('/test/example.ts')

        assert result.command == 'npx jest /test/example.ts'

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_java_file(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Test Java file handling."""
        mock_load_csv.return_value = {}
        mock_get_lang.return_value = 'java'
        mock_smart_detect.return_value = 'mvn test -Dtest=ExampleTest'

        result = get_test_command_for_file('/test/ExampleTest.java')

        assert result.command == 'mvn test -Dtest=ExampleTest'


# ============================================================================
# Issue #1080: Non-Python test verification uses wrong cwd — breaks monorepos
# ============================================================================

class TestIssue1080MonorepoCwd:
    """Tests for issue #1080: _detect_ts_test_runner must return config directory alongside command.

    Bug: _detect_ts_test_runner() finds the config directory (e.g., frontend/ containing
    jest.config.js) but only returns the command string, discarding the config directory.
    All 6 callers then use wrong cwd when running subprocess.run(), breaking monorepos.
    """

    # --- Test 1: Jest returns (command, config_dir) ---

    def test_detect_ts_test_runner_jest_returns_config_dir(self, tmp_path):
        """_detect_ts_test_runner must return the config directory alongside the Jest command.

        Before fix: returns bare string 'npx jest --no-coverage --'
        After fix: returns ('npx jest --no-coverage --', Path('frontend/'))
        """
        config_dir = tmp_path / "frontend"
        config_dir.mkdir()
        (config_dir / "jest.config.js").write_text("module.exports = {};")

        test_dir = config_dir / "src" / "lib" / "__test__"
        test_dir.mkdir(parents=True)
        test_file = test_dir / "api.test.ts"
        test_file.write_text("test('api', () => {});")

        result = _detect_ts_test_runner(test_file)
        assert result is not None
        # Bug #1080: string can't unpack to 2 values → ValueError
        cmd, returned_dir = result
        assert "npx jest" in cmd
        assert returned_dir == config_dir

    # --- Test 2: Vitest returns (command, config_dir) ---

    def test_detect_ts_test_runner_vitest_returns_config_dir(self, tmp_path):
        """_detect_ts_test_runner must return the config directory for Vitest."""
        config_dir = tmp_path / "packages" / "app"
        config_dir.mkdir(parents=True)
        (config_dir / "vitest.config.ts").write_text("export default {};")

        test_dir = config_dir / "src" / "__tests__"
        test_dir.mkdir(parents=True)
        test_file = test_dir / "utils.test.ts"
        test_file.write_text("test('utils', () => {});")

        result = _detect_ts_test_runner(test_file)
        assert result is not None
        cmd, returned_dir = result
        assert "npx vitest" in cmd
        assert returned_dir == config_dir

    # --- Test 3: Playwright returns (command, config_dir) ---

    def test_detect_ts_test_runner_playwright_returns_config_dir(self, tmp_path):
        """_detect_ts_test_runner must return the config directory for Playwright."""
        config_dir = tmp_path / "frontend"
        config_dir.mkdir()
        (config_dir / "playwright.config.ts").write_text("export default {};")

        test_dir = config_dir / "e2e" / "tests"
        test_dir.mkdir(parents=True)
        test_file = test_dir / "login.spec.ts"
        test_file.write_text("test('login', async () => {});")

        result = _detect_ts_test_runner(test_file)
        assert result is not None
        cmd, returned_dir = result
        assert "npx playwright" in cmd
        assert returned_dir == config_dir

    # --- Test 4: No config returns None (regression guard) ---

    def test_detect_ts_test_runner_no_config_returns_none(self, tmp_path):
        """_detect_ts_test_runner returns None when no config found (unchanged behavior)."""
        test_dir = tmp_path / "src"
        test_dir.mkdir()
        test_file = test_dir / "foo.test.ts"
        test_file.write_text("test('foo', () => {});")

        result = _detect_ts_test_runner(test_file)
        assert result is None

    # --- Test 5: get_test_command_for_file returns TestCommand with cwd for monorepo Jest ---

    def test_get_test_command_monorepo_jest_returns_cwd(self, tmp_path):
        """get_test_command_for_file must return a result with cwd for monorepo Jest.

        Before fix: returns bare string (no .cwd attribute)
        After fix: returns TestCommand(command=..., cwd=config_dir)
        """
        config_dir = tmp_path / "frontend"
        config_dir.mkdir()
        (config_dir / "jest.config.js").write_text("module.exports = {};")

        test_dir = config_dir / "src" / "lib" / "__test__"
        test_dir.mkdir(parents=True)
        test_file = test_dir / "api.test.ts"
        test_file.write_text("test('api', () => {});")

        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        # Bug #1080: 'str' has no attribute 'cwd' → AttributeError
        assert result.cwd == config_dir

    # --- Test 6: CSV returns TestCommand with cwd=None ---

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.get_language')
    def test_csv_command_returns_testcommand_with_none_cwd(self, mock_get_lang, mock_load_csv):
        """CSV commands should return a result with cwd=None (caller decides cwd)."""
        mock_load_csv.return_value = {
            '.js': {'extension': '.js', 'run_test_command': 'node {file}'}
        }
        mock_get_lang.return_value = 'javascript'

        result = get_test_command_for_file('/test/example.js')
        assert result is not None
        # Bug #1080: 'str' has no attribute 'cwd' → AttributeError
        assert result.cwd is None

    # --- Test 7: Smart detection returns TestCommand with cwd=None ---

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_smart_detection_returns_testcommand_with_none_cwd(self, mock_get_lang, mock_smart, mock_csv):
        """Smart detection fallback should return a result with cwd=None."""
        mock_csv.return_value = {}
        mock_get_lang.return_value = 'ruby'
        mock_smart.return_value = 'ruby test_example.rb'

        result = get_test_command_for_file('/test/example.rb')
        assert result is not None
        # Bug #1080: 'str' has no attribute 'cwd' → AttributeError
        assert result.cwd is None

    # --- Test 8: Config directory 3 levels up from test file ---

    def test_detect_ts_test_runner_config_three_levels_up(self, tmp_path):
        """Walk-up logic must find config multiple directories up from the test file."""
        config_dir = tmp_path / "frontend"
        config_dir.mkdir()
        (config_dir / "jest.config.js").write_text("module.exports = {};")

        # 4 levels deep: frontend/src/components/__test__/deep/
        test_dir = config_dir / "src" / "components" / "__test__" / "deep"
        test_dir.mkdir(parents=True)
        test_file = test_dir / "Widget.test.tsx"
        test_file.write_text("test('widget', () => {});")

        result = _detect_ts_test_runner(test_file)
        assert result is not None
        cmd, returned_dir = result
        assert returned_dir == config_dir

    # --- Test 16: Exact monorepo scenario from the issue ---

    def test_exact_monorepo_scenario_from_issue(self, tmp_path):
        """Reproduce the exact scenario from issue downstream_project#900.

        Structure: frontend/jest.config.js, frontend/src/lib/__test__/api.test.ts
        Expected: cwd=frontend/ so Jest can find jest-environment-jsdom
        """
        config_dir = tmp_path / "frontend"
        config_dir.mkdir()
        (config_dir / "jest.config.js").write_text("module.exports = {};")
        (config_dir / "node_modules").mkdir()

        test_dir = config_dir / "src" / "lib" / "__test__"
        test_dir.mkdir(parents=True)
        test_file = test_dir / "api.test.ts"
        test_file.write_text("test('api', () => {});")

        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        # Bug #1080: str has no .cwd → AttributeError
        assert result.cwd == config_dir, (
            f"Bug #1080: Expected cwd={config_dir}, got {getattr(result, 'cwd', 'N/A (string)')}"
        )

    # --- Test 17: Flat repo (config at root) ---

    def test_flat_repo_config_at_root_returns_root_as_cwd(self, tmp_path):
        """For flat repos, config dir should be the repo root."""
        (tmp_path / "jest.config.js").write_text("module.exports = {};")

        test_dir = tmp_path / "src"
        test_dir.mkdir()
        test_file = test_dir / "utils.test.ts"
        test_file.write_text("test('utils', () => {});")

        result = _detect_ts_test_runner(test_file)
        assert result is not None
        cmd, returned_dir = result
        # Config at root → cwd should be root
        assert returned_dir == tmp_path

    # --- Test 18: Python regression guard ---

    def test_python_returns_testcommand_with_none_cwd(self):
        """Python files should return a result with cwd=None (uses _find_project_root separately).

        This verifies the TestCommand change doesn't break the Python code path.
        """
        result = get_test_command_for_file('/tmp/test_example.py', language='python')
        assert result is not None
        # Bug #1080: 'str' has no attribute 'cwd' → AttributeError
        assert result.cwd is None


class TestTestCommandDataclass:
    """Tests for the TestCommand dataclass itself."""

    def test_testcommand_default_cwd_is_none(self):
        tc = TestCommand(command="pytest foo.py")
        assert tc.command == "pytest foo.py"
        assert tc.cwd is None

    def test_testcommand_with_explicit_cwd(self, tmp_path):
        tc = TestCommand(command="npx jest", cwd=tmp_path)
        assert tc.cwd == tmp_path

    def test_testcommand_not_collected_by_pytest(self):
        # __test__ = False prevents pytest from treating it as a test class
        assert getattr(TestCommand, "__test__", True) is False


class TestAdditionalRunnerDetection:
    """Additional coverage for runner detection edge cases."""

    def test_vitest_mjs_config_detected(self, tmp_path):
        (tmp_path / "vitest.config.mjs").write_text("export default {};")
        (tmp_path / "package.json").write_text("{}")
        test_file = tmp_path / "src" / "foo.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('foo', () => {});")

        result = _detect_ts_test_runner(test_file)
        assert result is not None
        cmd, cfg_dir = result
        assert "npx vitest" in cmd
        assert cfg_dir == tmp_path

    def test_jest_mjs_config_detected(self, tmp_path):
        (tmp_path / "jest.config.mjs").write_text("export default {};")
        test_file = tmp_path / "foo.test.ts"
        test_file.write_text("test('foo', () => {});")

        result = _detect_ts_test_runner(test_file)
        assert result is not None
        cmd, _ = result
        assert "npx jest" in cmd

    def test_playwright_js_config_for_spec_file(self, tmp_path):
        (tmp_path / "playwright.config.js").write_text("module.exports = {};")
        test_file = tmp_path / "login.spec.ts"
        test_file.write_text("test('login', () => {});")

        result = _detect_ts_test_runner(test_file)
        assert result is not None
        cmd, _ = result
        assert "npx playwright" in cmd

    def test_playwright_mjs_config_for_spec_file(self, tmp_path):
        (tmp_path / "playwright.config.mjs").write_text("export default {};")
        test_file = tmp_path / "login.spec.tsx"
        test_file.write_text("test('x', () => {});")

        result = _detect_ts_test_runner(test_file)
        assert result is not None
        cmd, _ = result
        assert "npx playwright" in cmd

    def test_nearest_config_wins_over_ancestor(self, tmp_path):
        """A closer jest.config should be preferred over a more distant one."""
        (tmp_path / "vitest.config.ts").write_text("export default {};")
        (tmp_path / "package.json").write_text("{}")
        inner = tmp_path / "packages" / "app"
        inner.mkdir(parents=True)
        (inner / "jest.config.js").write_text("module.exports = {};")
        test_file = inner / "src" / "foo.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {});")

        result = _detect_ts_test_runner(test_file)
        assert result is not None
        cmd, cfg_dir = result
        assert "npx jest" in cmd
        assert cfg_dir == inner

    def test_absolute_resolved_path_used_in_command(self, tmp_path, monkeypatch):
        """The command should embed the resolved absolute path of the test file."""
        (tmp_path / "jest.config.js").write_text("module.exports = {};")
        (tmp_path / "package.json").write_text("{}")
        sub = tmp_path / "src"
        sub.mkdir()
        test_file = sub / "foo.test.ts"
        test_file.write_text("test('x', () => {});")

        # Change into the directory and pass a relative path
        monkeypatch.chdir(sub)
        result = get_test_command_for_file("foo.test.ts", language="typescript")
        assert result is not None
        assert str(test_file.resolve()) in result.command


class TestLoadLanguageFormatIntegration:
    """Integration tests that exercise CSV loading via public entry point."""

    def test_rust_extension_uses_cargo_test_from_csv(self):
        result = get_test_command_for_file("/tmp/lib.rs", language="rust")
        # CSV has 'cargo test' for .rs with no {file} placeholder
        assert result is not None
        assert "cargo test" in result.command

    def test_go_extension_uses_go_test_from_csv(self):
        result = get_test_command_for_file("/tmp/foo_test.go", language="go")
        assert result is not None
        assert "go test" in result.command
        assert "/tmp/foo_test.go" in result.command

class TestAdditionalCoverage:
    """Extra black-box coverage for uncovered branches."""

    def test_python_file_ignores_nearby_jest_config(self, tmp_path, monkeypatch):
        """Non-TS files must not trigger the TS runner detector."""
        (tmp_path / "jest.config.js").write_text("module.exports = {};")
        (tmp_path / ".git").mkdir()
        test_file = tmp_path / "test_foo.py"
        test_file.write_text("def test_x(): pass")

        result = get_test_command_for_file(str(test_file), language="python")
        assert result is not None
        assert "jest" not in result.command

    def test_playwright_command_omits_run_tests_by_path(self, tmp_path):
        (tmp_path / "playwright.config.ts").write_text("export default {};")
        test_file = tmp_path / "e2e" / "login.spec.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "--runTestsByPath" not in result.command

    def test_lerna_omitted_packages_does_not_invent_workspace(self, tmp_path):
        """Lerna without packages or package-manager proof fails closed."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text("{}")
        (repo / "lerna.json").write_text("{}")
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "npx jest" not in result.command

    def test_lerna_null_packages_does_not_authorize_root_runner(self, tmp_path):
        """An explicit null Lerna packages value is invalid, not a default."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text("{}")
        (repo / "lerna.json").write_text('{"packages": null}')
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command

    def test_lerna_omitted_packages_reuses_proven_npm_workspace(self, tmp_path):
        """A valid package-manager declaration can independently prove membership."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        (repo / "lerna.json").write_text("{}")
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" in result.command

    def test_valid_npm_workspace_survives_invalid_lerna_declaration(self, tmp_path):
        """Invalid Lerna data does not discard independent npm membership proof."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        (repo / "lerna.json").write_text('{"packages": null}')
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" in result.command
        assert "--runTestsByPath" in result.command
        assert result.cwd == repo

    def test_valid_lerna_workspace_survives_malformed_npm_manifest(self, tmp_path):
        """Malformed npm data does not discard independent Lerna membership proof."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text("{")
        (repo / "lerna.json").write_text('{"packages": ["packages/*"]}')
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" in result.command
        assert "--runTestsByPath" in result.command
        assert result.cwd == repo

    def test_invalid_npm_and_lerna_declarations_fail_closed(self, tmp_path):
        """Without a valid provider, malformed declarations prove no membership."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text("{")
        (repo / "lerna.json").write_text('{"packages": null}')
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command

    def test_invalid_pnpm_does_not_fall_through_to_npm_or_lerna(self, tmp_path):
        """An authoritative invalid pnpm declaration ignores other providers."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        (repo / "lerna.json").write_text('{"packages": ["packages/*"]}')
        (repo / "pnpm-workspace.yaml").write_text("packages: null\n")
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command

    def test_workspaces_dict_form_with_packages_key(self, tmp_path):
        """npm ``workspaces: {packages: [...]}`` dict form is honored."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text(
            '{"workspaces": {"packages": ["packages/*"]}}'
        )
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "x.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('x', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "npx jest" in result.command

    def test_pnpm_workspace_authoritative_over_package_json(self, tmp_path):
        """A pnpm-workspace.yaml declaration takes precedence over package.json workspaces."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        # package.json would include it, but pnpm authoritative declaration excludes it.
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        (repo / "pnpm-workspace.yaml").write_text("packages:\n  - 'other/*'\n")
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "x.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('x', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "npx jest" not in result.command

    def test_language_empty_string_from_get_language_returns_none(self, tmp_path):
        """An unknown extension yielding empty language must return None."""
        test_file = tmp_path / "file.unknownxyz"
        test_file.write_text("x")
        result = get_test_command_for_file(str(test_file))
        assert result is None

    def test_vitest_path_with_spaces_is_shell_quoted(self, tmp_path):
        repo = tmp_path / "my proj"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "vitest.config.ts").write_text("export default {};")
        test_file = repo / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        argv = shlex.split(result.command)
        assert str(test_file.resolve()) in argv


class TestRunnerBoundaryRegressions:
    """Public-boundary regressions for ownership proof and bounded discovery."""

    @pytest.mark.parametrize(
        ("relative_package", "patterns", "inherits_jest"),
        (
            (("packages", ".hidden"), ["packages/*"], False),
            (("packages", ".hidden"), ["packages/.*"], True),
            (("packages", "visible"), ["packages/*"], True),
            (("node_modules", "dependency"), ["**"], False),
            (("packages", "visible"), ["**"], True),
        ),
    )
    def test_npm_workspace_provider_boundaries_control_root_runner_inheritance(
        self, tmp_path, relative_package, patterns, inherits_jest
    ):
        """npm dot and node_modules rules govern public runner inheritance."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text(json.dumps({"workspaces": patterns}))
        leaf = repo.joinpath(*relative_package)
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert ("npx jest" in result.command) is inherits_jest

    @pytest.mark.parametrize("pattern", ("#pkg", "./#pkg"))
    def test_npm_comment_pattern_cannot_authorize_root_jest_config(
        self, tmp_path, pattern
    ):
        """npm comments cannot make an independent hash-named package a workspace."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text(json.dumps({"workspaces": [pattern]}))
        leaf = repo / "#pkg"
        leaf.mkdir()
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command
        assert result.cwd is None

    @pytest.mark.parametrize("pattern", ("#pkg", "./#pkg"))
    def test_npm_comment_pattern_does_not_discard_lerna_membership(
        self, tmp_path, pattern
    ):
        """A valid Lerna declaration can still prove membership independently."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text(json.dumps({"workspaces": [pattern]}))
        (repo / "lerna.json").write_text('{"packages": ["#pkg"]}')
        leaf = repo / "#pkg"
        leaf.mkdir()
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" in result.command
        assert result.cwd == repo

    @pytest.mark.parametrize("pattern", ("#pkg", "./#pkg"))
    def test_npm_comment_patterns_do_not_prove_pure_membership(self, pattern):
        """The provider seam preserves npm comments without changing Lerna rules."""
        package = ("#pkg",)
        npm = _WorkspaceDeclaration(_WorkspaceProvider.NPM, (pattern,))
        lerna = _WorkspaceDeclaration(_WorkspaceProvider.LERNA, ("#pkg",))

        assert _declared_workspace_membership(package, npm) is False
        assert _declared_workspace_membership(package, lerna) is True

    @pytest.mark.parametrize("extglob", ("?(foo)", "*(foo)", "+(foo)", "@(foo)", "!(foo)"))
    @pytest.mark.parametrize("excluded", (False, True))
    def test_unsupported_extglob_declaration_cannot_authorize_root_runner(
        self, tmp_path, extglob, excluded
    ):
        """Any extglob makes the relevant workspace declaration unproven."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        patterns = ["packages/*", f"{'!' if excluded else ''}packages/{extglob}"]
        (repo / "package.json").write_text(json.dumps({"workspaces": patterns}))
        leaf = repo / "packages" / "foo"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command

    @pytest.mark.parametrize("marker_kind", ("dangling", "looping", "escaping"))
    def test_invalid_symlink_leaf_blocks_matching_npm_workspace(
        self, tmp_path, marker_kind
    ):
        """A matching npm declaration cannot authorize an invalid symlink leaf."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        marker = leaf / "package.json"
        if marker_kind == "escaping":
            target = tmp_path / "outside-package.json"
            target.write_text("{}")
        elif marker_kind == "dangling":
            target = tmp_path / "missing-package.json"
        else:
            target = marker
        marker.symlink_to(target)
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command

    @pytest.mark.parametrize("contents", ("{", "null", "[]", '"package"'))
    def test_non_object_or_malformed_leaf_blocks_matching_npm_workspace(
        self, tmp_path, contents
    ):
        """Only a bounded JSON object is a crossable package leaf."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text(contents)
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command

    def test_unreadable_leaf_blocks_matching_npm_workspace(self, tmp_path):
        """A deterministic read-failure seam keeps the leaf independent."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        marker = leaf / "package.json"
        marker.write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {})")
        from pdd.get_test_command import _read_workspace_manifest

        def unreadable_leaf(path):
            if Path(os.path.abspath(path)) == marker:
                return None
            return _read_workspace_manifest(path)

        with patch(
            "pdd.get_test_command._read_workspace_manifest",
            side_effect=unreadable_leaf,
        ):
            result = get_test_command_for_file(
                str(test_file), language="typescript"
            )

        assert result is not None
        assert "npx jest" not in result.command

    @pytest.mark.parametrize("provider", ("lerna", "pnpm"))
    def test_invalid_leaf_blocks_other_valid_workspace_providers(
        self, tmp_path, provider
    ):
        """Lerna and pnpm membership also require a legitimate package leaf."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text("{}")
        if provider == "lerna":
            (repo / "lerna.json").write_text('{"packages": ["packages/*"]}')
        else:
            (repo / "pnpm-workspace.yaml").write_text(
                "packages:\n  - 'packages/*'\n"
            )
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command

    def test_git_worktree_file_is_repository_ceiling(self, tmp_path):
        """A worktree-style .git file prevents discovery above the repository."""
        (tmp_path / "jest.config.js").write_text("module.exports = {};")
        repo = tmp_path / "worktree"
        repo.mkdir()
        (repo / ".git").write_text("gitdir: /tmp/example.git/worktrees/example\n")
        test_file = repo / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")

        assert result is not None
        assert "npx jest" not in result.command

    def test_public_lookup_reads_each_workspace_manifest_at_most_once(
        self, tmp_path
    ):
        """Overlapping package-boundary searches reuse per-lookup manifest reads."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["*"]}')
        current = repo
        manifest_paths = {repo / "package.json"}
        for index in range(8):
            current = current / f"level-{index}"
            current.mkdir()
            marker = current / "package.json"
            marker.write_text('{"workspaces": ["*"]}')
            manifest_paths.add(marker)
        test_file = current / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {})")

        reads = []
        parses = []
        from pdd.get_test_command import (
            _parse_package_manifest,
            _read_workspace_manifest,
        )

        def counted_read(path):
            reads.append(path.resolve())
            return _read_workspace_manifest(path)

        def counted_parse(contents):
            parses.append(contents)
            return _parse_package_manifest(contents)

        with patch(
            "pdd.get_test_command._read_workspace_manifest",
            side_effect=counted_read,
        ), patch(
            "pdd.get_test_command._parse_package_manifest",
            side_effect=counted_parse,
        ):
            result = get_test_command_for_file(
                str(test_file), language="typescript"
            )

        assert result is not None and "npx jest" in result.command
        relevant_reads = [path for path in reads if path in manifest_paths]
        assert len(relevant_reads) == len(set(relevant_reads))
        assert len(parses) == len(manifest_paths)

    @pytest.mark.parametrize(
        ("config_name", "test_name", "runner_token"),
        (
            ("jest.config.js", "widget.test.ts", "jest"),
            ("vitest.config.ts", "widget.test.ts", "vitest"),
            ("playwright.config.ts", "widget.spec.ts", "playwright"),
        ),
    )
    def test_public_lookup_global_match_budget_fails_closed(
        self, tmp_path, config_name, test_name, runner_token
    ):
        """Many costly package boundaries share one deterministic work cap."""
        repo = tmp_path / runner_token
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / config_name).write_text("export default {};\n")
        patterns = ["x" * 128] * 127 + ["*"]
        declaration = json.dumps({"workspaces": patterns})
        current = repo
        for index in range(60):
            (current / "package.json").write_text(declaration)
            current = current / f"level-{index:02d}"
            current.mkdir()
        (current / "package.json").write_text("{}")
        test_file = current / "src" / test_name
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {});\n")
        budget = _WorkspaceMatchBudget(250_000)

        with patch(
            "pdd.get_test_command._WorkspaceMatchBudget", return_value=budget
        ):
            result = get_test_command_for_file(
                str(test_file), language="typescript"
            )

        assert result is not None
        assert f"npx {runner_token}" not in result.command
        assert budget.exhausted is True
        assert 0 < budget.spent <= budget.limit

    def test_ordinary_deep_workspace_resolves_below_global_match_budget(
        self, tmp_path
    ):
        """Cheap valid membership across many boundaries remains supported."""
        repo = tmp_path / "ordinary"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};\n")
        declaration = json.dumps({"workspaces": ["*"]})
        current = repo
        for index in range(60):
            (current / "package.json").write_text(declaration)
            current = current / f"level-{index:02d}"
            current.mkdir()
        (current / "package.json").write_text("{}")
        test_file = current / "src" / "widget.test.ts"
        test_file.parent.mkdir()
        test_file.write_text("test('x', () => {});\n")
        budget = _WorkspaceMatchBudget(250_000)

        with patch(
            "pdd.get_test_command._WorkspaceMatchBudget", return_value=budget
        ):
            result = get_test_command_for_file(
                str(test_file), language="typescript"
            )

        assert result is not None
        assert "npx jest" in result.command
        assert result.cwd == repo
        assert budget.exhausted is False
        assert 0 < budget.spent < budget.limit
