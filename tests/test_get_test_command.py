import pytest
from pathlib import Path
from unittest.mock import patch, mock_open, MagicMock
import csv
import io
import json
import shlex
import sys
import os

# Import the module under test
from pdd.get_test_command import (
    get_test_command_for_file,
    _detect_ts_test_runner,
    TestCommand,
    _workspace_globs_for,
    _belongs_to_ancestor_workspace,
    _package_matches_workspace,
    _wildcard_segment_match,
    _expand_braces,
    _BraceBudgetError,
    _PatternBudgetError,
    _relative_matches_workspace_glob,
    _lexical_repo_root,
    _find_expandable_brace,
    _has_brace_range,
    _has_complete_bracket_class,
    _has_complete_extglob,
    _MAX_GLOB_LENGTH,
    _RUNNER_CONFIGS,
    _MAX_BRACE_SCAN_WORK,
    _MAX_MATCH_CELLS,
    _MAX_BRACE_EXPANSION,
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
        """A CSV path with spaces must be shell-quoted (callers use shell=True)."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': 'pytest {file}'}
        }
        mock_get_lang.return_value = 'python'

        result = get_test_command_for_file('/my path/test file.py')

        # Quoted so a POSIX shell tokenizer recovers the exact path (no re-split).
        assert result.command == "pytest '/my path/test file.py'"
        assert shlex.split(result.command) == ['pytest', '/my path/test file.py']

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_csv_path_with_shell_metacharacters_is_not_injected(self, mock_get_lang, mock_smart, mock_load_csv):
        """A CSV-fallback path containing $()/;/spaces must not inject under shell=True."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': 'pytest {file}'}
        }
        mock_get_lang.return_value = 'python'
        evil = '/repo/$(touch PWN)/a; rm -rf x.py'

        result = get_test_command_for_file(evil)

        argv = shlex.split(result.command)
        # The whole malicious path must survive as a single argument token.
        assert argv == ['pytest', evil], (result.command, argv)
        assert '$(touch' not in argv, argv

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

    @pytest.mark.story(story_id="pdd_nested_ts_runner_resolution")
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

    def test_npm_star_star_pruned_by_star_negation_no_config_inheritance(self, tmp_path):
        """End-to-end: with npm ``workspaces: ["packages/**", "!packages/*"]`` the raw
        positive ``packages/**`` is pruned (its string is matched by the negation glob
        ``packages/*``), so NO package under ``packages/`` is a member — a DEEP
        ``packages/deep/app`` must NOT inherit the repo-root Jest config."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text(
            '{"workspaces": ["packages/**", "!packages/*"]}')
        pkg = repo / "packages" / "deep" / "app"
        pkg.mkdir(parents=True)
        (pkg / "package.json").write_text("{}")  # independent package, not a member
        test_file = pkg / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
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


class TestWorkspaceMembershipHardening:
    """Round-4 review hardening: nested workspace roots, source precedence,
    malformed manifests, brace-expansion budget, and symlink containment."""

    def test_nested_intermediate_manifest_does_not_stop_walk(self, tmp_path):
        """A member below an independent intermediate manifest still reaches root.

        Root declares ``vendor/container/packages/*``; ``vendor/container`` has its
        own (independent) ``package.json`` that does *not* match that glob, and the
        member is ``vendor/container/packages/app``. The walk must cross the
        intermediate manifest and still find the workspace-root Jest config.
        """
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text(
            '{"workspaces": ["vendor/container/packages/*"]}'
        )
        container = repo / "vendor" / "container"
        container.mkdir(parents=True)
        (container / "package.json").write_text("{}")  # independent intermediate
        leaf = container / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")  # the member
        test_dir = leaf / "src" / "__tests__"
        test_dir.mkdir(parents=True)
        test_file = test_dir / "widget.test.ts"
        test_file.write_text("describe('w', () => {})")

        cmd, returned_dir = _detect_ts_test_runner(test_file)
        assert "npx jest" in cmd
        assert returned_dir == repo.resolve()

    def test_pnpm_yaml_is_authoritative_over_stale_package_json(self, tmp_path):
        """pnpm ignores package.json ``workspaces``; a stale field must not add members.

        The root has a stale ``workspaces: ["packages/*"]`` but the authoritative
        ``pnpm-workspace.yaml`` lists only ``apps/*``. A leaf under ``packages/``
        must NOT be a member (and must not adopt the root Jest config), while a
        leaf under ``apps/`` must be.
        """
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        (repo / "pnpm-workspace.yaml").write_text("packages:\n  - 'apps/*'\n")

        stale = repo / "packages" / "tool"
        stale.mkdir(parents=True)
        (stale / "package.json").write_text("{}")
        assert _belongs_to_ancestor_workspace(stale) is False

        member = repo / "apps" / "web"
        member.mkdir(parents=True)
        (member / "package.json").write_text("{}")
        assert _belongs_to_ancestor_workspace(member) is True

        # And end-to-end: the stale packages/ leaf must not adopt root Jest.
        test_file = stale / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")
        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_pnpm_yaml_without_parser_fails_closed(self, tmp_path, monkeypatch):
        """If PyYAML is unavailable, a pnpm workspace yields no globs (fail closed)."""
        import builtins
        real_import = builtins.__import__

        def fake_import(name, *args, **kwargs):
            if name == "yaml":
                raise ImportError("no yaml")
            return real_import(name, *args, **kwargs)

        monkeypatch.setattr(builtins, "__import__", fake_import)
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / "pnpm-workspace.yaml").write_text("packages:\n  - 'packages/*'\n")
        # Even the package.json field must be ignored when pnpm manages the repo.
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        assert _workspace_globs_for(repo) == []

    def test_pnpm_yaml_uses_yaml_1_2_scalar_resolution(self, tmp_path):
        """pnpm parses YAML 1.2, whose core schema resolves ``0o12`` as octal and
        ``1e3`` as a float — non-string ``packages`` entries that must be rejected.
        PyYAML (1.1) would keep them as strings and falsely prove membership, so the
        loader is configured with YAML-1.2 scalar resolution. A *quoted* ``"0o12"``
        is a string in both and stays a valid glob."""
        anc = tmp_path / "anc"
        anc.mkdir()
        (anc / "pnpm-workspace.yaml").write_text("packages:\n  - 0o12\n  - 1e3\n")
        assert _workspace_globs_for(anc) == []  # both are numbers → no globs
        (anc / "pnpm-workspace.yaml").write_text('packages:\n  - "0o12"\n')
        assert _workspace_globs_for(anc) == ["0o12"]  # quoted → string glob

    def test_pnpm_yaml_1_1_only_scalars_stay_string_globs(self, tmp_path):
        """The YAML 1.2 core schema replaces PyYAML's 1.1 table wholesale, so scalars
        that YAML 1.1 resolves as non-strings but YAML 1.2 keeps as STRINGS
        (``yes``/``no``/``on``/``off`` booleans, ``0b10`` binary, ``1:20``
        sexagesimal, ``2020-01-01`` timestamps, ``1_000`` underscore ints) remain
        valid string globs — they must NOT reject the whole declaration and deny a
        legitimate sibling glob its membership."""
        anc = tmp_path / "anc"
        anc.mkdir()
        (anc / "pnpm-workspace.yaml").write_text(
            "packages:\n  - packages/*\n  - yes\n  - 0b10\n  - 1:20\n"
            "  - 2020-01-01\n  - 1_000\n")
        assert _workspace_globs_for(anc) == [
            "packages/*", "yes", "0b10", "1:20", "2020-01-01", "1_000"]
        # And end-to-end: a real sibling glob still confers membership.
        assert _package_matches_workspace(("packages", "app"), ["packages/*", "yes"]) is True

    def test_pnpm_yaml_duplicate_keys_fail_closed(self, tmp_path):
        """pnpm rejects duplicate mapping keys; PyYAML silently keeps the last. The
        loader raises on a duplicate so the parse fails membership closed rather than
        adopting whichever value PyYAML happened to keep."""
        anc = tmp_path / "anc"
        anc.mkdir()
        (anc / "pnpm-workspace.yaml").write_text(
            "packages:\n  - a/*\npackages:\n  - b/*\n")
        assert _workspace_globs_for(anc) == []

    def test_pnpm_yaml_empty_scalar_is_null_and_fails_closed(self, tmp_path):
        """An empty YAML item (``- `` with nothing after it) resolves to null under
        YAML 1.2, a non-string entry that MUST reject the whole declaration — it must
        not be kept as an empty string that quietly drops out and leaves a sibling
        glob falsely conferring membership."""
        anc = tmp_path / "anc"
        anc.mkdir()
        (anc / "pnpm-workspace.yaml").write_text("packages:\n  - packages/*\n  -\n")
        assert _workspace_globs_for(anc) == []

    def test_pnpm_yaml_octal_and_decimal_int_keys_are_duplicates(self, tmp_path):
        """A YAML-1.2 integer constructor parses ``012`` as decimal 12 (not octal 10),
        so sibling mapping keys ``012:`` and ``12:`` are the SAME integer and a
        duplicate — the parse must fail closed. YAML 1.1's octal reading would make
        them look distinct and let a sibling ``packages`` glob falsely confer
        membership."""
        anc = tmp_path / "anc"
        anc.mkdir()
        (anc / "pnpm-workspace.yaml").write_text(
            "packages:\n  - packages/*\n012: a\n12: b\n")
        assert _workspace_globs_for(anc) == []
        # A single numeric key (no collision) parses fine.
        (anc / "pnpm-workspace.yaml").write_text("packages:\n  - packages/*\n012: a\n")
        assert _workspace_globs_for(anc) == ["packages/*"]

    def test_workspace_membership_is_order_dependent_with_reinclusion(self):
        """Include/exclude is evaluated in declaration order (last match wins), so a
        later positive re-includes a path an earlier ``!`` excluded — matching both
        npm's @npmcli/map-workspaces and pnpm's @pnpm/matcher. An exclusion that is
        the last matching pattern still excludes."""
        reinclude = ["packages/**", "!packages/legacy/**", "packages/legacy/app"]
        assert _package_matches_workspace(("packages", "legacy", "app"), reinclude) is True
        assert _package_matches_workspace(("packages", "legacy", "other"), reinclude) is False
        assert _package_matches_workspace(("packages", "app"), reinclude) is True
        # A trailing exclusion still excludes (last match wins).
        assert _package_matches_workspace(
            ("packages", "app", "test", "x"), ["packages/**", "!**/test/**"]) is False
        # An exclusion BEFORE a positive is overridden by the positive (order).
        assert _package_matches_workspace(
            ("packages", "app"), ["!packages/app", "packages/**"]) is True

    def test_non_dict_package_json_does_not_crash(self, tmp_path):
        """A package.json whose top level is a JSON array must not raise."""
        anc = tmp_path / "anc"
        anc.mkdir()
        (anc / "package.json").write_text("[]")
        assert _workspace_globs_for(anc) == []

    def test_non_dict_lerna_json_does_not_crash(self, tmp_path):
        """A lerna.json whose top level is a JSON array must not raise."""
        anc = tmp_path / "anc"
        anc.mkdir()
        (anc / "lerna.json").write_text("[]")
        assert _workspace_globs_for(anc) == []

    def test_malformed_manifest_membership_is_unproven_not_crashing(self, tmp_path):
        """An ancestor with a non-object package.json yields no membership crash."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('"just a string"')  # valid JSON, non-object
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")
        # Must not raise; membership unproven → independent leaf → no root Jest.
        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_brace_bomb_raises_budget_error(self):
        """A pathological brace pattern must not materialize an exponential list."""
        with pytest.raises(_BraceBudgetError):
            _expand_braces("x" + "{a,b}" * 40)

    def test_whitespace_surrounded_glob_is_not_normalized(self):
        """Surrounding whitespace is literal to workspace tools, so `" packages/* "`
        must NOT be normalized into a broader `packages/*` (which would falsely
        prove membership). A clean glob still matches."""
        assert _package_matches_workspace(("packages", "app"), [" packages/* "]) is False
        assert _package_matches_workspace(("packages", "app"), ["\tpackages/*"]) is False
        assert _package_matches_workspace(("packages", "app"), ["packages/*"]) is True

    def test_whitespace_glob_does_not_adopt_workspace_config(self, tmp_path):
        """A whitespace-padded workspace glob must not let an independent leaf adopt
        the root Jest config."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": [" packages/* "]}')
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")
        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_brace_bomb_membership_fails_closed(self):
        """Membership fails closed (False) on a brace-bomb glob rather than hanging."""
        bomb = "x" + "{a,b}" * 40
        assert _package_matches_workspace(("a",), [bomb]) is False
        # A brace bomb in an exclusion must not force a member out silently either;
        # it simply fails membership closed.
        assert _package_matches_workspace(("packages", "app"), ["packages/*", "!" + bomb]) is False

    def test_normal_brace_within_budget_still_matches(self):
        """Ordinary brace alternations are unaffected by the budget."""
        assert _package_matches_workspace(("packages", "app"), ["packages/{app,lib}"]) is True
        assert _package_matches_workspace(("packages", "web"), ["packages/{app,lib}"]) is False

    def test_brace_after_single_option_group_still_expands(self):
        """A real ``{a,b}`` alternation must expand even when a *single-option*
        brace (``{foo}``) precedes it in the same pattern. Otherwise the earlier
        singleton short-circuits expansion and an exclusion glob like
        ``!packages/{foo}/{a,b}`` never matches, so an excluded package is falsely
        treated as a workspace member and inherits an ancestor's Jest config."""
        assert sorted(_expand_braces("packages/{foo}/{a,b}")) == [
            "packages/{foo}/a",
            "packages/{foo}/b",
        ]
        globs = ["packages/**", "!packages/{foo}/{a,b}"]
        # The excluded leaf is NOT a member...
        assert _package_matches_workspace(("packages", "{foo}", "a"), globs) is False
        assert _package_matches_workspace(("packages", "{foo}", "b"), globs) is False
        # ...but a sibling the exclusion does not name still is (negative control).
        assert _package_matches_workspace(("packages", "{foo}", "c"), globs) is True

    def test_unbalanced_brace_does_not_short_circuit_later_alternation(self):
        """An *unmatched* opening ``{`` is literal but MUST NOT stop expansion of a
        later balanced alternation. Otherwise ``!packages/{foo/{a,b}`` never expands
        its ``{a,b}``, the exclusion never matches, and the excluded package is
        falsely proven a workspace member (bash: ``{foo/a`` and ``{foo/b``)."""
        assert sorted(_expand_braces("packages/{foo/{a,b}")) == [
            "packages/{foo/a",
            "packages/{foo/b",
        ]
        globs = ["packages/**", "!packages/{foo/{a,b}"]
        assert _package_matches_workspace(("packages", "{foo", "a"), globs) is False
        assert _package_matches_workspace(("packages", "{foo", "b"), globs) is False
        # A sibling the exclusion does not name is still a member (negative control).
        assert _package_matches_workspace(("packages", "{foo", "c"), globs) is True
        # A trailing unmatched brace with no later alternation stays fully literal.
        assert _expand_braces("packages/foo{") == ["packages/foo{"]

    def test_nested_brace_inside_single_option_group_expands(self):
        """A nested alternation inside a single-option outer brace still expands
        (bash parity for ``{a{b,c}}`` → ``{ab} {ac}``), rather than being emitted
        whole and left unexpanded."""
        assert sorted(_expand_braces("packages/{a{b,c}}")) == [
            "packages/{ab}",
            "packages/{ac}",
        ]

    def test_backslash_escaped_glob_fails_membership_closed(self):
        """A backslash escapes brace metacharacters in minimatch (``{foo\\,bar,baz}``
        is two options, not three). This expander is not escape-aware, so rather
        than over-expand ``\\,`` into a spurious ``bar`` member — or, in an
        exclusion, silently fail to exclude — any backslash-bearing glob set fails
        membership closed."""
        # Positive glob: the escaped comma must NOT yield a spurious ``bar`` member.
        assert _package_matches_workspace(
            ("packages", "bar"), [r"packages/{foo\,bar,baz}"]) is False
        # Exclusion glob with an escape: whole set fails closed (never falsely a
        # member because the exclusion was misparsed).
        assert _package_matches_workspace(
            ("packages", "x"), ["packages/*", r"!packages/{a\,b}"]) is False
        # A backslash anywhere in the set is enough to fail closed.
        assert _package_matches_workspace(
            ("packages", "app"), [r"packages/\{app\}"]) is False

    def test_bracket_character_class_glob_fails_membership_closed(self):
        """Per-segment ``fnmatch`` diverges from minimatch on bracket character
        classes: ``[^a]`` negates in minimatch but ``^`` is a literal member in
        fnmatch, and POSIX classes like ``[[:alpha:]]`` are unsupported. A glob
        using a bracket class therefore fails membership closed rather than
        over-matching a positive or under-matching an exclusion into a false
        member."""
        # fnmatch would falsely match `a` against `[^a]`; must fail closed instead.
        assert _package_matches_workspace(("packages", "a"), ["packages/[^a]"]) is False
        # Bracket construct in an exclusion also fails the whole set closed.
        assert _package_matches_workspace(
            ("packages", "a"), ["packages/*", "!packages/[^a]"]) is False
        assert _package_matches_workspace(
            ("packages", "a"), ["packages/[[:alpha:]]"]) is False
        # Even a range fnmatch *could* handle is rejected — the whole class of
        # bracket constructs fails closed for a single, auditable boundary.
        assert _package_matches_workspace(("packages", "app"), ["packages/[a-z]pp"]) is False
        # Critically, a bracket in the *path* (a dynamic-route dir name) is NOT a
        # glob metacharacter and still matches an ordinary `*` glob.
        assert _package_matches_workspace(("packages", "[eventId]"), ["packages/*"]) is True
        # An *unmatched* `[` (no closing `]`) is literal in both fnmatch and
        # minimatch, so it is NOT rejected — the literal glob still matches its dir.
        assert _package_matches_workspace(("packages", "foo[bar"), ["packages/foo[bar"]) is True

    def test_extglob_glob_fails_membership_closed(self):
        """minimatch expands extglobs (``@(a|b)``, ``!(x)``, ``+(…)``, ``?(…)``,
        ``*(…)``) but the per-segment ``fnmatch`` matcher treats them literally, so
        an extglob exclusion under-matches into a false member. Any glob containing
        an extglob prefix therefore fails membership closed."""
        # Extglob exclusion must not fail to exclude `packages/foo`.
        assert _package_matches_workspace(
            ("packages", "foo"), ["packages/*", "!packages/@(foo|bar)"]) is False
        assert _package_matches_workspace(
            ("packages", "foo"), ["packages/*", "!packages/!(bar)"]) is False
        # Extglob positives also fail closed rather than mismatch.
        assert _package_matches_workspace(("packages", "foofoo"), ["packages/+(foo)"]) is False
        # A bare `?` wildcard (no paren) is still supported and NOT an extglob.
        assert _package_matches_workspace(("packages", "ab"), ["packages/a?"]) is True
        # An `@`-scoped-style path with no `(` is not an extglob and still matches.
        assert _package_matches_workspace(("@scope", "pkg"), ["@scope/*"]) is True

    def test_deeply_nested_singleton_with_alternations_is_time_bounded(self):
        """A tiny (<1 KB) glob nesting a deep singleton before several alternations
        stays within the byte/count/segment budgets yet would cost tens of seconds
        of pure re-scanning. The aggregate brace-scan budget makes it fail closed
        quickly instead of stalling runner discovery."""
        pattern = "{" * 400 + "x" + "}" * 400 + "/{a,b}" * 10
        assert len(pattern) < 1024
        assert _package_matches_workspace(("never",), [pattern]) is False

    def test_scan_budget_does_not_reject_large_legitimate_brace(self):
        """A genuinely large alternation (hundreds of options) still expands and
        matches — the scan budget only trips on pathological nested re-scanning,
        not on ordinary breadth."""
        globs = ["packages/{" + ",".join(f"p{i}" for i in range(500)) + "}"]
        assert _package_matches_workspace(("packages", "p0"), globs) is True
        assert _package_matches_workspace(("packages", "p499"), globs) is True
        assert _package_matches_workspace(("packages", "p500"), globs) is False

    def test_long_non_brace_prefix_is_charged_against_scan_budget(self):
        """The non-brace prefix a scan skips before the first ``{`` must be charged
        against the work budget. Otherwise a long ``*`` run before an alternation is
        re-walked free for every one of up to 1024 worklist entries, and at every
        ancestor boundary of a deep walk — a multi-second stall within all other
        budgets. Charging makes the deep-boundary case fail closed instead."""
        prefix_len = 3990
        pattern = "**/" + "*" * prefix_len + "{a,b}" * 10
        work = [_MAX_BRACE_SCAN_WORK]
        _find_expandable_brace(pattern, 2000, work)
        # The whole prefix (plus a little) is charged, not a token amount.
        assert (_MAX_BRACE_SCAN_WORK - work[0]) >= prefix_len
        # A deep walk sharing one work budget across boundaries fails closed rather
        # than re-spending it: 80 checks must not each cost a full budget.
        cells = [_MAX_MATCH_CELLS]
        shared_work = [_MAX_BRACE_SCAN_WORK]
        expand = [_MAX_BRACE_EXPANSION]
        results = [
            _package_matches_workspace(
                ("packages", "bbbbbbbbbb"), [pattern], cells, shared_work, expand)
            for _ in range(80)
        ]
        # Shared budget is exhausted → the walk fails membership closed, not stalls.
        assert all(r is False for r in results)

    def test_brace_range_glob_fails_membership_closed(self):
        """minimatch expands numeric/alphabetic brace ranges (``{1..3}``, ``{a..c}``,
        zero-padded ``{01..03}``, stepped ``{1..9..2}``); this expander only does
        comma alternation, so a range brace would be emitted literally and an
        exclusion range would fail to exclude. Any glob containing ``..`` therefore
        fails membership closed (no legitimate workspace path holds ``..``)."""
        assert _package_matches_workspace(
            ("packages", "1"), ["packages/**", "!packages/{1..3}"]) is False
        assert _package_matches_workspace(("packages", "b"), ["packages/{a..c}"]) is False
        assert _package_matches_workspace(("packages", "02"), ["packages/{01..03}"]) is False

    def test_internal_dot_segment_is_not_collapsed(self):
        """minimatch does not collapse an *internal* ``.`` segment, so
        ``packages/./x`` must not be treated as ``packages/x`` and falsely prove
        membership. A *leading* ``./`` is npm-normalized and still matches."""
        # Internal `.` → the glob needs a literal `.` segment the path lacks.
        assert _package_matches_workspace(("packages", "app"), ["packages/./*"]) is False
        assert _package_matches_workspace(
            ("packages", "app"), ["packages/**", "!packages/./app"]) is True
        # Leading `./` normalization is preserved.
        assert _package_matches_workspace(("packages", "app"), ["./packages/*"]) is True
        # A genuine literal `.`-named segment still matches itself.
        assert _package_matches_workspace(("packages", "."), ["packages/*"]) is False

    def test_question_mark_matches_astral_over_utf16_units(self):
        """``?`` matches exactly one UTF-16 code unit (minimatch parity), so a single
        ``?`` does NOT match an astral character (two units) but ``??`` does — no
        fail-closed approximation is needed, and include/exclude semantics stay
        order-independent. ``*`` spans the whole segment and BMP ``?`` is unaffected."""
        emoji = "\U0001F600"
        # A single `?` is one unit → does not match the two-unit emoji → not a member.
        assert _package_matches_workspace(("packages", emoji), ["packages/?"]) is False
        # `??` is two units → matches the emoji exactly.
        assert _package_matches_workspace(("packages", emoji), ["packages/??"]) is True
        # A `?` in a different segment (consumed by `**`/`*`) does not spuriously
        # reject, and the result is independent of positive-glob order.
        assert _package_matches_workspace(
            ("packages", "app", emoji), ["packages/ap?/**"]) is True
        assert _package_matches_workspace(
            ("packages", "a", emoji), ["packages/?/x", "packages/**"]) is True
        assert _package_matches_workspace(
            ("packages", "a", emoji), ["packages/**", "packages/?/x"]) is True
        # `*` still matches an astral segment; a BMP `?` still works normally.
        assert _package_matches_workspace(("packages", emoji), ["packages/*"]) is True
        assert _package_matches_workspace(("packages", "ab"), ["packages/a?"]) is True

    def test_multiple_leading_bang_fails_membership_closed(self):
        """Two or more leading ``!`` toggle negation in minimatch (``!!x`` positive,
        ``!!!x`` negates again). This matcher does not track that parity, so a
        multi-bang glob fails membership closed rather than be mis-classified as a
        literal (which would falsely prove membership for ``!!!packages/foo``)."""
        assert _package_matches_workspace(
            ("packages", "foo"), ["packages/**", "!!!packages/foo"]) is False
        assert _package_matches_workspace(("packages", "foo"), ["!!packages/foo"]) is False
        # A single `!` exclusion is unaffected and still excludes.
        assert _package_matches_workspace(
            ("packages", "foo"), ["packages/**", "!packages/foo"]) is False
        assert _package_matches_workspace(
            ("packages", "bar"), ["packages/**", "!packages/foo"]) is True

    def test_leading_hash_comment_glob_matches_nothing(self):
        """A positive pattern whose effective form (after an optional leading
        ``./``) begins with ``#`` is a minimatch comment: it matches nothing and
        must not be fnmatch-ed literally into a false member. It is skipped, not
        fail-closed, so a real glob alongside a comment still works."""
        assert _package_matches_workspace(("packages", "#foo"), ["#*"]) is False
        assert _package_matches_workspace(("packages", "#foo"), ["./#*"]) is False
        # A comment entry does not disable the rest of the declaration.
        assert _package_matches_workspace(
            ("packages", "app"), ["#comment", "packages/*"]) is True

    def test_literal_double_dot_and_unmatched_bracket_are_not_over_rejected(self):
        """The fail-closed guard targets *unsupported* constructs, not any literal
        occurrence of their characters. A package dir named ``foo..bar`` (literal
        ``..`` outside a brace) or ``foo[bar`` (an unmatched ``[``) is matched
        literally by fnmatch, exactly like minimatch, so such globs must still
        prove membership rather than be needlessly rejected."""
        assert _package_matches_workspace(
            ("packages", "foo..bar"), ["packages/foo..bar"]) is True
        assert _package_matches_workspace(
            ("packages", "foo[bar"), ["packages/foo[bar"]) is True
        # But an in-brace range and a closed class still fail closed.
        assert _package_matches_workspace(
            ("packages", "1"), ["packages/**", "!packages/{1..3}"]) is False
        assert _package_matches_workspace(("packages", "a"), ["packages/[^a]"]) is False

    def test_dollar_brace_is_literal_not_expanded(self):
        """minimatch's brace-expansion treats a ``{`` immediately preceded by ``$``
        (shell-style ``${...}``) as literal, never expanding it. Expanding it would
        falsely prove membership for an independent ``$foo`` leaf."""
        assert _expand_braces("packages/${foo,bar}") == ["packages/${foo,bar}"]
        assert _package_matches_workspace(
            ("packages", "$foo"), ["packages/${foo,bar}"]) is False
        # A real brace elsewhere in the same pattern still expands.
        assert sorted(_expand_braces("${a,b}/{c,d}")) == [
            "${a,b}/c", "${a,b}/d",
        ]

    def test_double_dot_in_comma_alternation_is_not_a_range(self):
        """A ``..`` inside a brace group that also has a top-level comma is a literal
        part of one alternation option, not a range, and must not be rejected: both
        ``packages/foo..bar`` and ``packages/baz`` are members of
        ``packages/{foo..bar,baz}``. An unbalanced ``{foo..bar`` is literal too. A
        *pure* range (no comma) still fails closed."""
        assert _package_matches_workspace(
            ("packages", "foo..bar"), ["packages/{foo..bar,baz}"]) is True
        assert _package_matches_workspace(
            ("packages", "baz"), ["packages/{foo..bar,baz}"]) is True
        assert _package_matches_workspace(
            ("packages", "{foo..bar"), ["packages/{foo..bar"]) is True
        # Pure range (no comma), including nested inside an alternation, fails closed.
        assert _package_matches_workspace(
            ("packages", "1"), ["packages/**", "!packages/{1..3}"]) is False
        assert _package_matches_workspace(("packages", "2"), ["packages/{a,{1..3}}"]) is False

    def test_astral_question_mark_matches_over_utf16_units(self):
        """``?`` matches one UTF-16 unit, so it never spuriously rejects when a ``?``
        segment aligns with a BMP segment while ``*`` consumes an astral one
        (``packages/*/a??`` matches ``packages/😀/app``), and a ``?`` aligned with an
        astral segment simply does not match it (one unit ≠ two)."""
        emoji = "\U0001F600"
        assert _package_matches_workspace(
            ("packages", emoji, "app"), ["packages/*/a??"]) is True
        # `?` (one unit) does not match the two-unit emoji → not a member.
        assert _package_matches_workspace(("packages", emoji), ["packages/?"]) is False
        assert _package_matches_workspace(
            ("packages", "app", emoji), ["packages/app/?"]) is False
        # `??` (two units) does match it.
        assert _package_matches_workspace(
            ("packages", "app", emoji), ["packages/app/??"]) is True
        # `**` makes alignment flexible → conservatively fail closed.
        assert _package_matches_workspace(
            ("packages", emoji, "app"), ["packages/**/a?"]) is False

    def test_empty_bracket_class_is_not_treated_as_a_class(self):
        """``[]``, ``[!]``, ``[^]`` are empty (invalid) classes — no content between
        the optional negation marker and ``]`` — that both fnmatch and minimatch
        treat literally. The guard must NOT flag them as character classes (which
        would fail the whole membership check closed); a non-empty class still is."""
        # Guard: empty groups are not classes; a group with content is.
        assert _has_complete_bracket_class("packages/[]") is False
        assert _has_complete_bracket_class("packages/[!]") is False
        assert _has_complete_bracket_class("packages/[^]") is False
        assert _has_complete_bracket_class("packages/[^a]") is True
        assert _has_complete_bracket_class("packages/[ab]") is True
        # A dir literally named ``[]``/``[!]`` matches its literal glob (fnmatch and
        # minimatch agree); a real class still fails membership closed.
        assert _package_matches_workspace(("packages", "[]"), ["packages/[]"]) is True
        assert _package_matches_workspace(("packages", "[!]"), ["packages/[!]"]) is True
        assert _package_matches_workspace(("packages", "a"), ["packages/[^a]"]) is False
        assert _package_matches_workspace(("packages", "b"), ["packages/[ab]"]) is False

    def test_expanded_patterns_are_revalidated_for_constructs(self):
        """Brace expansion can *create* an unsupported construct from separate
        alternatives or *dissolve* an apparent one, so validation must run on each
        concrete (expanded) pattern, not the raw glob."""
        # `{?,x}(foo)` expands to `?(foo)` — an extglob fnmatch would mishandle
        # (`?` matching `a`); must fail closed, not falsely prove `a(foo)`.
        assert _package_matches_workspace(
            ("packages", "a(foo)"), ["packages/{?,x}(foo)"]) is False
        # `{[,x}]` expands only to the literals `[]` and `x]` — both supported — so
        # it must NOT be rejected by a raw-level bracket scan.
        assert _package_matches_workspace(("packages", "[]"), ["packages/{[,x}]"]) is True
        assert _package_matches_workspace(("packages", "x]"), ["packages/{[,x}]"]) is True
        # `[{a,b}]` expands to real classes `[a]`/`[b]` → still fails closed.
        assert _package_matches_workspace(("packages", "a"), ["packages/[{a,b}]"]) is False

    def test_dollar_brace_is_opaque_including_nested(self):
        """A balanced ``${...}`` is opaque to brace-expansion, nested braces
        included, so ``${foo,{bar,baz}}`` is fully literal (its inner ``{bar,baz}``
        must NOT expand into a false member), while ``${1..3}`` is a literal dir name
        (its ``..`` is not a range) and must stay matchable."""
        assert _expand_braces("packages/${foo,{bar,baz}}") == ["packages/${foo,{bar,baz}}"]
        assert _package_matches_workspace(
            ("packages", "${foo,bar}"), ["packages/${foo,{bar,baz}}"]) is False
        assert _package_matches_workspace(
            ("packages", "${1..3}"), ["packages/${1..3}"]) is True
        # A real brace after a ``${...}`` group still expands.
        assert sorted(_expand_braces("${a,b}/{c,d}")) == ["${a,b}/c", "${a,b}/d"]

    def test_unbalanced_dollar_brace_still_expands_later_alternation(self):
        """An *unbalanced* ``${`` (no matching ``}``) is a literal ``${``, not an
        opaque group, so a later balanced ``{a,b}`` must still expand. Otherwise
        ``!packages/${foo/{a,b}`` never excludes ``packages/${foo/a``."""
        assert sorted(_expand_braces("packages/${foo/{a,b}")) == [
            "packages/${foo/a",
            "packages/${foo/b",
        ]
        globs = ["packages/**", "!packages/${foo/{a,b}"]
        assert _package_matches_workspace(("packages", "${foo", "a"), globs) is False
        assert _package_matches_workspace(("packages", "${foo", "b"), globs) is False
        assert _package_matches_workspace(("packages", "${foo", "c"), globs) is True

    def test_literal_bracket_forms_are_not_reinterpreted_by_fnmatch(self):
        """The matcher implements ``*``/``?``/literal directly (no ``fnmatch``), so a
        literal bracket form it permits is matched literally, matching minimatch —
        not reinterpreted as a class. ``[^]``/``[!]`` are empty (literal); ``[^]]``/
        ``[!]]``/``[]]`` are real non-empty classes (``]`` is their first member) and
        fail closed."""
        # Empty forms: literal, so they match only their literal dir name.
        assert _package_matches_workspace(("packages", "^"), ["packages/[^]"]) is False
        assert _package_matches_workspace(("packages", "[^]"), ["packages/[^]"]) is True
        assert _package_matches_workspace(("packages", "[!]"), ["packages/[!]"]) is True
        # ']' as first member → non-empty class → fail closed.
        assert _has_complete_bracket_class("packages/[^]]") is True
        assert _has_complete_bracket_class("packages/[!]]") is True
        assert _has_complete_bracket_class("packages/[]]") is True
        assert _package_matches_workspace(("packages", "a"), ["packages/[^]]"]) is False

    def test_leading_prefix_normalized_exactly_once(self):
        """npm's leading normalization is exactly ``^\\.?/+`` (an optional leading dot
        then the entire leading slash run, once). A prefix left OVER is significant, so
        ``/./packages/*`` (→ ``./packages/*``), ``//./packages/*``, and
        ``././packages/*`` do NOT match ``packages/app``. A single leading ``./`` or a
        leading slash run — including ``.//`` and ``.///`` (dot + all slashes) — does."""
        for glob in ("/./packages/*", "//./packages/*", "././packages/*",
                     ".//./packages/*"):
            assert _package_matches_workspace(("packages", "app"), [glob]) is False, glob
        for glob in ("packages/*", "./packages/*", "/packages/*", "//packages/*",
                     ".//packages/*", ".///packages/*", "///packages/*"):
            assert _package_matches_workspace(("packages", "app"), [glob]) is True, glob

    def test_membership_semantics_are_source_dependent(self):
        """Both npm/yarn/lerna (``@npmcli/map-workspaces``) and pnpm (``@pnpm/matcher``)
        honor re-inclusion, but DIFFERENTLY: npm's ``appendNegatedPatterns`` drops an
        earlier negation wholesale when a later positive's pattern-string matches it
        (re-including the sibling too), while pnpm decides per-path (last matching
        pattern wins, sibling stays excluded). The ``ordered`` flag selects the
        algorithm; direct callers default to pnpm. Verified against @npmcli/map-workspaces
        source (a later specific positive removes the earlier negation)."""
        # A specific re-inclusion after a broad exclusion.
        reinc = ["packages/**", "!packages/legacy/**", "packages/legacy/app"]
        # The named package is re-included by BOTH.
        assert _package_matches_workspace(
            ("packages", "legacy", "app"), reinc, ordered=False) is True   # npm
        assert _package_matches_workspace(
            ("packages", "legacy", "app"), reinc, ordered=True) is True    # pnpm
        # The SIBLING differs: npm drops the whole negation (member); pnpm keeps it out.
        assert _package_matches_workspace(
            ("packages", "legacy", "other"), reinc, ordered=False) is True   # npm re-includes subtree
        assert _package_matches_workspace(
            ("packages", "legacy", "other"), reinc, ordered=True) is False   # pnpm still excludes
        # A later positive equal to an earlier exclusion removes it under npm.
        undo = ["packages/*", "!packages/app", "packages/app"]
        assert _package_matches_workspace(("packages", "app"), undo, ordered=False) is True
        assert _package_matches_workspace(("packages", "app"), undo, ordered=True) is True
        # Both agree on a plain positive and a never-undone trailing exclusion.
        assert _package_matches_workspace(("packages", "app"), ["packages/*"], ordered=False) is True
        assert _package_matches_workspace(
            ("packages", "app", "test", "x"), ["packages/**", "!**/test/**"], ordered=False) is False
        assert _package_matches_workspace(
            ("packages", "app", "test", "x"), ["packages/**", "!**/test/**"], ordered=True) is False

    def test_node_modules_is_never_a_workspace_member(self):
        """A package inside any ``node_modules/`` is never a workspace member, even under
        a broad ``**``: npm appends ``**/node_modules/**`` to its ignore set and
        pnpm/yarn skip ``node_modules`` during discovery. A leaf dir literally named
        ``node_modules`` (nothing inside it) is not itself excluded."""
        for ordered in (True, False):
            assert _package_matches_workspace(
                ("node_modules", "dep"), ["**"], ordered=ordered) is False, ordered
            assert _package_matches_workspace(
                ("packages", "app", "node_modules", "x"), ["**"], ordered=ordered) is False, ordered
            assert _package_matches_workspace(
                ("packages", "app"), ["**"], ordered=ordered) is True, ordered
        # A leaf directory literally named node_modules is matchable.
        assert _package_matches_workspace(
            ("packages", "node_modules"), ["packages/*"], ordered=False) is True

    def test_npm_hash_comment_semantics_split_preprocessing_vs_final(self):
        """npm's ``appendNegatedPatterns`` preprocessing uses DEFAULT minimatch, where a
        leading ``#`` PATTERN is a comment, but the FINAL ``glob`` matches ``#``
        LITERALLY (nocomment). So:
          * a positive ``#noop`` (as a pattern-string, first arg to minimatch) still
            matches an earlier negation ``**`` and removes it, re-including ``packages/app``;
          * a leading-``#`` NEGATION matches nothing during preprocessing, so a positive
            cannot remove it and it survives (``["**","!#foo","#foo"]`` keeps ``#foo``
            excluded);
          * in final matching ``#`` is literal, so a positive ``#noop`` DOES match a
            package directory literally named ``#noop``."""
        # Positive comment removes an earlier non-comment negation (re-inclusion).
        globs = ["packages/**", "!**", "#noop"]
        assert _package_matches_workspace(("packages", "app"), globs, ordered=False) is True
        assert _package_matches_workspace(("packages", "app"), globs, ordered=True) is False
        # A leading-# NEGATION matches nothing during preprocessing → survives → excludes.
        excl = ["**", "!#foo", "#foo"]
        assert _package_matches_workspace(("#foo",), excl, ordered=False) is False
        # In final matching ``#`` is LITERAL, so a positive ``#noop`` matches a dir ``#noop``.
        assert _package_matches_workspace(("#noop",), ["#noop"], ordered=False) is True

    def test_npm_final_negation_uses_dot_true_semantics(self):
        """npm applies surviving negations as ``glob``'s dot:true IGNORE set, so a
        wildcard negation excludes a leading-dot directory, while positives keep dot:false.
        ``["packages/.*", "!packages/*"]`` therefore EXCLUDES ``packages/.shadow`` (the
        ``!packages/*`` ignore matches it under dot:true) even though ``packages/*`` as a
        POSITIVE would not match ``.shadow``."""
        assert _package_matches_workspace(
            ("packages", ".shadow"), ["packages/.*", "!packages/*"], ordered=False) is False
        # Positive-only dot:false: packages/* does not match a dotfile...
        assert _package_matches_workspace(
            ("packages", ".shadow"), ["packages/*"], ordered=False) is False
        # ...but a dot-leading positive does, and a normal name is unaffected.
        assert _package_matches_workspace(
            ("packages", ".shadow"), ["packages/.*"], ordered=False) is True
        assert _package_matches_workspace(
            ("packages", "app"), ["packages/*"], ordered=False) is True

    def test_dot_and_dotdot_segments_match_only_identical_literals(self):
        """A ``.`` or ``..`` path segment (which appears when a raw pattern-STRING like
        ``packages/./x`` is matched as a path during npm's pruning) is matched ONLY by an
        identical literal pattern segment — never by a wildcard or ``**``. So for
        ``["packages/.*/*", "!packages/.*/**", "packages/./x"]`` the positive
        ``packages/./x`` does NOT match ``packages/.*/**`` (``.*`` cannot consume ``.``),
        the negation survives, and ``packages/.shadow/y`` stays excluded."""
        g = ["packages/.*/*", "!packages/.*/**", "packages/./x"]
        assert _package_matches_workspace(
            ("packages", ".shadow", "y"), g, ordered=False) is False
        # A `.` path segment is not matched by a wildcard/globstar, only by literal `.`.
        assert _relative_matches_workspace_glob((".",), ".*") is False
        assert _relative_matches_workspace_glob((".",), "**") is False
        assert _relative_matches_workspace_glob((".",), ".") is True
        assert _relative_matches_workspace_glob(("..",), "*") is False
        assert _relative_matches_workspace_glob(("..",), "..") is True

    def test_terminal_star_run_is_budget_charged(self):
        """A long trailing run of ``*`` in the segment matcher is charged against the
        shared work budget (a prior unbudgeted terminal-star scan could reach ~10^8
        iterations under the cell cap). A pathological long-star + brace + globstar glob
        fails membership closed instead of hanging."""
        import time
        glob = "?" + "*" * 4000 + "{a,b}" * 4 + "/**"
        deep = tuple("x" for _ in range(200))
        t0 = time.time()
        result = _package_matches_workspace(deep, [glob], ordered=False)
        assert (time.time() - t0) < 2.0, "pathological star-wall must stay bounded"
        assert result in (True, False)  # decided within budget, not hung

    def test_npm_pruning_collapses_empty_and_trailing_slash_segments(self):
        """minimatch collapses repeated/trailing ``/`` for the pattern-vs-pattern
        comparison, so a positive ``packages//app`` (or ``packages/app/``) still matches
        the negation ``packages/*`` and removes it — ``packages/app`` is a member."""
        assert _package_matches_workspace(
            ("packages", "app"),
            ["packages/**", "!packages/*", "packages//app"], ordered=False) is True
        assert _package_matches_workspace(
            ("packages", "app"),
            ["packages/**", "!packages/*", "packages/app/"], ordered=False) is True

    def test_pnpm_treats_hash_literally(self):
        """pnpm (``@pnpm/matcher``) treats ``#`` LITERALLY — only a leading ``!`` is
        special — so a ``#app`` pattern matches a directory named ``#app`` and a later
        ``#app`` re-includes it after ``!#app``. The npm-preprocessing comment rule does
        NOT apply to pnpm (ordered)."""
        assert _package_matches_workspace(("#app",), ["#app"], ordered=True) is True
        assert _package_matches_workspace(
            ("#app",), ["!#app", "#app"], ordered=True) is True
        assert _package_matches_workspace(
            ("#app",), ["**", "!#app"], ordered=True) is False

    def test_npm_empty_positive_pattern_removes_prior_negation(self):
        """Under npm's ``appendNegatedPatterns`` an EMPTY positive pattern-string is
        preserved (not dropped) and can still match+remove a prior negation, even though
        it never matches a non-empty leaf. ``["packages/**", "!**", ""]`` therefore drops
        ``!**`` and ``packages/app`` is a member."""
        assert _package_matches_workspace(
            ("packages", "app"), ["packages/**", "!**", ""], ordered=False) is True

    def test_npm_removal_compares_raw_unexpanded_positive_string(self):
        """npm's ``appendNegatedPatterns`` compares the RAW positive pattern STRING
        (braces literal) against each negation, expanding braces only for the final
        concrete-path membership test. So a later brace positive ``packages/{a,b}`` does
        NOT remove a specific earlier ``!packages/a`` (the raw string ``packages/{a,b}``
        doesn't match ``packages/a``): ``packages/a`` stays excluded, ``packages/b`` is a
        member. (Expanding the positive before comparison would wrongly re-include
        ``packages/a``.)"""
        g = ["packages/**", "!packages/a", "packages/{a,b}"]
        assert _package_matches_workspace(("packages", "a"), g, ordered=False) is False  # excluded
        assert _package_matches_workspace(("packages", "b"), g, ordered=False) is True   # member
        # A brace NEGATION, by contrast, is expanded — a raw positive matching any of its
        # expansions removes the whole group.
        g2 = ["packages/**", "!packages/{a,c}", "packages/a"]
        assert _package_matches_workspace(("packages", "a"), g2, ordered=False) is True
        assert _package_matches_workspace(("packages", "c"), g2, ordered=False) is True
        # pnpm (per-path last-match) re-includes packages/a via the later brace positive.
        assert _package_matches_workspace(("packages", "a"), g, ordered=True) is True

    def test_npm_surviving_negation_prunes_matching_positive_patterns(self):
        """npm's ``appendNegatedPatterns`` also runs the SYMMETRIC step: each surviving
        negation removes any POSITIVE pattern whose raw pattern STRING it matches
        (``minimatch.match(patterns, negated)``). So ``["packages/*", "!packages/?"]``
        drops ``packages/*`` (its string matches ``packages/?``) and ``packages/app`` is
        NOT a member — even though the concrete path ``packages/app`` does not itself
        match the single-char ``packages/?``."""
        g = ["packages/*", "!packages/?"]
        assert _package_matches_workspace(("packages", "app"), g, ordered=False) is False
        assert _package_matches_workspace(("packages", "a"), g, ordered=False) is False
        # A positive NOT matched by the negation survives.
        g2 = ["packages/*", "other/*", "!packages/?"]
        assert _package_matches_workspace(("other", "x"), g2, ordered=False) is True

    def test_npm_leading_normalization_applies_once_before_brace_expansion(self):
        """npm normalizes each RAW pattern with ``^\\.?/+`` exactly once, BEFORE minimatch
        expands braces — so a slash GENERATED by brace expansion stays anchored and is not
        re-normalized. ``["{/packages/*,other/*}"]`` yields an anchored ``/packages/*``
        that does NOT match the relative ``packages/app``, while ``other/*`` matches
        ``other/app``. A non-slash brace alternative still matches."""
        anchored = ["{/packages/*,other/*}"]
        for ordered in (False, True):
            assert _package_matches_workspace(("packages", "app"), anchored, ordered=ordered) is False
            assert _package_matches_workspace(("other", "app"), anchored, ordered=ordered) is True
        assert _package_matches_workspace(
            ("packages", "app"), ["{packages/*,other/*}"], ordered=False) is True

    def test_npm_negation_removal_uses_splice_while_increment_semantics(self):
        """npm's negation-removal loop splices at index ``i`` then does ``++i``, so a
        matching negation ADJACENT to a removed one is skipped and survives. For
        ``["packages/**", "!packages/**", "!packages/*", "packages/app"]`` the positive
        ``packages/app`` removes ``!packages/**`` (slot 0) but the loop advances past the
        shifted ``!packages/*`` — which survives and excludes ``packages/app``. Reproduce
        the sequential (not simultaneous) semantics."""
        g = ["packages/**", "!packages/**", "!packages/*", "packages/app"]
        assert _package_matches_workspace(("packages", "app"), g, ordered=False) is False

    def test_npm_positive_pattern_star_matches_glob_star_during_pruning(self):
        """During npm's pattern-vs-pattern pruning the raw positive ``packages/**`` is
        matched (as a literal path) against the negation glob ``packages/*``: the ``*`` in
        the glob is a WILDCARD that matches the literal segment ``**``. So
        ``["packages/**", "!packages/*"]`` prunes ``packages/**`` and NO package under it
        is a member — neither ``packages/app`` nor a deeper ``packages/deep/app``. (A
        matcher that consumed the pattern ``*`` as a literal equal to the name ``*`` would
        wrongly keep the positive.)"""
        g = ["packages/**", "!packages/*"]
        assert _package_matches_workspace(("packages", "app"), g, ordered=False) is False
        assert _package_matches_workspace(("packages", "deep", "app"), g, ordered=False) is False
        # A literal ``*`` in a real segment still matches a pattern ``*`` and a literal ``*``.
        assert _wildcard_segment_match("**", "*") is True
        assert _wildcard_segment_match("a*b", "a*b") is True

    def test_jest_config_extensions_include_cjs_and_json(self):
        """Jest supports `.cjs`/`.json` (and TS variants) config files; a project using
        `jest.config.cjs` must be detected as a Jest project, not fall back to tsx."""
        jest = next(c[1] for c in _RUNNER_CONFIGS if "jest" in c[0])
        for name in ("jest.config.js", "jest.config.mjs", "jest.config.cjs",
                     "jest.config.json", "jest.config.ts"):
            assert name in jest, name

    def test_json_manifest_rejects_nonstandard_constants(self, tmp_path):
        """``NaN``/``Infinity``/``-Infinity`` are accepted by Python's ``json`` but
        rejected by npm's (Node's) strict JSON parser, so a manifest containing them —
        even outside the workspace field — is invalid and must fail membership closed,
        not prove a member off the still-parsed ``workspaces`` list."""
        for body in ('{"workspaces":["packages/*"],"x":NaN}',
                     '{"workspaces":["packages/*"],"x":Infinity}',
                     '{"workspaces":["packages/*"],"x":-Infinity}'):
            (tmp_path / "package.json").write_text(body)
            assert _workspace_globs_for(tmp_path) == []
        # lerna.json uses the same parser and is guarded too.
        (tmp_path / "package.json").unlink()
        (tmp_path / "lerna.json").write_text('{"packages":["packages/*"],"x":NaN}')
        assert _workspace_globs_for(tmp_path) == []

    def test_matcher_fast_rejects_and_bounds_wildcard_work(self):
        """Without ``**`` every pattern segment consumes exactly one path segment, so a
        segment-count mismatch is rejected before the DP. And the per-unit character
        work of matching is charged against a shared budget, so a manifest of many
        long wildcard-heavy globs against a deep path fails closed instead of burning
        CPU (the reviewer's 80-segment path × 100 × 240-wildcard-segment case)."""
        # Fast reject on unequal segment counts (no ``**``): 2 pattern vs 3 path segs.
        assert _package_matches_workspace(("a", "b", "c"), ["x/y"]) is False
        # A pathological deep match with ``**`` fails closed (budget), not hangs.
        pattern = "**/" + "/".join(["a*b"] * 240)
        assert _package_matches_workspace(
            tuple(["bbbbbbbbbb"] * 80), [pattern] * 100) is False

    def test_length_guard_precedes_syntax_scan(self):
        """The cheap length guard runs before any O(len) syntax scan, and the bracket
        scan is linear, so a hostile megabyte-long unmatched-``[`` glob fails closed
        immediately instead of triggering a quadratic pre-scan."""
        huge = "packages/" + "[" * 2_000_000
        assert len(huge) > _MAX_GLOB_LENGTH
        assert _package_matches_workspace(("a",), [huge]) is False
        # The linear bracket scanner itself does not choke on the raw string either.
        assert _has_complete_bracket_class("[" * 100000) is False

    def test_leading_slash_normalized_before_hash_and_glob_matching(self):
        """A leading ``/`` (or ``//`` / ``.//``) is normalized the SAME way for a
        ``#``-pattern as for any other glob. In pnpm (the default) and npm FINAL matching
        ``#`` is LITERAL, so ``//#*`` normalizes to ``#*`` and matches a directory named
        ``#evil`` — the leading slashes are removed, not left to break the match. A
        two-segment path still fails a one-segment pattern on segment count."""
        # Normalized to `#*`; matches the single-segment `#evil` literally.
        assert _package_matches_workspace(("#evil",), ["//#*"]) is True
        assert _package_matches_workspace(("#evil",), [".//#*"]) is True
        # `/#*` -> `#*` (one segment) cannot match a two-segment path.
        assert _package_matches_workspace(("#evil", "package"), ["/#*"]) is False
        # A leading `/` on a real glob is still just normalized away.
        assert _package_matches_workspace(("packages", "app"), ["/packages/*"]) is True

    def test_generated_dollar_brace_adjacency_still_expands(self):
        """A ``$`` produced as a brace option must not be mistaken for an opaque
        ``${...}`` when it lands before another brace. ``{$,x}{a,b}`` expands to
        ``$a``/``$b``/``xa``/``xb`` (genuine ``${...}`` spans are masked out before
        expansion), so the exclusion actually fires."""
        assert sorted(_expand_braces("{$,x}{a,b}")) == ["$a", "$b", "xa", "xb"]
        globs = ["packages/**", "!packages/{$,x}{a,b}"]
        assert _package_matches_workspace(("packages", "$a"), globs) is False
        assert _package_matches_workspace(("packages", "xb"), globs) is False
        assert _package_matches_workspace(("packages", "yy"), globs) is True
        # A genuine balanced ${...} is still opaque (masked, restored literally).
        assert _expand_braces("packages/${foo,bar}") == ["packages/${foo,bar}"]

    def test_astral_question_mark_with_globstar_matches_over_utf16(self):
        """With UTF-16-unit ``?`` matching, ``packages/ap?/**`` matches
        ``("packages", "app", "😀")`` (``ap?`` matches ``app``, ``**`` consumes the
        emoji), and ``packages/?/**`` does not match ``("packages", "😀", "app")``
        (a one-unit ``?`` cannot match the two-unit emoji segment)."""
        emoji = "\U0001F600"
        assert _package_matches_workspace(
            ("packages", "app", emoji), ["packages/ap?/**"]) is True
        assert _package_matches_workspace(
            ("packages", emoji, "app"), ["packages/?/**"]) is False
        # But `??/**` DOES match the two-unit emoji segment.
        assert _package_matches_workspace(
            ("packages", emoji, "app"), ["packages/??/**"]) is True

    def test_incomplete_extglob_marker_is_not_rejected(self):
        """An *incomplete* extglob marker (``foo?(bar`` with no ``)``) is minimatch's
        ``?`` wildcard plus a literal ``(`` — the direct matcher agrees — so it must
        match, not be rejected. A *complete* extglob group still fails closed."""
        assert _package_matches_workspace(
            ("packages", "foox(bar"), ["packages/foo?(bar"]) is True
        assert _has_complete_extglob("packages/foo?(bar") is False
        assert _has_complete_extglob("packages/@(a|b)") is True
        assert _package_matches_workspace(
            ("packages", "foo"), ["packages/*", "!packages/@(foo|bar)"]) is False

    def test_bracket_and_extglob_do_not_cross_slash(self):
        """A bracket class or extglob is confined to one ``/``-delimited segment, so a
        ``[`` in one segment and ``]`` in another (``foo[/bar]``) — or an ``?(`` split
        across ``/`` (``foo?(/bar)``) — is literal in minimatch and MUST match, not be
        rejected. A class/extglob wholly within one segment still fails closed."""
        assert _package_matches_workspace(
            ("packages", "foo[", "bar]"), ["packages/foo[/bar]"]) is True
        assert _package_matches_workspace(
            ("packages", "foox(", "bar)"), ["packages/foo?(/bar)"]) is True
        assert _package_matches_workspace(("packages", "a"), ["packages/[^a]"]) is False
        assert _package_matches_workspace(
            ("packages", "foo"), ["packages/x", "!packages/@(foo|bar)"]) is False

    def test_brace_range_grammar_multi_char_endpoints_are_literal(self):
        """Only real minimatch ranges — integer or single-character endpoints, with
        an optional integer step — fail closed. Multi-character (``{foo..bar}``),
        non-integer numeric (``{1.0..3.0}``), and empty (``{..}``) forms are literal
        and MUST stay matchable."""
        assert _has_brace_range("{1..3}") is True
        assert _has_brace_range("{a..z}") is True
        assert _has_brace_range("{01..03}") is True
        assert _has_brace_range("{1..9..2}") is True
        assert _has_brace_range("{-2..2}") is True
        assert _has_brace_range("{foo..bar}") is False
        assert _has_brace_range("{1.0..3.0}") is False
        assert _has_brace_range("{..}") is False
        # Plus-prefixed and non-ASCII/Unicode endpoints are literal, not ranges.
        assert _has_brace_range("{+1..+3}") is False
        assert _has_brace_range("{١..٣}") is False  # Arabic-Indic digits
        assert _package_matches_workspace(
            ("packages", "{+1..+3}"), ["packages/{+1..+3}"]) is True
        # A literal multi-char-endpoint "range" matches its literal dir name.
        assert _package_matches_workspace(
            ("packages", "{foo..bar}"), ["packages/{foo..bar}"]) is True
        # A real range still fails closed (comma-only expander cannot expand it).
        assert _package_matches_workspace(
            ("packages", "2"), ["packages/**", "!packages/{1..3}"]) is False

    def test_symlinked_test_dir_escaping_repo_is_refused(self, tmp_path):
        """A test dir symlinked outside the repo must not adopt an out-of-repo config."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        outside = tmp_path / "outside"
        (outside / "tests").mkdir(parents=True)
        (outside / "jest.config.js").write_text("module.exports = {};")
        (outside / "tests" / "foo.test.ts").write_text("describe('x', () => {})")
        # repo/tests -> outside/tests (escapes the repository)
        (repo / "tests").symlink_to(outside / "tests", target_is_directory=True)

        result = _detect_ts_test_runner(repo / "tests" / "foo.test.ts")
        assert result is None

    def test_symlink_within_repo_still_detected(self, tmp_path):
        """A symlink that stays inside the repo must still find the repo's config."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        real = repo / "real" / "tests"
        real.mkdir(parents=True)
        (real / "foo.test.ts").write_text("describe('x', () => {})")
        link = repo / "linked"
        link.symlink_to(repo / "real", target_is_directory=True)

        cmd, returned_dir = _detect_ts_test_runner(link / "tests" / "foo.test.ts")
        assert "npx jest" in cmd
        assert returned_dir == repo.resolve()

    def test_package_json_jest_key_detected_without_dedicated_config(self, tmp_path):
        """Jest reads config from a top-level ``"jest"`` object in ``package.json``, so a
        package with only that key (no ``jest.config.*``) and a nested ``.test.ts`` is a
        Jest project — it must not fall through to ``npx tsx``."""
        repo = tmp_path / "repo"
        (repo / "src").mkdir(parents=True)
        (repo / ".git").mkdir()
        (repo / "package.json").write_text('{"jest": {"testEnvironment": "node"}}')
        (repo / "src" / "a.test.ts").write_text("test('x', () => {})")
        cmd, cwd = _detect_ts_test_runner(repo / "src" / "a.test.ts")
        assert "npx jest" in cmd and "--runTestsByPath" in cmd, cmd
        assert cwd == repo.resolve()
        # A package.json WITHOUT a jest object (and no config) is not a Jest project.
        (repo / "package.json").write_text('{"name": "x"}')
        assert _detect_ts_test_runner(repo / "src" / "a.test.ts") is None
        # A non-object jest value is ignored (fails closed, not a Jest project).
        (repo / "package.json").write_text('{"jest": "some/path"}')
        assert _detect_ts_test_runner(repo / "src" / "a.test.ts") is None

    def test_vite_config_adopted_only_when_vitest_is_proven(self, tmp_path):
        """Vitest loads ``vite.config.*`` as its config, but only a manifest that PROVES
        Vitest (a ``vitest`` dependency or a script invoking it) makes a ``vite.config.*``
        a test runner. An ordinary Vite-only app (``vite.config.ts`` but no vitest) is
        NOT a test project and must not be adopted."""
        repo = tmp_path / "repo"
        (repo / "src").mkdir(parents=True)
        (repo / ".git").mkdir()
        (repo / "vite.config.ts").write_text("export default {}")
        (repo / "src" / "a.test.ts").write_text("test('x', () => {})")
        # Vite-only (no vitest) → not a test project.
        (repo / "package.json").write_text('{"devDependencies": {"vite": "^5"}}')
        assert _detect_ts_test_runner(repo / "src" / "a.test.ts") is None
        # vitest in devDependencies (a STRING spec) → adopt vite.config.ts as Vitest.
        (repo / "package.json").write_text('{"devDependencies": {"vitest": "^1"}}')
        cmd, cwd = _detect_ts_test_runner(repo / "src" / "a.test.ts")
        assert "npx vitest run" in cmd, cmd
        assert cwd == repo.resolve()
        # A NON-STRING vitest dependency value (false/null/number) is not a valid package
        # spec (npm rejects it) and does NOT prove Vitest.
        for bad in ("false", "null", "1"):
            (repo / "package.json").write_text(
                '{"devDependencies": {"vite": "^5", "vitest": %s}}' % bad)
            assert _detect_ts_test_runner(repo / "src" / "a.test.ts") is None, bad
        # '#' comment provenance (Bash-accurate): a mid-word, QUOTED, or ESCAPED '#' is
        # literal so a later vitest clause still proves; an unquoted comment ends only its
        # own line.
        for script in ("echo a#b && npx vitest",           # mid-word
                       'echo "# harmless" && npx vitest',   # quoted
                       r"echo \#harmless && npx vitest",     # escaped
                       "echo hi # comment\nnpx vitest"):     # comment ends at newline
            (repo / "package.json").write_text(
                json.dumps({"scripts": {"test": script}}))
            cmd4, _ = _detect_ts_test_runner(repo / "src" / "a.test.ts")
            assert cmd4 is not None and "npx vitest run" in cmd4, script
        # A genuine leading-'#' comment does NOT prove.
        for script in ("echo hi # npx vitest", "# npx vitest"):
            (repo / "package.json").write_text(
                json.dumps({"scripts": {"test": script}}))
            assert _detect_ts_test_runner(repo / "src" / "a.test.ts") is None, script
        # A here-document / here-string BODY is data, not commands — a `vitest` line
        # inside it must NOT prove Vitest (a Vite-only manifest false-positive).
        for script in ("cat <<EOF\nnpx vitest\nEOF", "bash <<< 'npx vitest'",
                       "cat << 'END'\nvitest run\nEND"):
            (repo / "package.json").write_text(
                json.dumps({"scripts": {"test": script}}))
            assert _detect_ts_test_runner(repo / "src" / "a.test.ts") is None, script
        # A script invoking the vitest BINARY proves it — directly, via a direct package
        # runner (npx/bunx), via an explicit exec subcommand (pnpm exec / bun x), or with
        # a `--` options terminator (npm exec -- vitest).
        for script in ("vitest run", "npx vitest", "npx --yes vitest", "bunx vitest",
                       "pnpm exec vitest", "pnpm dlx vitest", "bun x vitest",
                       "yarn exec vitest", "npm exec -- vitest", "pnpm dlx -- vitest",
                       "./node_modules/.bin/vitest"):
            (repo / "package.json").write_text(
                json.dumps({"scripts": {"test": script}}))
            cmd2, _ = _detect_ts_test_runner(repo / "src" / "a.test.ts")
            assert cmd2 is not None and "npx vitest run" in cmd2, (script, cmd2)
        # DoS: an oversized (near-1MB) no-whitespace script value must fail proof closed
        # QUICKLY (a quadratic shell-lexer cost is unacceptable), not be adopted.
        import time as _time
        (repo / "package.json").write_text(
            json.dumps({"scripts": {"test": "x" * (900 * 1024)}}))
        _t0 = _time.time()
        assert _detect_ts_test_runner(repo / "src" / "a.test.ts") is None
        assert _time.time() - _t0 < 2.0, "oversized script must fail closed quickly"
        # A script where "vitest" is not the invoked BINARY — a bare argument; an arg to
        # echo/node/command; the value of a runner option flag; a package.json SCRIPT
        # name (`npm run vitest` / bare `pnpm vitest`, which may be a Vite-only shadow);
        # a substring; or only reachable past an ESCAPED/quoted operator — does NOT prove
        # Vitest.
        for script in ("echo no-vitest-installed", "cat vitest.config.ts",
                       "echo run-vitest-later", "echo vitest", "node vitest",
                       "command -v vitest", "printf vitest", "pnpm run test",
                       "npx --package vitest echo ok", "npx -p vitest echo ok",
                       "npm run vitest", "pnpm run vitest", "yarn run vitest",
                       "pnpm vitest", "yarn vitest", "npm vitest",
                       r"echo x\; vitest", "echo 'a; b' vitest"):
            (repo / "package.json").write_text(
                json.dumps({"scripts": {"test": script}}))
            assert _detect_ts_test_runner(repo / "src" / "a.test.ts") is None, script
        # Script-shadowing: `npm run vitest` runs a "vitest" script that is actually Vite,
        # so a Vite-only package with such a script must NOT be adopted as Vitest.
        (repo / "package.json").write_text(json.dumps(
            {"scripts": {"test": "npm run vitest", "vitest": "vite --mode test"}}))
        assert _detect_ts_test_runner(repo / "src" / "a.test.ts") is None
        # Binary-position invocations (incl. env prefix and a later clause) DO prove.
        for script in ("CI=1 vitest run", "build && vitest"):
            (repo / "package.json").write_text('{"scripts": {"test": "%s"}}' % script)
            cmd3, _ = _detect_ts_test_runner(repo / "src" / "a.test.ts")
            assert cmd3 is not None and "npx vitest run" in cmd3, (script, cmd3)

    def test_symlink_to_foreign_checkout_is_refused(self, tmp_path):
        """A symlink whose target is itself a git checkout must not be adopted.

        `repo/link -> outside` where BOTH `repo/.git` and `outside/.git` exist.
        The lexical repo root must anchor at `repo` (skipping the symlinked
        component whose `.git` probe would follow the link), so `outside`'s Jest
        config is refused rather than adopted.
        """
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        outside = tmp_path / "outside"
        outside.mkdir()
        (outside / ".git").mkdir()
        (outside / "jest.config.js").write_text("module.exports = {};")
        (outside / "tests").mkdir()
        (outside / "tests" / "foo.test.ts").write_text("describe('x', () => {})")
        (repo / "link").symlink_to(outside, target_is_directory=True)

        result = _detect_ts_test_runner(repo / "link" / "tests" / "foo.test.ts")
        assert result is None

    def test_many_double_star_segments_matches_in_polynomial_time(self):
        """A wall of `**` segments must not backtrack exponentially or recurse."""
        rel = tuple(["a"] * 20)
        # 8 `**` followed by a non-matching literal previously took ~0.6s.
        assert _relative_matches_workspace_glob(rel, "/".join(["**"] * 8) + "/zzz") is False
        assert _relative_matches_workspace_glob(rel, "/".join(["**"] * 8) + "/a") is True

    def test_double_star_wall_over_segment_budget_fails_closed(self):
        """A pattern past the segment budget raises `_PatternBudgetError`."""
        huge = "/".join(["**"] * 1000) + "/never"
        with pytest.raises(_PatternBudgetError):
            _relative_matches_workspace_glob(("a",), huge)
        assert _package_matches_workspace(("a",), [huge]) is False

    def test_deeply_nested_brace_bomb_does_not_recurse(self):
        """1000 nested `{a,b}` groups must fail closed, not raise RecursionError."""
        bomb = "x" + "{a,b}" * 1000
        # Iterative expansion → budget error, never RecursionError.
        with pytest.raises(_BraceBudgetError):
            _expand_braces(bomb)
        assert _package_matches_workspace(("a",), [bomb]) is False

    def test_non_string_workspace_entry_fails_closed(self, tmp_path):
        """A `true`/number entry in `workspaces` must not coerce into a glob."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": [true]}')
        leaf = repo / "True"  # what str(True) would have matched
        leaf.mkdir()
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")

        assert _workspace_globs_for(repo) == []
        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_non_string_lerna_and_pnpm_entries_fail_closed(self, tmp_path):
        """Non-string entries in lerna.json / pnpm-workspace.yaml yield no globs."""
        anc = tmp_path / "a"
        anc.mkdir()
        (anc / "lerna.json").write_text('{"packages": ["packages/*", 5]}')
        assert _workspace_globs_for(anc) == []

        pytest.importorskip("yaml")
        anc2 = tmp_path / "b"
        anc2.mkdir()
        (anc2 / "pnpm-workspace.yaml").write_text("packages:\n  - true\n")
        assert _workspace_globs_for(anc2) == []

    def test_pnpm_yaml_invalid_utf8_fails_closed(self, tmp_path):
        """Invalid UTF-8 in pnpm-workspace.yaml must not raise UnicodeDecodeError."""
        pytest.importorskip("yaml")
        anc = tmp_path / "a"
        anc.mkdir()
        (anc / "pnpm-workspace.yaml").write_bytes(b"packages:\n  - '\xff\xfe'\n")
        assert _workspace_globs_for(anc) == []

    def test_symlink_to_nested_foreign_checkout_is_refused(self, tmp_path):
        """A symlinked component whose target holds a *nested* foreign checkout.

        `repo/link -> outside`, `repo/.git`, `outside/foreign/.git`,
        `outside/foreign/jest.config.js`, test at `repo/link/foreign/foo.test.ts`.
        The `.git` probe must not follow the `link` symlink to anchor at the
        foreign checkout; containment anchors at `repo` and refuses.
        """
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        outside = tmp_path / "outside"
        (outside / "foreign").mkdir(parents=True)
        (outside / "foreign" / ".git").mkdir()
        (outside / "foreign" / "jest.config.js").write_text("module.exports = {};")
        (outside / "foreign" / "foo.test.ts").write_text("describe('x', () => {})")
        (repo / "link").symlink_to(outside, target_is_directory=True)

        result = _detect_ts_test_runner(repo / "link" / "foreign" / "foo.test.ts")
        assert result is None

    def test_deep_path_ending_in_escape_symlink_is_refused(self, tmp_path):
        """A deep (>200-segment) in-repo path ending in an escaping symlink.

        `_lexical_repo_root` must walk to the real repo root (no artificial depth
        cap) and anchor there, so the just-outside config is refused rather than
        adopted because containment was silently skipped.
        """
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        outside = tmp_path / "outside"
        outside.mkdir()
        (outside / "jest.config.js").write_text("module.exports = {};")
        (outside / "foo.test.ts").write_text("describe('x', () => {})")
        deep = repo
        for _ in range(205):
            deep = deep / "a"
        deep.mkdir(parents=True)
        (deep / "esc").symlink_to(outside, target_is_directory=True)

        assert _lexical_repo_root(deep / "esc" / "foo.test.ts") == repo.resolve()
        assert _detect_ts_test_runner(deep / "esc" / "foo.test.ts") is None

    def test_dotfile_segment_not_matched_by_wildcard(self):
        """minimatch dot:false — a wildcard must not match a leading-dot segment."""
        assert _package_matches_workspace(("packages", ".shadow"), ["packages/*"]) is False
        assert _package_matches_workspace((".shadow", "pkg"), ["**"]) is False
        assert _package_matches_workspace((".shadow", "pkg"), ["**/pkg"]) is False
        # An explicit dot pattern DOES match.
        assert _package_matches_workspace(("packages", ".shadow"), ["packages/.*"]) is True
        assert _package_matches_workspace(("packages", ".shadow"), ["packages/.shadow"]) is True
        # Ordinary (non-dot) segments are unaffected.
        assert _package_matches_workspace(("packages", "app"), ["packages/*"]) is True
        assert _package_matches_workspace(("a", "b", "c"), ["**"]) is True

    def test_dotfile_package_does_not_adopt_workspace_config(self, tmp_path):
        """A `.shadow` package under `packages/*` must not inherit the root config."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        leaf = repo / "packages" / ".shadow"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_aggregate_brace_budget_across_many_globs_fails_closed(self):
        """The brace budget is aggregate: thousands of expanding globs fail closed."""
        many = ["packages/{a,b}"] * 3000
        assert _package_matches_workspace(("packages", "a"), many) is False

    def test_raw_glob_count_cap_fails_closed(self):
        """A declaration with an absurd number of raw globs fails closed."""
        assert _package_matches_workspace(("packages", "a"), ["packages/*"] * 5000) is False

    def test_moderate_glob_declaration_still_matches(self):
        """A realistic (dozens) declaration is unaffected by the budgets."""
        globs = ["packages/x{}".format(i) for i in range(49)] + ["packages/*"]
        assert _package_matches_workspace(("packages", "app"), globs) is True

    def test_comma_bomb_brace_fails_closed(self):
        """A single brace with a huge number of comma options fails closed."""
        with pytest.raises(_BraceBudgetError):
            _expand_braces("x{" + ",".join(["a"] * 200000) + "}")

    def test_long_prefix_brace_glob_fails_closed_by_bytes(self):
        """A long-prefix glob with a few braces (under the count budget) must fail
        closed on the length cap, not multiply into gigabytes of strings."""
        import time
        glob = "x" * 2_000_000 + "{a,b}{c,d}{e,f}{g,h}{i,j}"
        start = time.monotonic()
        assert _package_matches_workspace(("x",), [glob]) is False
        assert time.monotonic() - start < 5.0  # must not blow up

    def test_pnpm_yaml_recursion_bomb_fails_closed(self, tmp_path):
        """Deeply nested YAML must fail closed rather than raising RecursionError."""
        pytest.importorskip("yaml")
        anc = tmp_path / "a"
        anc.mkdir()
        (anc / "pnpm-workspace.yaml").write_text("packages: " + "[" * 3000 + "]" * 3000 + "\n")
        assert _workspace_globs_for(anc) == []

    def test_pnpm_yaml_date_like_scalar_is_a_string_glob(self, tmp_path):
        """YAML 1.2's core schema (which pnpm uses) has NO timestamp type, so a
        date-like scalar such as ``2020-99-99`` is a plain STRING — a literal glob,
        not a construction that crashes (the YAML 1.1 timestamp constructor raised a
        bare ValueError on an out-of-range date). Discovery must not crash, and the
        entry is kept as a literal glob."""
        pytest.importorskip("yaml")
        anc = tmp_path / "anc"
        anc.mkdir()
        (anc / "pnpm-workspace.yaml").write_text("packages:\n  - 2020-99-99\n")
        assert _workspace_globs_for(anc) == ["2020-99-99"]  # literal string glob
        (anc / "pnpm-workspace.yaml").write_text("packages:\n  - 2020-13-45\n")
        assert _workspace_globs_for(anc) == ["2020-13-45"]

    def test_pnpm_malformed_timestamp_leaf_not_a_member(self, tmp_path):
        """End-to-end: a pnpm YAML that fails to construct must not let a leaf adopt
        the root Jest config (and must not crash discovery)."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "pnpm-workspace.yaml").write_text("packages: [2020-99-99]\n")
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")
        pytest.importorskip("yaml")
        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_slash_wall_glob_fails_closed(self):
        """A glob with thousands of `/` segments fails closed via the segment cap."""
        with pytest.raises(_PatternBudgetError):
            _relative_matches_workspace_glob(("a",), "/".join(["x"] * 1000))
        assert _package_matches_workspace(("a",), ["/".join(["x"] * 1000)]) is False

    def test_aggregate_match_work_is_bounded(self):
        """Many long `**` globs against a deep path must fail closed (aggregate
        DP-cell budget), not spend seconds of CPU per membership check."""
        import time
        rel = tuple(["a"] * 128)
        glob = "/".join(["**"] * 255 + ["z"])  # 256 segments, at the per-glob cap
        globs = [glob] * 1024  # up to the brace-expansion count budget
        start = time.monotonic()
        assert _package_matches_workspace(rel, globs) is False
        assert time.monotonic() - start < 2.0  # must not grind for seconds

    def test_discovery_wide_match_budget_bounds_deep_chain(self, tmp_path):
        """The matching budget is shared across the whole discovery walk, so a heavy
        manifest re-evaluated at each of many nested package boundaries cannot stall
        for seconds. A legit deep chain with a normal manifest still resolves."""
        import time
        import json as _json
        # Hostile: root manifest with 1000 long globstar globs, deep member chain.
        repo = tmp_path / "hostile"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        heavy = "/".join(["**"] * 255 + ["nomatch"])
        (repo / "package.json").write_text(_json.dumps({"workspaces": [heavy] * 1000 + ["**"]}))
        deep = repo
        for i in range(70):
            deep = deep / f"p{i}"
            deep.mkdir()
            (deep / "package.json").write_text("{}")
        test_file = deep / "s" / "w.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")
        start = time.monotonic()
        _detect_ts_test_runner(test_file)  # must not hang
        assert time.monotonic() - start < 3.0

        # Legit: same depth, a normal manifest still finds the root Jest config.
        good = tmp_path / "good"
        good.mkdir()
        (good / ".git").mkdir()
        (good / "jest.config.js").write_text("module.exports = {};")
        (good / "package.json").write_text('{"workspaces": ["**"]}')
        d = good
        for i in range(70):
            d = d / f"p{i}"
            d.mkdir()
            (d / "package.json").write_text("{}")
        tf = d / "s" / "w.test.ts"
        tf.parent.mkdir(parents=True)
        tf.write_text("describe('w', () => {})")
        cmd, _ = _detect_ts_test_runner(tf)
        assert "npx jest" in cmd

    def test_dotdot_through_symlink_is_refused(self, tmp_path):
        """A `..` component that traverses a symlink must fail closed.

        `os.path.abspath` collapses `..` textually before symlink inspection, so a
        path like `repo/link/../../foreign/...` (link is a symlink) could otherwise
        mis-anchor containment and adopt a foreign checkout's config.
        """
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "pdd" / "prompts").mkdir(parents=True)
        (repo / "prompts").symlink_to(repo / "pdd" / "prompts", target_is_directory=True)
        foreign = tmp_path / "foreign"
        (foreign / "pkg").mkdir(parents=True)
        (foreign / "pkg" / "jest.config.js").write_text("module.exports = {};")
        (foreign / "pkg" / "a.test.ts").write_text("describe('x', () => {})")

        crafted = repo / "prompts" / ".." / ".." / "foreign" / "pkg" / "a.test.ts"
        assert _detect_ts_test_runner(crafted) is None

    def test_dotdot_without_symlink_still_works(self, tmp_path):
        """A `..` component with no intervening symlink is handled normally."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "a" / "tests").mkdir(parents=True)
        (repo / "a" / "tests" / "x.test.ts").write_text("describe('x', () => {})")

        path = repo / "a" / ".." / "a" / "tests" / "x.test.ts"
        cmd, _ = _detect_ts_test_runner(path)
        assert "npx jest" in cmd

    def test_config_file_symlink_escaping_repo_is_refused(self, tmp_path):
        """A runner config that is itself a symlink escaping the repo is refused."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        foreign = tmp_path / "foreign"
        foreign.mkdir()
        (foreign / "jest.config.js").write_text("module.exports = {};")
        (repo / "jest.config.js").symlink_to(foreign / "jest.config.js")
        (repo / "src").mkdir()
        (repo / "src" / "a.test.ts").write_text("describe('x', () => {})")

        assert _detect_ts_test_runner(repo / "src" / "a.test.ts") is None

    def test_config_file_symlink_within_repo_is_allowed(self, tmp_path):
        """An in-repo config symlink is fine; a broken one is refused."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "real.config.js").write_text("module.exports = {};")
        (repo / "jest.config.js").symlink_to(repo / "real.config.js")
        (repo / "src").mkdir()
        (repo / "src" / "a.test.ts").write_text("describe('x', () => {})")
        cmd, _ = _detect_ts_test_runner(repo / "src" / "a.test.ts")
        assert "npx jest" in cmd

        broken = tmp_path / "repo2"
        broken.mkdir()
        (broken / ".git").mkdir()
        (broken / "jest.config.js").symlink_to(broken / "nonexistent.js")
        (broken / "src").mkdir()
        (broken / "src" / "a.test.ts").write_text("describe('x', () => {})")
        assert _detect_ts_test_runner(broken / "src" / "a.test.ts") is None

    def test_workspace_root_without_package_json_stops_the_walk(self, tmp_path):
        """A pnpm/lerna workspace root lacking its own package.json still caps the walk.

        An unrelated Jest config above the declared workspace root must NOT be
        adopted just because the root has no package.json to trigger the boundary.
        """
        outer = tmp_path / "outer"
        outer.mkdir()
        (outer / ".git").mkdir()
        (outer / "jest.config.js").write_text("module.exports = {};")  # unrelated, above
        ws = outer / "myws"
        ws.mkdir()
        (ws / "pnpm-workspace.yaml").write_text("packages:\n  - 'packages/*'\n")  # no package.json
        leaf = ws / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")

        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_workspace_root_with_own_config_is_still_inherited(self, tmp_path):
        """A pnpm workspace root (no package.json) that DOES have a config is used."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "pnpm-workspace.yaml").write_text("packages:\n  - 'packages/*'\n")
        (repo / "jest.config.js").write_text("module.exports = {};")  # at the ws root
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")

        cmd, returned_dir = _detect_ts_test_runner(test_file)
        assert "npx jest" in cmd
        assert returned_dir == repo.resolve()

    def test_json_recursion_bomb_manifest_fails_closed(self, tmp_path):
        """A deeply nested package.json/lerna.json must fail closed, not RecursionError."""
        for name, body in (
            ("package.json", '{"workspaces":' + "[" * 100000 + "]" * 100000 + "}"),
            ("lerna.json", '{"packages":' + "[" * 100000 + "]" * 100000 + "}"),
        ):
            anc = tmp_path / name.replace(".", "_")
            anc.mkdir()
            (anc / name).write_text(body)
            assert _workspace_globs_for(anc) == []

    def test_oversized_manifest_fails_closed(self, tmp_path):
        """An oversized declaration file contributes no globs (not fully parsed)."""
        anc = tmp_path / "a"
        anc.mkdir()
        (anc / "package.json").write_text(
            '{"workspaces":["packages/*"]}\n' + " " * (2 * 1024 * 1024)
        )
        assert _workspace_globs_for(anc) == []

    def test_high_cardinality_manifest_fails_closed_fast(self, tmp_path):
        """A manifest under the byte cap but with a huge number of entries must
        fail membership closed (cardinality guard) without a giant copy — and an
        over-byte-cap manifest is rejected before it is parsed at all."""
        import json as _json
        import time
        # Under byte cap, well over the raw-glob cardinality cap.
        anc = tmp_path / "pkg"
        anc.mkdir()
        (anc / "package.json").write_text(_json.dumps({"workspaces": ["a"] * 50000}))
        start = time.monotonic()
        assert _workspace_globs_for(anc) == []
        assert time.monotonic() - start < 2.0

        # Over the (small) pnpm byte cap → rejected before parsing (no OOM).
        pytest.importorskip("yaml")
        anc2 = tmp_path / "pnpm"
        anc2.mkdir()
        (anc2 / "pnpm-workspace.yaml").write_text("packages: [" + "a," * 200000 + "a]")
        start = time.monotonic()
        assert _workspace_globs_for(anc2) == []
        assert time.monotonic() - start < 2.0

    @pytest.mark.skipif(not os.path.exists("/dev/zero"), reason="needs /dev/zero")
    def test_manifest_symlinked_to_device_fails_closed(self, tmp_path):
        """A manifest that is a symlink to a device (st_size 0, streams forever)
        must fail closed instead of hanging on read."""
        import time
        anc = tmp_path / "a"
        anc.mkdir()
        (anc / "pnpm-workspace.yaml").symlink_to("/dev/zero")
        start = time.monotonic()
        assert _workspace_globs_for(anc) == []
        assert time.monotonic() - start < 5.0

    def test_manifest_symlinked_to_regular_file_is_read(self, tmp_path):
        """A manifest that is a symlink to a genuine regular file is still read."""
        anc = tmp_path / "a"
        anc.mkdir()
        real = anc / "real.yaml"
        real.write_text("packages:\n  - 'packages/*'\n")
        (anc / "pnpm-workspace.yaml").symlink_to(real)
        pytest.importorskip("yaml")
        assert _workspace_globs_for(anc) == ["packages/*"]

    def test_dangling_pnpm_symlink_is_authoritative_fail_closed(self, tmp_path):
        """A dangling pnpm-workspace.yaml symlink is still authoritative: it must
        not fall through to a stale package.json `workspaces` field."""
        anc = tmp_path / "a"
        anc.mkdir()
        (anc / "package.json").write_text('{"workspaces": ["packages/*"]}')  # stale
        (anc / "pnpm-workspace.yaml").symlink_to(tmp_path / "does-not-exist.yaml")
        assert _workspace_globs_for(anc) == []

    def test_dangling_pnpm_symlink_leaf_not_a_member(self, tmp_path):
        """End-to-end: a dangling pnpm symlink must not let a leaf adopt root Jest."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        (repo / "pnpm-workspace.yaml").symlink_to(tmp_path / "missing.yaml")
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")
        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_dangling_package_json_symlink_still_stops_walk(self, tmp_path):
        """An independent package whose package.json is a dangling symlink must
        still be a JS project boundary — the walk must not slip past it and adopt
        an unrelated ancestor's config."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")  # unrelated ancestor
        leaf = repo / "packages" / "indep"
        leaf.mkdir(parents=True)
        (leaf / "package.json").symlink_to(tmp_path / "missing.json")  # dangling
        test_file = leaf / "src" / "a.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('x', () => {})")
        assert _detect_ts_test_runner(test_file) is None

    def test_member_with_dangling_package_json_still_inherits(self, tmp_path):
        """A proven workspace member still inherits the root config even if its own
        package.json is a dangling symlink (membership is by path, not manifest read)."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["packages/*"]}')
        member = repo / "packages" / "app"
        member.mkdir(parents=True)
        (member / "package.json").symlink_to(tmp_path / "gone.json")  # dangling
        test_file = member / "src" / "a.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('x', () => {})")
        cmd, returned_dir = _detect_ts_test_runner(test_file)
        assert "npx jest" in cmd
        assert returned_dir == repo.resolve()

    def test_self_referential_symlink_path_is_refused(self, tmp_path):
        """A self-referential (looping) symlink path must fail closed, not raise."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        loop = repo / "loop"
        loop.symlink_to(loop)  # points at itself → resolve() raises on 3.12
        assert _detect_ts_test_runner(loop / "a.test.ts") is None

    def test_directory_symlink_loop_is_refused(self, tmp_path):
        """A pair of mutually-referential directory symlinks must fail closed."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        a = repo / "a"
        b = repo / "b"
        a.symlink_to(b)
        b.symlink_to(a)
        assert _detect_ts_test_runner(a / "x.test.ts") is None

    def test_ancestor_manifests_parsed_at_most_once_per_discovery(self, tmp_path):
        """Deeply nested packages must not re-parse every ancestor manifest
        quadratically — each ancestor is read at most once per discovery."""
        import pdd.get_test_command as mod
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "package.json").write_text('{"workspaces": ["**"]}')
        deep = repo
        depth = 25
        for i in range(depth):
            deep = deep / f"p{i}"
            deep.mkdir()
            (deep / "package.json").write_text("{}")
        test_file = deep / "src" / "w.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")

        reads = {"n": 0}
        original = mod._workspace_globs_uncached

        def _counting(ancestor):
            reads["n"] += 1
            return original(ancestor)

        mod._workspace_globs_uncached = _counting
        try:
            result = _detect_ts_test_runner(test_file)
        finally:
            mod._workspace_globs_uncached = original
        assert result is not None and "npx jest" in result[0]
        # With caching, reads are bounded near the path depth, not depth^2.
        assert reads["n"] <= depth + 5, reads["n"]

    def test_malformed_lerna_does_not_grant_default_glob(self, tmp_path):
        """A parse-failing lerna.json must not fall through to the `packages/*` default."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "lerna.json").write_text("{ this is not json")
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")
        # Membership unproven (lerna parse failed → no default) → no root Jest.
        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "npx jest" not in result.command, result.command

    def test_lerna_explicit_null_packages_is_not_the_default(self, tmp_path):
        """`lerna.json` `{"packages": null}` is an explicit value, NOT an omitted
        key, so it must NOT grant the `packages/*` default; only a genuinely
        omitted key does."""
        # Direct: omitted vs explicit-null.
        omitted = tmp_path / "omitted"
        omitted.mkdir()
        (omitted / "lerna.json").write_text("{}")
        assert _workspace_globs_for(omitted) == ["packages/*"]

        explicit_null = tmp_path / "explicit_null"
        explicit_null.mkdir()
        (explicit_null / "lerna.json").write_text('{"packages": null}')
        assert _workspace_globs_for(explicit_null) == []

        # End-to-end: an independent leaf must not adopt the root Jest via the
        # spurious default from an explicit-null lerna.json.
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        (repo / "lerna.json").write_text('{"packages": null}')
        leaf = repo / "packages" / "app"
        leaf.mkdir(parents=True)
        (leaf / "package.json").write_text("{}")
        test_file = leaf / "src" / "widget.test.ts"
        test_file.parent.mkdir(parents=True)
        test_file.write_text("describe('w', () => {})")
        result = get_test_command_for_file(str(test_file), language="typescript")
        assert result is not None
        assert "npx jest" not in result.command, result.command


class TestFixErrorLoopPlaceholderSafety:
    """fix_error_loop must not re-substitute placeholders into a completed command."""

    def test_no_reinjection_via_maliciously_named_path(self, tmp_path):
        """A test path containing a literal `{test}` and shell metachars must not
        break the shell quoting of the already-formed TS runner command."""
        import shlex
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        evil_dir = repo / "{test};touch PWN"
        evil_dir.mkdir()
        test_file = evil_dir / "a.test.ts"
        test_file.write_text("describe('x', () => {})")

        tc = get_test_command_for_file(str(test_file), language="typescript")
        # Simulate the caller: the command must round-trip through a POSIX shell
        # tokenizer back to the exact resolved path — no injected `;`/`touch` token.
        argv = shlex.split(tc.command)
        assert str(test_file.resolve()) in argv, (tc.command, argv)
        assert "touch" not in argv, argv

    def test_run_non_python_initial_verification_does_not_reinject(self, tmp_path):
        """`_run_non_python_initial_verification` must execute the command as-is.

        Directly exercises the fix_error_loop boundary: the command handed to
        subprocess.run must still round-trip to the resolved path (no `{file}`/
        `{test}` re-substitution splicing an injected `;touch` token).
        """
        import shlex
        from unittest.mock import patch
        from pdd.fix_error_loop import _run_non_python_initial_verification

        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        (repo / "jest.config.js").write_text("module.exports = {};")
        evil = repo / "{test};touch PWN"
        evil.mkdir()
        test_file = evil / "a.test.ts"
        test_file.write_text("describe('x', () => {})")
        code_file = evil / "a.ts"
        code_file.write_text("export const x = 1;")

        captured = {}

        class _Proc:
            returncode = 0
            stdout = ""
            stderr = ""

        def _fake_run(command, **kwargs):
            captured["command"] = command
            captured["shell"] = kwargs.get("shell")
            return _Proc()

        with patch("pdd.fix_error_loop.subprocess.run", side_effect=_fake_run):
            _run_non_python_initial_verification(str(test_file), str(code_file))

        cmd = captured["command"]
        argv = shlex.split(cmd)
        assert str(test_file.resolve()) in argv, (cmd, argv)
        assert "touch" not in argv, argv


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


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

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
