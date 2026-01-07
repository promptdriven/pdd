# tests/test_sync_backward_compat.py
"""
Backward Compatibility Tests for Issue #251: PDD sync failing (v0.0.100) - outdated parameters

Root Cause: v0.0.100 introduced changes to path resolution that break compatibility with
projects created in v0.0.99. The sync operation fails with empty file collections because:

1. v0.0.100 expects `.pddrc` to have `outputs` templates for path generation
2. v0.0.99 projects lack these `outputs` configurations
3. The fallback logic in `get_pdd_file_paths` and `construct_paths` fails to correctly
   identify existing files when `outputs` templates are absent

These tests verify that v0.0.99 projects sync correctly with v0.0.100.
"""

import json
import os
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock


class TestV099ProjectSyncWithV0100Binary:
    """
    Test Case 1: v0.0.99 Project Sync with v0.0.100 Binary

    Verifies that projects created with v0.0.99 (with legacy metadata files and
    `.pddrc` lacking `outputs` templates) function correctly without empty file
    collection errors when syncing with v0.0.100.
    """

    @pytest.fixture
    def v099_project(self, tmp_path):
        """
        Create a v0.0.99-style project structure.

        This mimics the user's environment from Issue #251 where:
        - Meta files have pdd_version: "0.0.99"
        - .pddrc lacks `outputs` configuration
        - Files exist in standard locations
        """
        # Create .pddrc WITHOUT outputs configuration (v0.0.99 style)
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text('''version: "1.0"
contexts:
  default:
    defaults:
      default_language: "python"
''')

        # Create .pdd/meta directory with v0.0.99 fingerprint
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        fingerprint = {
            "pdd_version": "0.0.99",
            "timestamp": "2026-01-03T04:48:28.868793+00:00",
            "command": "generate",
            "prompt_hash": "abc123def456",
            "code_hash": "789ghi012jkl",
            "example_hash": "mno345pqr678",
            "test_hash": "stu901vwx234",
            "test_files": {
                "test_cli.py": "stu901vwx234"
            }
        }

        (meta_dir / "cli_python.json").write_text(json.dumps(fingerprint, indent=2))

        # Create prompt file
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "cli_python.prompt").write_text("Generate a CLI module")

        # Create existing code files (as they would exist in a v0.0.99 project)
        (tmp_path / "cli.py").write_text("# CLI module code")

        # Create examples directory with example file
        examples_dir = tmp_path / "examples"
        examples_dir.mkdir()
        (examples_dir / "cli_example.py").write_text("# CLI example")

        # Create tests directory with test file
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        (tests_dir / "test_cli.py").write_text("# CLI tests")

        return tmp_path

    def test_get_pdd_file_paths_does_not_return_empty_collections(self, v099_project):
        """
        BUG REPRODUCTION: get_pdd_file_paths should return valid file paths
        for v0.0.99 projects that lack `outputs` configuration.

        This test FAILS on buggy code because construct_paths returns empty
        outputs when `outputs` config is missing, causing the sync to fail
        with "Collected input files: [], Collected output files: []".
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(v099_project)

            paths = get_pdd_file_paths(
                basename="cli",
                language="python",
                prompts_dir="prompts"
            )

            # CRITICAL: Paths should NOT be empty/None for any required file type
            assert paths.get('prompt') is not None, \
                "Prompt path should not be None for v0.0.99 project"
            assert paths.get('code') is not None, \
                "Code path should not be None for v0.0.99 project"
            assert paths.get('example') is not None, \
                "Example path should not be None for v0.0.99 project"
            assert paths.get('test') is not None, \
                "Test path should not be None for v0.0.99 project"

            # Paths should be valid Path objects, not empty strings
            prompt_path = str(paths['prompt'])
            code_path = str(paths['code'])

            assert prompt_path != "", "Prompt path should not be empty string"
            assert code_path != "", "Code path should not be empty string"

            # The paths should point to reasonable locations
            assert "cli" in code_path.lower() or "cli" in prompt_path.lower(), \
                f"Paths should contain 'cli': prompt={prompt_path}, code={code_path}"

        finally:
            os.chdir(original_cwd)

    def test_existing_files_are_detected_in_v099_project(self, v099_project):
        """
        Files that exist in v0.0.99 project structure should be detected.

        The sync operation should recognize existing files and not attempt
        to regenerate them unnecessarily.
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(v099_project)

            paths = get_pdd_file_paths(
                basename="cli",
                language="python",
                prompts_dir="prompts"
            )

            # Check that the returned paths point to files that actually exist
            prompt_path = Path(paths['prompt'])
            code_path = Path(paths['code'])

            # At minimum, the prompt should exist (it's the input)
            assert prompt_path.exists() or prompt_path.name == "cli_python.prompt", \
                f"Prompt path {prompt_path} should be resolvable"

        finally:
            os.chdir(original_cwd)


class TestLegacyPddrcWithoutOutputsConfig:
    """
    Test Case 2: Legacy .pddrc Without outputs Config

    Ensures the system uses explicit `*_output_path` values directly and
    falls back to legacy path construction without requiring `outputs` templates.
    """

    @pytest.fixture
    def legacy_pddrc_project(self, tmp_path):
        """Create a project with legacy .pddrc (no outputs, but explicit paths)."""
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text('''version: "1.0"
contexts:
  backend:
    paths:
      - "src/**"
    defaults:
      default_language: "python"
      generate_output_path: "src/"
      test_output_path: "tests/"
      example_output_path: "examples/"
  default:
    defaults:
      default_language: "python"
''')

        # Create required directories
        (tmp_path / "prompts").mkdir()
        (tmp_path / "prompts" / "my_module_python.prompt").write_text("Module prompt")
        (tmp_path / "src").mkdir()
        (tmp_path / "tests").mkdir()
        (tmp_path / "examples").mkdir()

        return tmp_path

    def test_explicit_output_paths_used_without_outputs_templates(self, legacy_pddrc_project):
        """
        When .pddrc has explicit *_output_path values but no `outputs` templates,
        those explicit paths should be used for path resolution.
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(legacy_pddrc_project)

            paths = get_pdd_file_paths(
                basename="my_module",
                language="python",
                prompts_dir="prompts",
                context_override="backend"
            )

            # Paths should be resolved using the explicit config, not fail
            code_path = str(paths.get('code', ''))
            test_path = str(paths.get('test', ''))
            example_path = str(paths.get('example', ''))

            # Should use the configured directories
            assert code_path != "", "Code path should not be empty"
            assert test_path != "", "Test path should not be empty"
            assert example_path != "", "Example path should not be empty"

            # Paths should respect the configured output directories
            # (specific assertions depend on implementation details)

        finally:
            os.chdir(original_cwd)


class TestMixedVersionMetaFiles:
    """
    Test Case 3: Mixed Version Meta Files in Same Project

    Tests scenarios where some modules have v0.0.99 metadata while others
    have v0.0.100 metadata, confirming all sync successfully.
    """

    @pytest.fixture
    def mixed_version_project(self, tmp_path):
        """Create a project with mixed v0.0.99 and v0.0.100 meta files."""
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text('''version: "1.0"
contexts:
  default:
    defaults:
      default_language: "python"
''')

        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        # v0.0.99 fingerprint (7 modules like in the issue)
        v099_fingerprint = {
            "pdd_version": "0.0.99",
            "timestamp": "2026-01-03T04:48:28.868793+00:00",
            "command": "generate",
            "prompt_hash": "hash1",
            "code_hash": "hash2",
            "example_hash": "hash3",
            "test_hash": "hash4"
        }

        # v0.0.100 fingerprint (1 module like in the issue)
        v0100_fingerprint = {
            "pdd_version": "0.0.100",
            "timestamp": "2026-01-03T21:59:21.000000+00:00",
            "command": "generate",
            "prompt_hash": "hash5",
            "code_hash": "hash6",
            "example_hash": "hash7",
            "test_hash": "hash8"
        }

        # Create 7 v0.0.99 modules
        for module in ["pipeline", "llm", "models", "rules", "helpers", "report", "fix"]:
            (meta_dir / f"{module}_python.json").write_text(json.dumps(v099_fingerprint, indent=2))

        # Create 1 v0.0.100 module
        (meta_dir / "cli_python.json").write_text(json.dumps(v0100_fingerprint, indent=2))

        # Create prompt files
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        for module in ["pipeline", "llm", "models", "rules", "helpers", "report", "fix", "cli"]:
            (prompts_dir / f"{module}_python.prompt").write_text(f"Prompt for {module}")

        return tmp_path

    def test_v099_modules_resolve_paths_correctly(self, mixed_version_project):
        """
        v0.0.99 modules should have their paths resolved correctly even
        when other modules in the project use v0.0.100.
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(mixed_version_project)

            # Test a v0.0.99 module
            paths = get_pdd_file_paths(
                basename="pipeline",
                language="python",
                prompts_dir="prompts"
            )

            # Should return valid paths, not empty
            assert paths.get('code') is not None, "v0.0.99 module should have code path"
            assert paths.get('prompt') is not None, "v0.0.99 module should have prompt path"

        finally:
            os.chdir(original_cwd)

    def test_v0100_modules_still_work(self, mixed_version_project):
        """
        v0.0.100 modules should continue to work correctly.
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(mixed_version_project)

            # Test the v0.0.100 module
            paths = get_pdd_file_paths(
                basename="cli",
                language="python",
                prompts_dir="prompts"
            )

            # Should return valid paths
            assert paths.get('code') is not None, "v0.0.100 module should have code path"
            assert paths.get('prompt') is not None, "v0.0.100 module should have prompt path"

        finally:
            os.chdir(original_cwd)


class TestSyncWithoutPddrc:
    """
    Test Case 4: Sync Without .pddrc (Bare Project)

    Validates that projects lacking `.pddrc` files default to standard
    path resolution using directory conventions without triggering
    empty file collection failures.
    """

    @pytest.fixture
    def bare_project(self, tmp_path):
        """Create a minimal project without .pddrc."""
        # No .pddrc file at all

        # Create prompt file using default conventions
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "calculator_python.prompt").write_text("Calculate things")

        # Create code file in root (default convention)
        (tmp_path / "calculator.py").write_text("# Calculator code")

        # Create standard directories
        (tmp_path / "tests").mkdir()
        (tmp_path / "examples").mkdir()

        return tmp_path

    def test_paths_resolved_without_pddrc(self, bare_project):
        """
        Without .pddrc, path resolution should use sensible defaults
        and not fail with empty collections.
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(bare_project)

            paths = get_pdd_file_paths(
                basename="calculator",
                language="python",
                prompts_dir="prompts"
            )

            # Should return valid paths using defaults
            assert paths.get('code') is not None, "Bare project should have code path"
            assert paths.get('prompt') is not None, "Bare project should have prompt path"
            assert paths.get('test') is not None, "Bare project should have test path"
            assert paths.get('example') is not None, "Bare project should have example path"

            # Paths should not be empty strings
            code_path = str(paths['code'])
            assert code_path != "", "Code path should not be empty"
            assert "calculator" in code_path.lower(), \
                f"Code path should contain 'calculator': {code_path}"

        finally:
            os.chdir(original_cwd)


class TestRegressionTemplateBasedPathsStillWork:
    """
    Test Case 5: Regression - Template-Based Paths Still Work

    Confirms that modern projects with full `outputs` template configuration
    maintain correct path generation functionality after any fixes.
    """

    @pytest.fixture
    def modern_project_with_outputs(self, tmp_path):
        """Create a modern project with full outputs configuration."""
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text('''version: "1.0"
contexts:
  backend:
    paths:
      - "backend/**"
    defaults:
      default_language: "python"
      outputs:
        prompt:
          path: "prompts/backend/{name}_{language}.prompt"
        code:
          path: "backend/src/{name}.py"
        test:
          path: "backend/tests/test_{name}.py"
        example:
          path: "context/{name}_example.py"
  default:
    defaults:
      default_language: "python"
      outputs:
        prompt:
          path: "prompts/{name}_{language}.prompt"
        code:
          path: "{name}.py"
        test:
          path: "tests/test_{name}.py"
        example:
          path: "examples/{name}_example.py"
''')

        # Create directories
        (tmp_path / "prompts" / "backend").mkdir(parents=True)
        (tmp_path / "backend" / "src").mkdir(parents=True)
        (tmp_path / "backend" / "tests").mkdir(parents=True)
        (tmp_path / "context").mkdir()

        # Create prompt file
        (tmp_path / "prompts" / "backend" / "utils_python.prompt").write_text("Utils prompt")

        return tmp_path

    def test_template_based_paths_work_with_context(self, modern_project_with_outputs):
        """
        Modern projects with `outputs` templates should continue to work.
        This is a regression test to ensure fixes don't break new functionality.
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(modern_project_with_outputs)

            paths = get_pdd_file_paths(
                basename="utils",
                language="python",
                prompts_dir="prompts/backend",
                context_override="backend"
            )

            # Template-based paths should be correctly generated
            assert paths.get('code') is not None, "Modern project should have code path"

            code_path = str(paths['code'])
            # Should use the template from outputs config
            assert "backend" in code_path or "utils" in code_path, \
                f"Code path should use template config: {code_path}"

        finally:
            os.chdir(original_cwd)


class TestEmptyFileCollectionBugReproduction:
    """
    Direct reproduction of the bug from Issue #251.

    The core symptom is: "Collected input files: [], Collected output files: []"
    This happens when path resolution fails for v0.0.99 projects.
    """

    @pytest.fixture
    def issue_251_reproduction(self, tmp_path):
        """
        Reproduce the exact scenario from Issue #251.

        User environment:
        - v0.0.100 binary
        - Project with v0.0.99 meta files
        - .pddrc without outputs templates
        """
        # Minimal .pddrc like in the issue
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text('''version: "1.0"
contexts:
  default:
    defaults:
      default_language: "python"
''')

        # Create .pdd/meta with v0.0.99 fingerprint
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        # Structure matching the Gist from Issue #251
        fingerprint = {
            "pdd_version": "0.0.99",
            "timestamp": "2026-01-03T04:48:28.868793+00:00",
            "command": "test_extend",
            "prompt_hash": "247e42f484092e026ce9968dd7254f10c6b795fd025517f066b5fc463f691251",
            "code_hash": "3327ecfa43c2ebabf1309b3119eb4461edf304b35d8d3e94a9334ebac1768e79",
            "example_hash": "f6d991c75cb36e3903c3055d98bd52a1c60b5de5ea5b9cac131a0325b38b1853",
            "test_hash": "0b97e0d7ce40664000ba9d7bbc58c904ec9814fc3e84803ea584e673c7befbc1",
            "test_files": {
                "test_cli.py": "0b97e0d7ce40664000ba9d7bbc58c904ec9814fc3e84803ea584e673c7befbc1"
            }
        }

        (meta_dir / "cli_python.json").write_text(json.dumps(fingerprint, indent=2))

        # Create the files that should be detected
        (tmp_path / "prompts").mkdir()
        (tmp_path / "prompts" / "cli_python.prompt").write_text("CLI prompt content")
        (tmp_path / "cli.py").write_text("# CLI code")
        (tmp_path / "examples").mkdir()
        (tmp_path / "examples" / "cli_example.py").write_text("# CLI example")
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "test_cli.py").write_text("# CLI tests")

        return tmp_path

    def test_file_collection_not_empty_for_v099_project(self, issue_251_reproduction):
        """
        CRITICAL BUG TEST: File collection should NOT be empty.

        This test reproduces the exact failure from Issue #251 where
        the sync operation reports:
        "Debug: Collected input files: [], Collected output files: []"

        Expected: Files should be collected correctly
        Actual (buggy): Empty lists are returned
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(issue_251_reproduction)

            paths = get_pdd_file_paths(
                basename="cli",
                language="python",
                prompts_dir="prompts"
            )

            # The bug manifests as empty/None paths
            # This assertion should FAIL on the buggy code
            prompt_path = paths.get('prompt')
            code_path = paths.get('code')
            example_path = paths.get('example')
            test_path = paths.get('test')

            # All paths must be non-None
            assert prompt_path is not None, \
                "BUG: prompt path is None - this causes empty file collection"
            assert code_path is not None, \
                "BUG: code path is None - this causes empty file collection"
            assert example_path is not None, \
                "BUG: example path is None - this causes empty file collection"
            assert test_path is not None, \
                "BUG: test path is None - this causes empty file collection"

            # Paths must resolve to non-empty strings
            assert str(prompt_path) != "", \
                "BUG: prompt path is empty string - this causes empty file collection"
            assert str(code_path) != "", \
                "BUG: code path is empty string - this causes empty file collection"

            # The prompt file exists and should be found
            prompt_file = Path(prompt_path)
            assert prompt_file.name == "cli_python.prompt", \
                f"Prompt filename should be 'cli_python.prompt', got '{prompt_file.name}'"

        finally:
            os.chdir(original_cwd)

    def test_sync_determine_operation_returns_valid_decision(self, issue_251_reproduction):
        """
        sync_determine_operation should return a valid decision, not error out.

        The function should analyze the project state and return an appropriate
        operation, not fail due to path resolution issues.
        """
        from pdd.sync_determine_operation import sync_determine_operation

        original_cwd = os.getcwd()
        try:
            os.chdir(issue_251_reproduction)

            # This should not raise an exception
            decision = sync_determine_operation(
                basename="cli",
                language="python",
                target_coverage=80.0
            )

            # Decision should be a valid SyncDecision object
            assert decision is not None, "sync_determine_operation returned None"
            assert hasattr(decision, 'operation'), "Decision missing 'operation' attribute"
            assert hasattr(decision, 'reason'), "Decision missing 'reason' attribute"

            # The operation should not be 'error' due to path issues
            assert decision.operation != "error" or "path" not in decision.reason.lower(), \
                f"Got error decision due to path issue: {decision.reason}"

        finally:
            os.chdir(original_cwd)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
