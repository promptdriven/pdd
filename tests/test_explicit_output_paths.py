"""
TDD tests for explicit output path handling.

Bug: When .pddrc has explicit output paths ending with /, these should be
used DIRECTLY without adding dir_prefix from the basename.

Issue: Running `pdd sync backend/utils/credit_helpers` with config:
    generate_output_path: "backend/functions/utils/"
    example_output_path: "context/"

Expected:
    code: backend/functions/utils/credit_helpers.py
    example: context/credit_helpers_example.py

Actual (broken):
    code: backend/utils/credit_helpers.py
    example: context/backend/utils/credit_helpers_example.py
"""
import os
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock


class TestExplicitOutputPaths:
    """Tests for using explicit config paths without dir_prefix."""

    @pytest.fixture
    def backend_utils_project(self, tmp_path):
        """Create a project with .pddrc containing backend-utils context."""
        # Create .pddrc
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text('''version: "1.0"
contexts:
  backend-utils:
    paths:
      - "backend/functions/utils/**"
    defaults:
      prompts_dir: "prompts/backend/utils"
      generate_output_path: "backend/functions/utils/"
      test_output_path: "backend/tests/"
      example_output_path: "context/"
      default_language: "python"
''')

        # Create prompt file
        prompt_dir = tmp_path / "prompts" / "backend" / "utils"
        prompt_dir.mkdir(parents=True)
        prompt_file = prompt_dir / "credit_helpers_python.prompt"
        prompt_file.write_text("Generate credit helpers module")

        # Create directories that would be expected
        (tmp_path / "backend" / "functions" / "utils").mkdir(parents=True)
        (tmp_path / "context").mkdir(parents=True)
        (tmp_path / "backend" / "tests").mkdir(parents=True)

        return tmp_path

    def test_code_path_uses_generate_output_path_directly(self, backend_utils_project):
        """
        Regression test: code path should use generate_output_path directly.

        When syncing "backend/utils/credit_helpers" with config:
            generate_output_path: "backend/functions/utils/"

        Expected: backend/functions/utils/credit_helpers.py
        Previously broken: backend/utils/credit_helpers.py (was using dir_prefix)
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(backend_utils_project)

            paths = get_pdd_file_paths(
                basename="backend/utils/credit_helpers",
                language="python",
                prompts_dir="prompts/backend/utils",
                context_override="backend-utils"
            )

            # The code path should use generate_output_path directly
            # NOT dir_prefix (backend/utils/) from the basename
            code_path = str(paths['code'])

            # Path may be absolute or relative, check the suffix
            assert code_path.endswith("backend/functions/utils/credit_helpers.py"), \
                f"Expected path ending with 'backend/functions/utils/credit_helpers.py' but got '{code_path}'. " \
                f"The generate_output_path config should be used directly, not dir_prefix."

        finally:
            os.chdir(original_cwd)

    def test_example_path_uses_example_output_path_directly(self, backend_utils_project):
        """
        Regression test: example path should use example_output_path directly.

        When syncing "backend/utils/credit_helpers" with config:
            example_output_path: "context/"

        Expected: context/credit_helpers_example.py
        Previously broken: context/backend/utils/credit_helpers_example.py
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(backend_utils_project)

            paths = get_pdd_file_paths(
                basename="backend/utils/credit_helpers",
                language="python",
                prompts_dir="prompts/backend/utils",
                context_override="backend-utils"
            )

            # The example path should use example_output_path directly
            # NOT add dir_prefix (backend/utils/) from the basename
            example_path = str(paths['example'])

            # Path may be absolute or relative, check the suffix
            assert example_path.endswith("context/credit_helpers_example.py"), \
                f"Expected path ending with 'context/credit_helpers_example.py' but got '{example_path}'. " \
                f"The example_output_path config should be used directly, not with dir_prefix added."

        finally:
            os.chdir(original_cwd)

    def test_test_path_uses_test_output_path_directly(self, backend_utils_project):
        """
        Regression test: test path should use test_output_path directly.

        When syncing "backend/utils/credit_helpers" with config:
            test_output_path: "backend/tests/"

        Expected: backend/tests/test_credit_helpers.py
        Previously broken: backend/tests/backend/utils/test_credit_helpers.py
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(backend_utils_project)

            paths = get_pdd_file_paths(
                basename="backend/utils/credit_helpers",
                language="python",
                prompts_dir="prompts/backend/utils",
                context_override="backend-utils"
            )

            # The test path should use test_output_path directly
            test_path = str(paths['test'])

            # Path may be absolute or relative, check the suffix
            assert test_path.endswith("backend/tests/test_credit_helpers.py"), \
                f"Expected path ending with 'backend/tests/test_credit_helpers.py' but got '{test_path}'. " \
                f"The test_output_path config should be used directly, not with dir_prefix added."

        finally:
            os.chdir(original_cwd)

    def test_examples_dir_uses_root_for_scanning(self, backend_utils_project):
        """
        For auto-deps scanning, examples_dir should be the ROOT directory only.

        When example_output_path is "context/", examples_dir should be "context"
        (not "context/backend/utils/" or similar with subdirectory structure).
        """
        from pdd.construct_paths import construct_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(backend_utils_project)

            prompt_file = backend_utils_project / "prompts" / "backend" / "utils" / "credit_helpers_python.prompt"

            resolved_config, _, _, _ = construct_paths(
                input_file_paths={"prompt_file": str(prompt_file)},
                force=True,
                quiet=True,
                command="sync",
                command_options={"basename": "backend/utils/credit_helpers"},
                context_override="backend-utils"
            )

            examples_dir = resolved_config.get("examples_dir", "")

            # examples_dir should be just "context" for scanning all examples
            assert examples_dir == "context", \
                f"Expected examples_dir='context' for scanning, but got '{examples_dir}'. " \
                f"Auto-deps should scan the ROOT examples directory, not a subdirectory."

        finally:
            os.chdir(original_cwd)


class TestBackwardsCompatibility:
    """Ensure old behavior works when explicit paths are not configured."""

    @pytest.fixture
    def minimal_project(self, tmp_path):
        """Create a project without explicit output paths."""
        # Create minimal .pddrc without explicit paths
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text('''version: "1.0"
contexts:
  default:
    defaults:
      default_language: "python"
''')

        # Create prompt file
        prompt_dir = tmp_path / "prompts" / "subdir"
        prompt_dir.mkdir(parents=True)
        prompt_file = prompt_dir / "my_module_python.prompt"
        prompt_file.write_text("Generate module")

        return tmp_path

    def test_dir_prefix_used_when_no_explicit_path(self, minimal_project):
        """
        When no explicit output paths are configured, dir_prefix should be used.
        This maintains backwards compatibility with old projects.
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(minimal_project)

            paths = get_pdd_file_paths(
                basename="subdir/my_module",
                language="python",
                prompts_dir="prompts/subdir"
            )

            # Without explicit paths, dir_prefix should be used
            code_path = str(paths['code'])

            # Should include subdir/ in the path (old behavior)
            assert "subdir" in code_path or code_path.startswith("./subdir"), \
                f"Expected dir_prefix 'subdir/' to be used for backwards compatibility, got '{code_path}'"

        finally:
            os.chdir(original_cwd)
