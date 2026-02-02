# tests/test_sync_template_prompt_discovery.py
"""
Tests for template-based prompt discovery in pdd sync.

Issue: When .pddrc has outputs.prompt.path configured for a context,
pdd sync should be able to find prompts using that template even when
the basename alone doesn't match the context's path patterns.

Example:
- .pddrc has backend-utils context with:
    outputs:
      prompt:
        path: "prompts/backend/utils/{name}_{language}.prompt"
- Prompt exists at: prompts/backend/utils/credit_helpers_python.prompt
- User runs: pdd sync credit_helpers
- Expected: Finds the prompt and uses backend-utils context
- Actual (bug): Looks in prompts/credit_helpers_python.prompt and fails

These tests should FAIL until the fix is implemented.
"""

import pytest
import os
from pathlib import Path
from unittest.mock import patch, MagicMock


def _make_frontend_context_project(tmp_path: Path, prompt_subdir: str = "app/sales") -> Path:
    """Create a project with .pddrc frontend context and a prompt in a subdirectory.

    Args:
        tmp_path: Temporary directory root.
        prompt_subdir: Subdirectory under prompts/frontend/ for the prompt file.

    Returns:
        The tmp_path root.
    """
    pddrc_content = """
version: "1.0"
contexts:
  frontend:
    paths:
      - "frontend/**"
      - "prompts/frontend/**"
    defaults:
      default_language: "typescriptreact"
      outputs:
        prompt:
          path: "prompts/frontend/{category}/{name}_{language}.prompt"
        code:
          path: "frontend/src/{category}/{name}.tsx"
  default:
    defaults:
      default_language: "python"
"""
    (tmp_path / ".pddrc").write_text(pddrc_content)

    prompt_dir = tmp_path / "prompts" / "frontend" / prompt_subdir
    prompt_dir.mkdir(parents=True)
    (prompt_dir / "page_TypescriptReact.prompt").write_text("# Sales page")

    return tmp_path


class TestTemplateBasedPromptDiscovery:
    """Test that sync can find prompts using outputs.prompt.path templates."""

    @pytest.fixture
    def pddrc_with_outputs(self, tmp_path):
        """Create a .pddrc with outputs configuration for prompt paths."""
        pddrc_content = """
version: "1.0"
contexts:
  backend-utils:
    paths:
      - "backend/functions/utils/**"
    defaults:
      default_language: "python"
      outputs:
        prompt:
          path: "prompts/backend/utils/{name}_{language}.prompt"
        code:
          path: "backend/functions/utils/{name}.py"
        test:
          path: "backend/tests/test_{name}.py"
        example:
          path: "context/backend/{name}_example.py"

  default:
    defaults:
      default_language: "python"
"""
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(pddrc_content)

        # Create the prompt file in the configured location
        prompts_dir = tmp_path / "prompts" / "backend" / "utils"
        prompts_dir.mkdir(parents=True, exist_ok=True)
        prompt_file = prompts_dir / "credit_helpers_python.prompt"
        prompt_file.write_text("# Test prompt for credit_helpers")

        return tmp_path

    def test_finds_prompt_using_outputs_template(self, pddrc_with_outputs):
        """
        BUG: pdd sync credit_helpers should find prompts/backend/utils/credit_helpers_python.prompt
        by searching through contexts with outputs.prompt.path configured.

        Currently fails because sync only looks in the default prompts/ directory.
        """
        from pdd.sync_main import _find_prompt_in_contexts

        original_cwd = os.getcwd()
        try:
            os.chdir(pddrc_with_outputs)

            # This function should exist and find the prompt
            result = _find_prompt_in_contexts('credit_helpers')

            assert result is not None, \
                "Should find prompt using outputs.prompt.path template"

            context_name, prompt_path, language = result
            assert context_name == 'backend-utils', \
                f"Should match backend-utils context, got {context_name}"
            assert language == 'python', \
                f"Should detect python language, got {language}"
            assert prompt_path.exists(), \
                f"Prompt path should exist: {prompt_path}"
            assert 'credit_helpers_python.prompt' in str(prompt_path), \
                f"Should find credit_helpers prompt, got {prompt_path}"
        finally:
            os.chdir(original_cwd)

    def test_detect_languages_uses_template_when_context_known(self, pddrc_with_outputs):
        """
        When context is known, _detect_languages_with_context should use the
        outputs.prompt.path template to find available languages.
        """
        from pdd.sync_main import _detect_languages_with_context

        original_cwd = os.getcwd()
        try:
            os.chdir(pddrc_with_outputs)

            # With context name, should find languages using template
            languages = _detect_languages_with_context(
                basename='credit_helpers',
                prompts_dir=Path('prompts'),  # This shouldn't matter when context is set
                context_name='backend-utils'
            )

            assert 'python' in languages, \
                f"Should detect python language from template path, got {languages}"
        finally:
            os.chdir(original_cwd)

    def test_detect_languages_with_subdirectory_basename(self, tmp_path):
        """
        Bug: _detect_languages uses full basename (including path) in glob pattern.

        When basename='frontend/components/types/marketplace' and
        prompts_dir='prompts/frontend/components/types', the glob pattern becomes
        'frontend/components/types/marketplace_*.prompt' which looks for a nested
        path that doesn't exist.

        The pattern should use only the name part ('marketplace'), not the full basename.
        """
        # Create prompt file with capitalized language (also tests case insensitivity)
        prompts_dir = tmp_path / "prompts" / "frontend" / "components" / "types"
        prompts_dir.mkdir(parents=True)
        (prompts_dir / "marketplace_Typescript.prompt").write_text("# Marketplace types")

        from pdd.sync_main import _detect_languages

        # Test _detect_languages directly with subdirectory basename
        languages = _detect_languages(
            basename='frontend/components/types/marketplace',
            prompts_dir=prompts_dir
        )

        assert 'typescript' in languages, \
            f"Should find typescript with subdirectory basename, got {list(languages.keys())}"

    def test_fallback_to_directory_scan_when_no_outputs_config(self, tmp_path):
        """
        When context doesn't have outputs.prompt.path, should fall back to
        scanning the prompts_dir directory directly.
        """
        # Create .pddrc without outputs config
        pddrc_content = """
version: "1.0"
contexts:
  backend:
    paths:
      - "backend/**"
    defaults:
      prompts_dir: "prompts"
      default_language: "python"
  default:
    defaults:
      default_language: "python"
"""
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(pddrc_content)

        # Create prompt in default location
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(parents=True, exist_ok=True)
        prompt_file = prompts_dir / "my_module_python.prompt"
        prompt_file.write_text("# Test prompt")

        from pdd.sync_main import _detect_languages

        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)

            # Should still work with directory scanning
            languages = _detect_languages('my_module', prompts_dir)
            assert 'python' in languages, \
                f"Should find python via directory scan, got {languages}"
        finally:
            os.chdir(original_cwd)

    def test_sync_uses_correct_output_paths_when_context_matched(self, pddrc_with_outputs):
        """
        When sync finds a prompt via template discovery, it should use the
        matching context's output paths for code, test, and example files.
        """
        from pdd.sync_main import _find_prompt_in_contexts
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(pddrc_with_outputs)

            # First, find the prompt and get the context
            result = _find_prompt_in_contexts('credit_helpers')
            assert result is not None, "Should find prompt"

            context_name, prompt_path, language = result

            # Then verify the output paths use the correct context
            paths = get_pdd_file_paths(
                basename='credit_helpers',
                language='python',
                prompts_dir='prompts',
                context_override=context_name  # Use the discovered context
            )

            # Should use backend-utils context output paths
            assert 'backend/functions/utils/credit_helpers.py' in str(paths.get('code', '')), \
                f"Code should go to backend/functions/utils/, got {paths.get('code')}"
            assert 'backend/tests/test_credit_helpers.py' in str(paths.get('test', '')), \
                f"Test should go to backend/tests/, got {paths.get('test')}"
        finally:
            os.chdir(original_cwd)


class TestPromptDiscoveryEdgeCases:
    """Edge cases for template-based prompt discovery."""

    @pytest.fixture
    def multi_context_pddrc(self, tmp_path):
        """Create .pddrc with multiple contexts having outputs.prompt.path."""
        pddrc_content = """
version: "1.0"
contexts:
  backend-utils:
    paths:
      - "backend/functions/utils/**"
    defaults:
      default_language: "python"
      outputs:
        prompt:
          path: "prompts/backend/utils/{name}_{language}.prompt"
        code:
          path: "backend/functions/utils/{name}.py"

  frontend-components:
    paths:
      - "frontend/components/**"
    defaults:
      default_language: "typescript"
      outputs:
        prompt:
          path: "prompts/frontend/components/{name}_{language}.prompt"
        code:
          path: "frontend/src/components/{name}/{name}.tsx"

  default:
    defaults:
      default_language: "python"
"""
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(pddrc_content)

        # Create prompts in both locations
        backend_prompts = tmp_path / "prompts" / "backend" / "utils"
        backend_prompts.mkdir(parents=True, exist_ok=True)
        (backend_prompts / "helper_python.prompt").write_text("# Backend helper")

        frontend_prompts = tmp_path / "prompts" / "frontend" / "components"
        frontend_prompts.mkdir(parents=True, exist_ok=True)
        (frontend_prompts / "Button_typescript.prompt").write_text("# Button component")

        return tmp_path

    def test_finds_correct_context_for_backend_prompt(self, multi_context_pddrc):
        """Should find backend-utils context for backend prompts."""
        from pdd.sync_main import _find_prompt_in_contexts

        original_cwd = os.getcwd()
        try:
            os.chdir(multi_context_pddrc)

            result = _find_prompt_in_contexts('helper')
            assert result is not None
            context_name, _, language = result
            assert context_name == 'backend-utils'
            assert language == 'python'
        finally:
            os.chdir(original_cwd)

    def test_finds_correct_context_for_frontend_prompt(self, multi_context_pddrc):
        """Should find frontend-components context for frontend prompts."""
        from pdd.sync_main import _find_prompt_in_contexts

        original_cwd = os.getcwd()
        try:
            os.chdir(multi_context_pddrc)

            result = _find_prompt_in_contexts('Button')
            assert result is not None
            context_name, _, language = result
            assert context_name == 'frontend-components'
            assert language == 'typescript'
        finally:
            os.chdir(original_cwd)

    def test_returns_none_when_no_matching_prompt(self, multi_context_pddrc):
        """Should return None when no prompt matches any context template."""
        from pdd.sync_main import _find_prompt_in_contexts

        original_cwd = os.getcwd()
        try:
            os.chdir(multi_context_pddrc)

            result = _find_prompt_in_contexts('nonexistent_module')
            assert result is None, "Should return None for nonexistent prompt"
        finally:
            os.chdir(original_cwd)


class TestPromptDiscoveryWithCategory:
    """Template discovery should handle category paths from context patterns."""

    @pytest.fixture
    def frontend_components_pddrc(self, tmp_path):
        pddrc_content = """
version: "1.0"
contexts:
  frontend-components:
    paths:
      - "frontend/components/**"
    defaults:
      default_language: "typescriptreact"
      outputs:
        prompt:
          path: "prompts/frontend/components/{category}/{name}_{language}.prompt"
        code:
          path: "frontend/src/components/{category}/{name}/{name}.tsx"
        example:
          path: "context/frontend/{name}_example.tsx"

  default:
    defaults:
      default_language: "python"
"""
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(pddrc_content)

        prompt_path = (
            tmp_path
            / "prompts"
            / "frontend"
            / "components"
            / "marketplace"
            / "AssetCard_typescriptreact.prompt"
        )
        prompt_path.parent.mkdir(parents=True, exist_ok=True)
        prompt_path.write_text("# AssetCard prompt")

        return tmp_path

    def test_sync_main_finds_prompt_with_category_context_prefix(self, frontend_components_pddrc):
        from pdd.sync_main import _find_prompt_in_contexts

        original_cwd = os.getcwd()
        try:
            os.chdir(frontend_components_pddrc)

            result = _find_prompt_in_contexts("frontend/components/marketplace/AssetCard")
            assert result is not None

            context_name, prompt_path, language = result
            assert context_name == "frontend-components"
            assert language == "typescriptreact"
            assert prompt_path.exists()
            assert str(prompt_path).endswith(
                "prompts/frontend/components/marketplace/AssetCard_typescriptreact.prompt"
            )
        finally:
            os.chdir(original_cwd)

    def test_sync_main_detect_languages_with_category_context_prefix(self, frontend_components_pddrc):
        from pdd.sync_main import _detect_languages_with_context

        original_cwd = os.getcwd()
        try:
            os.chdir(frontend_components_pddrc)

            languages = _detect_languages_with_context(
                basename="frontend/components/marketplace/AssetCard",
                prompts_dir=Path("prompts"),
                context_name="frontend-components",
            )

            assert "typescriptreact" in languages
        finally:
            os.chdir(original_cwd)


class TestPathResolutionBug:
    """Test that paths are resolved relative to .pddrc location, not CWD."""

    @pytest.fixture
    def pddrc_with_outputs(self, tmp_path):
        """Create a .pddrc with outputs configuration for prompt paths."""
        pddrc_content = """
version: "1.0"
contexts:
  backend-utils:
    paths:
      - "backend/functions/utils/**"
    defaults:
      default_language: "python"
      outputs:
        prompt:
          path: "prompts/backend/utils/{name}_{language}.prompt"
        code:
          path: "backend/functions/utils/{name}.py"
        test:
          path: "backend/tests/test_{name}.py"
        example:
          path: "context/backend/{name}_example.py"

  default:
    defaults:
      default_language: "python"
"""
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(pddrc_content)

        # Create the prompt file in the configured location
        prompts_dir = tmp_path / "prompts" / "backend" / "utils"
        prompts_dir.mkdir(parents=True, exist_ok=True)
        prompt_file = prompts_dir / "credit_helpers_python.prompt"
        prompt_file.write_text("# Test prompt for credit_helpers")

        return tmp_path

    def test_finds_prompt_when_running_from_subdirectory(self, pddrc_with_outputs):
        """
        BUG FIX: Should find prompts even when CWD is a subdirectory of project root.

        The bug was that paths were resolved relative to CWD instead of .pddrc location.
        This test runs from a subdirectory to catch the bug.
        """
        from pdd.sync_main import _find_prompt_in_contexts

        # Create a subdirectory to run from
        subdir = pddrc_with_outputs / "some_subdir"
        subdir.mkdir()

        original_cwd = os.getcwd()
        try:
            os.chdir(subdir)  # Run from subdirectory, not project root

            result = _find_prompt_in_contexts('credit_helpers')

            assert result is not None, \
                "Should find prompt even when running from subdirectory"

            context_name, prompt_path, language = result
            assert context_name == 'backend-utils', \
                f"Should match backend-utils context, got {context_name}"
            assert language == 'python', \
                f"Should detect python language, got {language}"
            assert prompt_path.exists(), \
                f"Prompt path should exist: {prompt_path}"
        finally:
            os.chdir(original_cwd)

    def test_detect_languages_works_from_subdirectory(self, pddrc_with_outputs):
        """
        BUG FIX: _detect_languages_with_context should work from subdirectory too.
        """
        from pdd.sync_main import _detect_languages_with_context

        # Create a subdirectory to run from
        subdir = pddrc_with_outputs / "some_subdir"
        subdir.mkdir()

        original_cwd = os.getcwd()
        try:
            os.chdir(subdir)  # Run from subdirectory

            languages = _detect_languages_with_context(
                basename='credit_helpers',
                prompts_dir=Path('prompts'),
                context_name='backend-utils'
            )

            assert 'python' in languages, \
                f"Should detect python language from subdirectory, got {languages}"
        finally:
            os.chdir(original_cwd)

    def test_sync_uses_correct_example_path(self, pddrc_with_outputs):
        """
        Example output should use outputs.example.path template.
        Verifies example goes to context/backend/credit_helpers_example.py
        """
        from pdd.sync_main import _find_prompt_in_contexts
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(pddrc_with_outputs)

            # First, find the prompt and get the context
            result = _find_prompt_in_contexts('credit_helpers')
            assert result is not None, "Should find prompt"

            context_name, prompt_path, language = result

            # Then verify the output paths use the correct context
            paths = get_pdd_file_paths(
                basename='credit_helpers',
                language='python',
                prompts_dir='prompts',
                context_override=context_name
            )

            # Should use backend-utils context output paths for example
            example_path = str(paths.get('example', ''))
            assert 'context/backend/credit_helpers_example.py' in example_path, \
                f"Example should go to context/backend/, got {example_path}"
        finally:
            os.chdir(original_cwd)

    def test_paths_correct_when_prompt_exists(self, pddrc_with_outputs):
        """
        BUG FIX: When prompt file EXISTS, outputs config should still be used.

        The bug was that get_pdd_file_paths only checks outputs config when
        prompt doesn't exist. When prompt EXISTS, it falls back to legacy paths.

        This test uses prompts_dir that makes the prompt file EXIST to trigger
        the bug.
        """
        from pdd.sync_main import _find_prompt_in_contexts
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(pddrc_with_outputs)

            # First, find the prompt and get the context
            result = _find_prompt_in_contexts('credit_helpers')
            assert result is not None, "Should find prompt"

            context_name, prompt_path, language = result

            # Use prompts_dir that makes prompt file EXIST
            # This is what sync_main does: prompts_dir = discovered_prompt_path.parent
            actual_prompts_dir = str(prompt_path.parent)

            paths = get_pdd_file_paths(
                basename='credit_helpers',
                language='python',
                prompts_dir=actual_prompts_dir,  # Makes prompt file EXIST
                context_override=context_name
            )

            # Should use backend-utils context output paths even when prompt EXISTS
            code_path = str(paths.get('code', ''))
            example_path = str(paths.get('example', ''))
            test_path = str(paths.get('test', ''))

            assert 'backend/functions/utils/credit_helpers.py' in code_path, \
                f"Code should go to backend/functions/utils/, got {code_path}"
            assert 'context/backend/credit_helpers_example.py' in example_path, \
                f"Example should go to context/backend/, got {example_path}"
            assert 'backend/tests/test_credit_helpers.py' in test_path, \
                f"Test should go to backend/tests/, got {test_path}"
        finally:
            os.chdir(original_cwd)

    def test_get_pdd_file_paths_returns_only_path_objects(self, pddrc_with_outputs):
        """
        BUG FIX: get_pdd_file_paths should only return Path objects, not strings.

        The function signature is -> Dict[str, Path]. Adding _matched_context (a string)
        violates this contract and breaks sync_orchestration.py:1599 which calls
        .exists() on all values.
        """
        from pdd.sync_main import _find_prompt_in_contexts
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(pddrc_with_outputs)

            result = _find_prompt_in_contexts('credit_helpers')
            context_name, prompt_path, language = result
            actual_prompts_dir = str(prompt_path.parent)

            paths = get_pdd_file_paths(
                basename='credit_helpers',
                language='python',
                prompts_dir=actual_prompts_dir,
                context_override=context_name
            )

            # All values (except test_files which is a list) should be Path objects
            for key, value in paths.items():
                if key == 'test_files':
                    continue
                assert isinstance(value, Path), \
                    f"pdd_files['{key}'] should be Path, got {type(value).__name__}: {value}"
        finally:
            os.chdir(original_cwd)


class TestExamplesDirFromOutputsTemplate:
    """Test that examples_dir is correctly extracted from outputs.example.path template."""

    @pytest.fixture
    def pddrc_with_outputs(self, tmp_path):
        """Create a .pddrc with outputs configuration for all paths."""
        pddrc_content = """
version: "1.0"
contexts:
  backend-utils:
    paths:
      - "backend/functions/utils/**"
    defaults:
      default_language: "python"
      outputs:
        prompt:
          path: "prompts/backend/utils/{name}_{language}.prompt"
        code:
          path: "backend/functions/utils/{name}.py"
        test:
          path: "backend/tests/test_{name}.py"
        example:
          path: "context/backend/{name}_example.py"

  default:
    defaults:
      default_language: "python"
"""
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(pddrc_content)

        # Create the prompt file in the configured location
        prompts_dir = tmp_path / "prompts" / "backend" / "utils"
        prompts_dir.mkdir(parents=True, exist_ok=True)
        prompt_file = prompts_dir / "credit_helpers_python.prompt"
        prompt_file.write_text("# Test prompt for credit_helpers")

        # Create example file at template-based location
        examples_dir = tmp_path / "context" / "backend"
        examples_dir.mkdir(parents=True, exist_ok=True)
        (examples_dir / "credit_helpers_example.py").write_text(
            "# Example file for credit_helpers\nprint('hello')\n"
        )

        return tmp_path

    def test_construct_paths_sets_examples_dir_default(self, pddrc_with_outputs):
        """
        examples_dir should default to "context" for auto-deps scanning.

        NOTE: outputs.example.path is for OUTPUT only (where to write examples),
        NOT for determining scan scope. Using it for scan scope caused CSV row
        deletion issues when syncing context-scoped modules.

        The examples_dir should fall back to "context" as the sensible default.
        """
        from pdd.sync_main import _find_prompt_in_contexts
        from pdd.construct_paths import construct_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(pddrc_with_outputs)

            # First find the prompt to get the context
            result = _find_prompt_in_contexts('credit_helpers')
            assert result is not None, "Should find prompt via template"
            context_name, prompt_path, language = result

            # Call construct_paths with sync command (same as sync_main.py does)
            resolved_config, _, _, _ = construct_paths(
                input_file_paths={"prompt_file": str(prompt_path)},
                force=True,
                quiet=True,
                command="sync",
                command_options={"basename": "credit_helpers", "language": "python"},
                context_override=context_name,
            )

            # examples_dir should default to "context", NOT be derived from outputs.example.path
            examples_dir = resolved_config.get("examples_dir", "examples")
            assert examples_dir == "context", \
                f"examples_dir should default to 'context', got '{examples_dir}'"

        finally:
            os.chdir(original_cwd)

    def test_examples_dir_points_to_existing_directory(self, pddrc_with_outputs):
        """
        Verify the examples_dir default points to a real directory.

        This ensures auto-deps will find files in the correct location.
        """
        from pdd.sync_main import _find_prompt_in_contexts
        from pdd.construct_paths import construct_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(pddrc_with_outputs)

            result = _find_prompt_in_contexts('credit_helpers')
            assert result is not None
            context_name, prompt_path, language = result

            resolved_config, _, _, _ = construct_paths(
                input_file_paths={"prompt_file": str(prompt_path)},
                force=True,
                quiet=True,
                command="sync",
                command_options={"basename": "credit_helpers", "language": "python"},
                context_override=context_name,
            )

            examples_dir = resolved_config.get("examples_dir", "examples")
            examples_path = Path(examples_dir)

            assert examples_path.exists(), \
                f"examples_dir '{examples_dir}' should exist"
            assert examples_path.is_dir(), \
                f"examples_dir '{examples_dir}' should be a directory"

        finally:
            os.chdir(original_cwd)

    def test_outputs_config_in_resolved_config(self, pddrc_with_outputs):
        """
        Verify that 'outputs' config is passed through to resolved_config.

        This is required for get_pdd_file_paths to use template-based paths.
        """
        from pdd.sync_main import _find_prompt_in_contexts
        from pdd.construct_paths import construct_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(pddrc_with_outputs)

            result = _find_prompt_in_contexts('credit_helpers')
            assert result is not None
            context_name, prompt_path, language = result

            resolved_config, _, _, _ = construct_paths(
                input_file_paths={"prompt_file": str(prompt_path)},
                force=True,
                quiet=True,
                command="sync",
                command_options={"basename": "credit_helpers", "language": "python"},
                context_override=context_name,
            )

            outputs = resolved_config.get("outputs")
            assert outputs is not None, \
                "resolved_config should have 'outputs' from context config"
            assert "example" in outputs, \
                "outputs should have 'example' key"
            assert outputs["example"].get("path") == "context/backend/{name}_example.py", \
                f"outputs.example.path should match .pddrc, got {outputs.get('example')}"

        finally:
            os.chdir(original_cwd)


class TestDetectLanguagesReturnsPathsDict:
    """Test that _detect_languages_with_context returns Dict[str, Path] not List[str]."""

    @pytest.fixture
    def frontend_context_pddrc(self, tmp_path):
        """Create .pddrc with frontend context using subdirectory prompts."""
        return _make_frontend_context_project(tmp_path, prompt_subdir="app/contributions/sales")

    def test_detect_languages_returns_paths(self, frontend_context_pddrc):
        """
        _detect_languages_with_context should return {language: path} dict,
        not just language names, so sync_main can use the correct file paths.
        """
        from pdd.sync_main import _detect_languages_with_context

        original_cwd = os.getcwd()
        try:
            os.chdir(frontend_context_pddrc)

            result = _detect_languages_with_context(
                basename='page',
                prompts_dir=Path('prompts'),
                context_name='frontend'
            )

            # Should return dict with paths, not just list of languages
            assert isinstance(result, dict), f"Should return dict, got {type(result)}"
            assert 'typescriptreact' in result
            assert result['typescriptreact'].exists(), \
                f"Path should exist: {result['typescriptreact']}"
            assert 'page_TypescriptReact.prompt' in str(result['typescriptreact'])
        finally:
            os.chdir(original_cwd)

    def test_detect_languages_fallback_returns_paths(self, tmp_path):
        """
        _detect_languages (non-context fallback) should also return {language: path} dict.
        """
        # Create .pddrc without outputs config
        pddrc_content = """
version: "1.0"
contexts:
  default:
    defaults:
      default_language: "python"
"""
        (tmp_path / ".pddrc").write_text(pddrc_content)

        # Create prompt in default location
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(parents=True)
        (prompts_dir / "my_module_python.prompt").write_text("# Test prompt")

        from pdd.sync_main import _detect_languages

        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)

            result = _detect_languages('my_module', prompts_dir)

            # Should return dict with paths
            assert isinstance(result, dict), f"Should return dict, got {type(result)}"
            assert 'python' in result
            assert result['python'].exists(), f"Path should exist: {result['python']}"
            assert 'my_module_python.prompt' in str(result['python'])
        finally:
            os.chdir(original_cwd)


class TestContextOverridePromptsDir:
    """Test that --context uses the context's prompts directory recursively."""

    @pytest.fixture
    def frontend_context_pddrc(self, tmp_path):
        """Create .pddrc with frontend context using subdirectory prompts."""
        return _make_frontend_context_project(tmp_path, prompt_subdir="app/sales")

    def test_context_override_searches_recursively(self, frontend_context_pddrc):
        """
        When --context frontend is provided, sync should search in
        prompts/frontend/**/ for prompt files, not just /prompts/.

        Issue #3: `pdd sync --basename page --context frontend` fails with:
        "No prompt files found for basename 'page' in directory '/prompts'"

        But the prompt exists at: prompts/frontend/app/sales/page_TypescriptReact.prompt
        """
        from pdd.sync_main import _detect_languages_with_context

        original_cwd = os.getcwd()
        try:
            os.chdir(frontend_context_pddrc)

            # With explicit context, should find prompt in prompts/frontend/**
            # even when basename alone ("page") doesn't match template
            languages = _detect_languages_with_context(
                basename='page',
                prompts_dir=Path('prompts'),  # Default dir
                context_name='frontend'  # Explicitly provided context
            )

            assert 'typescriptreact' in languages, \
                f"Should find prompt in context's prompts subdir recursively, got {languages}"
        finally:
            os.chdir(original_cwd)

    def test_context_override_multiple_nested_levels(self, tmp_path):
        """
        Should find prompts nested multiple levels deep within context prompts dir.
        """
        pddrc_content = """
version: "1.0"
contexts:
  frontend:
    paths:
      - "frontend/**"
      - "prompts/frontend/**"
    defaults:
      default_language: "typescriptreact"
      outputs:
        prompt:
          path: "prompts/frontend/{category}/{name}_{language}.prompt"
        code:
          path: "frontend/src/{category}/{name}.tsx"
  default:
    defaults:
      default_language: "python"
"""
        (tmp_path / ".pddrc").write_text(pddrc_content)

        # Create prompts at various nesting levels
        (tmp_path / "prompts" / "frontend" / "components" / "ui" / "buttons").mkdir(parents=True)
        (tmp_path / "prompts" / "frontend" / "components" / "ui" / "buttons" / "primary_TypescriptReact.prompt").write_text("# Primary button")

        from pdd.sync_main import _detect_languages_with_context

        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)

            languages = _detect_languages_with_context(
                basename='primary',
                prompts_dir=Path('prompts'),
                context_name='frontend'
            )

            assert 'typescriptreact' in languages, \
                f"Should find deeply nested prompt, got {languages}"
        finally:
            os.chdir(original_cwd)

    def test_context_override_finds_multiple_languages(self, tmp_path):
        """
        Should find all language variants when searching recursively.
        """
        pddrc_content = """
version: "1.0"
contexts:
  frontend:
    paths:
      - "frontend/**"
      - "prompts/frontend/**"
    defaults:
      default_language: "typescript"
      outputs:
        prompt:
          path: "prompts/frontend/{category}/{name}_{language}.prompt"
        code:
          path: "frontend/src/{category}/{name}.tsx"
  default:
    defaults:
      default_language: "python"
"""
        (tmp_path / ".pddrc").write_text(pddrc_content)

        # Create multiple language variants
        prompt_dir = tmp_path / "prompts" / "frontend" / "utils"
        prompt_dir.mkdir(parents=True)
        (prompt_dir / "formatter_typescript.prompt").write_text("# TS formatter")
        (prompt_dir / "formatter_javascript.prompt").write_text("# JS formatter")

        from pdd.sync_main import _detect_languages_with_context

        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)

            languages = _detect_languages_with_context(
                basename='formatter',
                prompts_dir=Path('prompts'),
                context_name='frontend'
            )

            assert 'typescript' in languages, f"Should find typescript, got {languages}"
            assert 'javascript' in languages, f"Should find javascript, got {languages}"
        finally:
            os.chdir(original_cwd)

    def test_sync_main_cli_context_enables_recursive_search(self, frontend_context_pddrc):
        """
        Bug: sync_main passes discovered_context (None when template fails)
        instead of context_override (CLI --context value) to _detect_languages_with_context.

        This causes "No prompt files found" even when --context frontend is provided.

        The test verifies sync_main correctly passes CLI context to language detection.
        """
        import click
        from unittest.mock import MagicMock

        original_cwd = os.getcwd()
        try:
            os.chdir(frontend_context_pddrc)

            # Create mock Click context with context="frontend" (simulating --context frontend)
            mock_ctx = MagicMock(spec=click.Context)
            mock_ctx.obj = {
                "context": "frontend",  # CLI --context frontend
                "verbose": False,
                "force": False,
                "quiet": True,
                "strength": 1.0,
                "temperature": 0.0,
                "time": 30,
            }

            from pdd.sync_main import sync_main

            # Should NOT raise "No prompt files found" because:
            # 1. context_override="frontend" is passed to _detect_languages_with_context
            # 2. _detect_languages_with_context extracts prompts_base_dir from template
            # 3. Recursive glob finds prompts/frontend/app/sales/page_TypescriptReact.prompt
            #
            # Bug behavior: Raises UsageError because discovered_context=None is passed
            # instead of context_override="frontend"

            results, total_cost, _ = sync_main(
                ctx=mock_ctx,
                basename='page',
                max_attempts=1,
                budget=1.0,
                skip_verify=True,
                skip_tests=True,
                target_coverage=80.0,
                dry_run=True,  # Don't actually sync, just verify discovery works
            )

            # If we get here without UsageError, the context was passed correctly
            # dry_run returns empty results but doesn't raise
            assert True, "sync_main should find prompt with --context frontend"

        except click.UsageError as e:
            pytest.fail(f"sync_main should not raise UsageError when --context is provided: {e}")
        finally:
            os.chdir(original_cwd)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
