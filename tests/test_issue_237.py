# tests/test_issue_237.py
"""
Issue #237: pdd sync generates files in incorrect locations

Root cause:
1. `.pddrc` patterns match OUTPUT paths instead of INPUT paths
2. `dir_prefix` always applied, causing double-pathing
3. No extensible way to define different project layouts

These tests define expected behavior and should FAIL until the fix is implemented.
"""

import pytest
import os
import sys
from pathlib import Path
from unittest.mock import patch, MagicMock


class TestGetRelativeBasename:
    """Test _get_relative_basename computes path relative to pattern base."""

    def test_strips_pattern_base_frontend(self):
        """frontend/components/marketplace/AssetCard with pattern frontend/components/** -> marketplace/AssetCard"""
        from pdd.construct_paths import _get_relative_basename

        result = _get_relative_basename(
            'frontend/components/marketplace/AssetCard',
            'frontend/components/**'
        )
        assert result == 'marketplace/AssetCard'

    def test_strips_pattern_base_backend(self):
        """backend/utils/credit_helpers with pattern backend/utils/** -> credit_helpers"""
        from pdd.construct_paths import _get_relative_basename

        result = _get_relative_basename(
            'backend/utils/credit_helpers',
            'backend/utils/**'
        )
        assert result == 'credit_helpers'

    def test_no_match_returns_original(self):
        """When pattern doesn't match, return original path."""
        from pdd.construct_paths import _get_relative_basename

        result = _get_relative_basename(
            'unknown/path/module',
            'other/**'
        )
        assert result == 'unknown/path/module'

    def test_handles_single_star_pattern(self):
        """Pattern with single * should also work."""
        from pdd.construct_paths import _get_relative_basename

        result = _get_relative_basename(
            'src/components/Button',
            'src/components/*'
        )
        assert result == 'Button'


class TestOutputPathGeneration:
    """Test that output paths are generated correctly with new template system."""

    @pytest.fixture
    def pddrc_with_outputs(self, tmp_path):
        """Create a .pddrc with outputs configuration."""
        pddrc_content = """
version: "1.0"
contexts:
  backend-utils:
    paths:
      - "backend/utils/**"
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
          path: "context/{name}_example.py"

  frontend-components:
    paths:
      - "frontend/components/**"
    defaults:
      default_language: "typescript"
      outputs:
        prompt:
          path: "prompts/frontend/components/{category}/{name}_{language}.prompt"
        code:
          path: "frontend/src/components/{category}/{name}/{name}.tsx"
        test:
          path: "frontend/src/components/{category}/{name}/__test__/{name}.test.tsx"
        storybook:
          path: "frontend/src/components/{category}/{name}/{name}.stories.tsx"
        example:
          path: "context/frontend/{name}_example.tsx"

  default:
    defaults:
      outputs:
        prompt:
          path: "prompts/{dir_prefix}{name}_{language}.prompt"
        code:
          path: "{dir_prefix}{name}.{ext}"
        test:
          path: "tests/{dir_prefix}test_{name}.{ext}"
        example:
          path: "context/{dir_prefix}{name}_example.{ext}"
"""
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(pddrc_content)
        return tmp_path

    def test_backend_utils_no_double_path(self, pddrc_with_outputs):
        """
        BUG: pdd sync backend/utils/credit_helpers currently generates:
             backend/utils/credit_helpers.py (wrong)

        EXPECTED: backend/functions/utils/credit_helpers.py
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(pddrc_with_outputs)

            # When using context 'backend-utils' with input 'credit_helpers'
            paths = get_pdd_file_paths(
                basename='credit_helpers',  # Relative to context pattern base
                language='python',
                prompts_dir='prompts/backend/utils',
                context_override='backend-utils'  # Force the correct context
            )

            assert str(paths['code']) == 'backend/functions/utils/credit_helpers.py'
            assert str(paths['test']) == 'backend/tests/test_credit_helpers.py'
            assert str(paths['example']) == 'context/credit_helpers_example.py'
        finally:
            os.chdir(original_cwd)

    def test_frontend_component_with_category(self, pddrc_with_outputs):
        """
        BUG: pdd sync frontend/components/marketplace/AssetCard currently generates:
             frontend/src/components/marketplace/AssetCard.tsx (wrong structure)

        EXPECTED: frontend/src/components/marketplace/AssetCard/AssetCard.tsx
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(pddrc_with_outputs)

            # When using context 'frontend-components' with input 'marketplace/AssetCard'
            paths = get_pdd_file_paths(
                basename='marketplace/AssetCard',  # Relative to context pattern base
                language='typescript',
                prompts_dir='prompts/frontend/components',
                context_override='frontend-components'  # Force the correct context
            )

            # Expected Next.js/Storybook component structure
            assert str(paths['code']) == 'frontend/src/components/marketplace/AssetCard/AssetCard.tsx'
            assert str(paths['test']) == 'frontend/src/components/marketplace/AssetCard/__test__/AssetCard.test.tsx'
            assert 'storybook' in paths
            assert str(paths['storybook']) == 'frontend/src/components/marketplace/AssetCard/AssetCard.stories.tsx'
        finally:
            os.chdir(original_cwd)

    def test_empty_category_no_double_slash(self, pddrc_with_outputs):
        """
        Edge case: When category is empty (e.g., frontend/components/Button),
        template {category}/{name} should NOT produce //Button.

        EXPECTED: frontend/src/components/Button/Button.tsx (normalized path)
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(pddrc_with_outputs)

            paths = get_pdd_file_paths(
                basename='Button',  # No category - just component name
                language='typescript',
                prompts_dir='prompts/frontend/components',
                context_override='frontend-components'  # Force the correct context
            )

            code_path = str(paths['code'])
            assert '//' not in code_path, f"Double slash found in path: {code_path}"
            assert code_path == 'frontend/src/components/Button/Button.tsx'
        finally:
            os.chdir(original_cwd)

    def test_default_context_uses_dir_prefix(self, pddrc_with_outputs):
        """
        For paths that don't match any specific context, the default
        context should use {dir_prefix} to preserve input structure.
        """
        from pdd.sync_determine_operation import get_pdd_file_paths

        original_cwd = os.getcwd()
        try:
            os.chdir(pddrc_with_outputs)

            paths = get_pdd_file_paths(
                basename='misc/helpers/utils',
                language='python',
                prompts_dir='prompts'
            )

            assert str(paths['code']) == 'misc/helpers/utils.py'
            assert str(paths['test']) == 'tests/misc/helpers/test_utils.py'
        finally:
            os.chdir(original_cwd)


class TestMatchedContextTracking:
    """Test that matched context is tracked for debugging."""

    def test_resolved_config_includes_matched_context(self, tmp_path):
        """resolved_config should include _matched_context for debugging."""
        pddrc_content = """
version: "1.0"
contexts:
  backend:
    paths:
      - "backend/**"
    defaults:
      default_language: "python"
  default:
    defaults:
      default_language: "python"
"""
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(pddrc_content)

        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)

            from pdd.construct_paths import construct_paths

            resolved_config, _, _, _ = construct_paths(
                input_file_paths={},
                force=True,
                quiet=True,
                command="sync",
                command_options={"basename": "my_module", "language": "python"}
            )

            assert '_matched_context' in resolved_config
        finally:
            os.chdir(original_cwd)


class TestPromptPathInOutputs:
    """Test that prompt paths can be configured via outputs section."""

    def test_prompt_path_from_outputs(self, tmp_path):
        """Prompt path should be taken from outputs.prompt.path if configured."""
        pddrc_content = """
version: "1.0"
contexts:
  api:
    paths:
      - "api/**"
    defaults:
      default_language: "python"
      outputs:
        prompt:
          path: "custom/prompts/{name}_{language}.prompt"
        code:
          path: "src/api/{name}.py"
"""
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(pddrc_content)

        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)

            from pdd.sync_determine_operation import get_pdd_file_paths

            paths = get_pdd_file_paths(
                basename='users',
                language='python',
                prompts_dir='prompts',  # Should be overridden by outputs config
                context_override='api'  # Force the correct context
            )

            assert str(paths['prompt']) == 'custom/prompts/users_python.prompt'
        finally:
            os.chdir(original_cwd)


class TestConstructPathsContextDetection:
    """Test that construct_paths uses prompt file path for context detection, not CWD."""

    def test_construct_paths_uses_prompt_file_for_context_detection(self, tmp_path):
        """Issue #237: Context should be detected from prompt file path, not CWD.

        When construct_paths receives a prompt file path, it should use that path
        to detect the context, not the current working directory. This ensures
        that the correct outputs config (with templates) is used for path generation.
        """
        pddrc_content = """
version: "1.0"
contexts:
  backend-utils:
    paths:
      - "prompts/backend/utils/**"
    defaults:
      default_language: "python"
      outputs:
        example:
          path: "context/backend/{name}_example.py"
  default:
    defaults:
      example_output_path: "context/"
"""
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(pddrc_content)

        # Create prompt file at path matching backend-utils context
        prompt_dir = tmp_path / "prompts" / "backend" / "utils"
        prompt_dir.mkdir(parents=True)
        prompt_file = prompt_dir / "credit_helpers_python.prompt"
        prompt_file.write_text("test prompt")

        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)  # CWD is project root - doesn't match any pattern

            from pdd.construct_paths import construct_paths

            resolved_config, _, _, _ = construct_paths(
                input_file_paths={"prompt_file": str(prompt_file)},
                force=True,
                quiet=True,
                command="sync",
                command_options={"basename": "credit_helpers", "language": "python"}
            )

            # BUG: Currently returns 'default' because it uses CWD for context detection
            # EXPECTED: Should return 'backend-utils' because prompt file matches the pattern
            assert resolved_config.get('_matched_context') == 'backend-utils', \
                f"Expected context 'backend-utils' but got '{resolved_config.get('_matched_context')}'"
            assert 'outputs' in resolved_config, \
                "Expected 'outputs' in resolved_config for template-based path generation"
        finally:
            os.chdir(original_cwd)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
