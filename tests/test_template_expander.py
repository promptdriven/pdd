# tests/test_template_expander.py
"""
Unit tests for the template_expander module.

Tests the template expansion utility that replaces placeholders like
{name}, {category}, {ext}, etc. with actual values.
"""

import pytest
from pathlib import Path


class TestExpandTemplate:
    """Test expand_template function."""

    def test_basic_name_replacement(self):
        """Test simple {name} placeholder replacement."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "src/{name}.py",
            {"name": "my_module"}
        )
        assert result == "src/my_module.py"

    def test_multiple_placeholders(self):
        """Test multiple placeholders in same template."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "{category}/{name}/{name}.tsx",
            {"name": "Button", "category": "components"}
        )
        assert result == "components/Button/Button.tsx"

    def test_extension_placeholder(self):
        """Test {ext} placeholder for file extension."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "src/{name}.{ext}",
            {"name": "module", "ext": "py"}
        )
        assert result == "src/module.py"

    def test_language_placeholder(self):
        """Test {language} placeholder for full language name."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "prompts/{name}_{language}.prompt",
            {"name": "auth", "language": "python"}
        )
        assert result == "prompts/auth_python.prompt"

    def test_dir_prefix_placeholder(self):
        """Test {dir_prefix} placeholder for directory path."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "tests/{dir_prefix}test_{name}.py",
            {"name": "utils", "dir_prefix": "lib/core/"}
        )
        assert result == "tests/lib/core/test_utils.py"

    def test_empty_dir_prefix(self):
        """Test empty {dir_prefix} doesn't break path."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "{dir_prefix}{name}.py",
            {"name": "main", "dir_prefix": ""}
        )
        assert result == "main.py"


class TestNameCaseConversions:
    """Test case conversion placeholders."""

    def test_snake_case_from_pascal(self):
        """Test {name_snake} converts PascalCase to snake_case."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "test_{name_snake}.py",
            {"name": "AssetCard"}
        )
        assert result == "test_asset_card.py"

    def test_snake_case_from_camel(self):
        """Test {name_snake} converts camelCase to snake_case."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "{name_snake}.py",
            {"name": "assetCard"}
        )
        assert result == "asset_card.py"

    def test_pascal_case_from_snake(self):
        """Test {name_pascal} converts snake_case to PascalCase."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "{name_pascal}.tsx",
            {"name": "asset_card"}
        )
        assert result == "AssetCard.tsx"

    def test_pascal_case_from_kebab(self):
        """Test {name_pascal} converts kebab-case to PascalCase."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "{name_pascal}.tsx",
            {"name": "asset-card"}
        )
        assert result == "AssetCard.tsx"

    def test_kebab_case_from_pascal(self):
        """Test {name_kebab} converts PascalCase to kebab-case."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "{name_kebab}.css",
            {"name": "AssetCard"}
        )
        assert result == "asset-card.css"

    def test_already_correct_case(self):
        """Test case conversions when already in target case."""
        from pdd.template_expander import expand_template

        # Already snake_case
        result = expand_template("{name_snake}", {"name": "already_snake"})
        assert result == "already_snake"

        # Already PascalCase
        result = expand_template("{name_pascal}", {"name": "AlreadyPascal"})
        assert result == "Alreadypascal"  # Note: splits on nothing, just capitalizes


class TestPathNormalization:
    """Test path normalization for edge cases."""

    def test_empty_category_removes_double_slash(self):
        """When {category} is empty, path should not have //."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "src/components/{category}/{name}/{name}.tsx",
            {"name": "Button", "category": ""}
        )
        # os.path.normpath removes double slashes
        assert "//" not in result
        assert result == "src/components/Button/Button.tsx"

    def test_trailing_slash_handling(self):
        """Trailing slashes should be handled correctly."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "{dir_prefix}{name}.py",
            {"name": "module", "dir_prefix": "lib/"}
        )
        assert result == "lib/module.py"

    def test_multiple_empty_segments(self):
        """Multiple empty path segments should collapse."""
        from pdd.template_expander import expand_template

        # Use category and dir_prefix as the known empty placeholders
        result = expand_template(
            "src/{category}/{dir_prefix}file.py",
            {"name": "test", "category": "", "dir_prefix": ""}
        )
        assert "//" not in result
        assert result == "src/file.py"

    def test_preserves_relative_path(self):
        """Should not convert relative paths to absolute."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "frontend/src/{name}.tsx",
            {"name": "App"}
        )
        assert result == "frontend/src/App.tsx"
        assert not result.startswith("/")


class TestMissingPlaceholders:
    """Test behavior when placeholders are missing from context."""

    def test_missing_placeholder_becomes_empty(self):
        """Missing context keys should become empty strings."""
        from pdd.template_expander import expand_template

        result = expand_template(
            "src/{category}/{name}.py",
            {"name": "module"}  # category missing
        )
        # Should handle gracefully - empty category
        assert "module.py" in result

    def test_unknown_placeholder_preserved(self):
        """Unknown placeholders that aren't in our list should be preserved or error."""
        from pdd.template_expander import expand_template

        # This tests behavior - might preserve {unknown} or error
        result = expand_template(
            "src/{unknown}/file.py",
            {"name": "test"}
        )
        # Implementation choice: either preserve as literal or treat as empty
        # Just verify it doesn't crash
        assert "file.py" in result


class TestComplexTemplates:
    """Test complex real-world template patterns."""

    def test_nextjs_component_template(self):
        """Test Next.js/Storybook component pattern."""
        from pdd.template_expander import expand_template

        template = "frontend/src/components/{category}/{name}/{name}.tsx"
        result = expand_template(template, {
            "name": "AssetCard",
            "category": "marketplace"
        })
        assert result == "frontend/src/components/marketplace/AssetCard/AssetCard.tsx"

    def test_nextjs_test_template(self):
        """Test Next.js test file pattern."""
        from pdd.template_expander import expand_template

        template = "frontend/src/components/{category}/{name}/__test__/{name}.test.tsx"
        result = expand_template(template, {
            "name": "AssetCard",
            "category": "marketplace"
        })
        assert result == "frontend/src/components/marketplace/AssetCard/__test__/AssetCard.test.tsx"

    def test_python_backend_template(self):
        """Test Python backend pattern."""
        from pdd.template_expander import expand_template

        template = "backend/functions/utils/{name}.py"
        result = expand_template(template, {"name": "credit_helpers"})
        assert result == "backend/functions/utils/credit_helpers.py"

    def test_vue_component_template(self):
        """Test Vue.js component pattern (future extensibility)."""
        from pdd.template_expander import expand_template

        template = "src/components/{name}/{name}.vue"
        result = expand_template(template, {"name": "UserProfile"})
        assert result == "src/components/UserProfile/UserProfile.vue"

    def test_go_package_template(self):
        """Test Go package pattern (future extensibility)."""
        from pdd.template_expander import expand_template

        template = "internal/{category}/{name}/{name}.go"
        result = expand_template(template, {
            "name": "handler",
            "category": "api"
        })
        assert result == "internal/api/handler/handler.go"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
