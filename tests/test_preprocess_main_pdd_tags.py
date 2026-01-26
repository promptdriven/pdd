"""
Unit tests for pdd preprocess --pdd-tags functionality.

Tests the injection of PDD metadata tags from architecture.json into prompts.
"""

import json
import tempfile
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.architecture_sync import (
    generate_tags_from_architecture,
    get_architecture_entry_for_prompt,
    has_pdd_tags,
)


# --- Test tag injection logic (unit tests for helper functions) ---

class TestPddTagsInjection:
    """Tests for PDD tags injection logic used by preprocess --pdd-tags."""

    def test_inject_tags_to_prompt_without_tags(self):
        """Test injecting tags into a prompt that has no PDD tags."""
        with tempfile.TemporaryDirectory() as tmpdir:
            tmppath = Path(tmpdir)

            # Create architecture.json
            arch_file = tmppath / "architecture.json"
            arch_data = [{
                "filename": "my_module_python.prompt",
                "filepath": "pdd/my_module.py",
                "reason": "Handles data processing",
                "description": "Data processor",
                "dependencies": ["utils.prompt", "config.prompt"],
                "priority": 1,
                "tags": ["module"],
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "process", "signature": "(data: Dict)", "returns": "Dict"}
                        ]
                    }
                }
            }]
            arch_file.write_text(json.dumps(arch_data, indent=2))

            # Original prompt content (no PDD tags)
            original_content = """% Role & Scope
Your goal is to implement a data processor.

% Requirements
1. Process input data
2. Return transformed data

% Deliverables
- Single file: pdd/my_module.py
"""

            # Verify no PDD tags
            assert not has_pdd_tags(original_content)

            # Get architecture entry
            entry = get_architecture_entry_for_prompt(
                "my_module_python.prompt",
                architecture_path=arch_file
            )
            assert entry is not None

            # Generate tags
            tags = generate_tags_from_architecture(entry)

            # Inject tags
            final_content = tags + '\n\n' + original_content

            # Verify tags were injected
            assert has_pdd_tags(final_content)
            assert '<pdd-reason>Handles data processing</pdd-reason>' in final_content
            assert '<pdd-interface>' in final_content
            assert '"type": "module"' in final_content
            assert '<pdd-dependency>utils.prompt</pdd-dependency>' in final_content
            assert '<pdd-dependency>config.prompt</pdd-dependency>' in final_content

            # Verify original content preserved
            assert '% Role & Scope' in final_content
            assert '% Requirements' in final_content

    def test_skip_injection_when_tags_exist(self):
        """Test that injection is skipped when prompt already has PDD tags."""
        content_with_tags = """<pdd-reason>Manual reason</pdd-reason>

% Role & Scope
Your goal is to implement...
"""

        # Should detect existing tags
        assert has_pdd_tags(content_with_tags)

        # Simulating the logic: don't inject if tags exist
        arch_entry = {
            "reason": "Architecture reason (should NOT override)",
            "dependencies": ["dep.prompt"]
        }

        # If tags exist, don't inject
        if has_pdd_tags(content_with_tags):
            final_content = content_with_tags
        else:
            tags = generate_tags_from_architecture(arch_entry)
            final_content = tags + '\n\n' + content_with_tags

        # Verify manual tags preserved, architecture tags NOT added
        assert '<pdd-reason>Manual reason</pdd-reason>' in final_content
        assert 'Architecture reason' not in final_content

    def test_no_injection_when_no_architecture_entry(self):
        """Test that no tags are injected when no architecture entry exists."""
        with tempfile.TemporaryDirectory() as tmpdir:
            tmppath = Path(tmpdir)

            # Empty architecture
            arch_file = tmppath / "architecture.json"
            arch_file.write_text("[]")

            original_content = "% Prompt without architecture entry"

            # Try to get entry
            entry = get_architecture_entry_for_prompt(
                "orphan.prompt",
                architecture_path=arch_file
            )

            assert entry is None

            # No injection when no entry
            if entry and not has_pdd_tags(original_content):
                tags = generate_tags_from_architecture(entry)
                final_content = tags + '\n\n' + original_content
            else:
                final_content = original_content

            # Content should be unchanged
            assert final_content == original_content
            assert not has_pdd_tags(final_content)

    def test_partial_architecture_entry(self):
        """Test injection with partial architecture data (only some fields)."""
        with tempfile.TemporaryDirectory() as tmpdir:
            tmppath = Path(tmpdir)

            # Architecture with only reason (no interface or dependencies)
            arch_file = tmppath / "architecture.json"
            arch_data = [{
                "filename": "simple.prompt",
                "filepath": "pdd/simple.py",
                "reason": "Simple module",
                "description": "Test",
                "dependencies": [],
                "priority": 1,
                "tags": []
                # No interface field
            }]
            arch_file.write_text(json.dumps(arch_data, indent=2))

            entry = get_architecture_entry_for_prompt(
                "simple.prompt",
                architecture_path=arch_file
            )

            tags = generate_tags_from_architecture(entry)

            # Should only have reason tag
            assert '<pdd-reason>Simple module</pdd-reason>' in tags
            assert '<pdd-interface>' not in tags
            assert '<pdd-dependency>' not in tags

    def test_injection_preserves_prompt_formatting(self):
        """Test that injection preserves the original prompt formatting."""
        original_content = """% Role & Scope
Your goal is to implement a feature.

% Requirements
1. First requirement
2. Second requirement
   - Sub-item a
   - Sub-item b

% Code Examples
```python
def example():
    pass
```

% Deliverables
- Single file: output.py
"""

        arch_entry = {
            "reason": "Test module",
            "interface": {"type": "module", "module": {"functions": []}},
            "dependencies": []
        }

        tags = generate_tags_from_architecture(arch_entry)
        final_content = tags + '\n\n' + original_content

        # Verify original formatting preserved
        assert '% Role & Scope' in final_content
        assert '   - Sub-item a' in final_content  # Indentation preserved
        assert '```python' in final_content  # Code blocks preserved
        assert 'def example():' in final_content

    def test_complex_interface_injection(self):
        """Test injection with complex interface structure."""
        arch_entry = {
            "reason": "Complex module",
            "interface": {
                "type": "module",
                "module": {
                    "functions": [
                        {
                            "name": "process_data",
                            "signature": "(data: List[Dict[str, Any]], config: Optional[Config] = None) -> Tuple[bool, List[Result]]",
                            "returns": "Tuple[bool, List[Result]]",
                            "sideEffects": [
                                "Logs processing steps",
                                "Updates metrics",
                                "Sends notifications on failure"
                            ]
                        },
                        {
                            "name": "validate_input",
                            "signature": "(data: Any) -> ValidationResult",
                            "returns": "ValidationResult"
                        }
                    ]
                }
            },
            "dependencies": ["logger.prompt", "metrics.prompt", "notifier.prompt"]
        }

        tags = generate_tags_from_architecture(arch_entry)

        # Verify complex interface is properly serialized
        assert '<pdd-interface>' in tags
        assert 'process_data' in tags
        assert 'validate_input' in tags
        assert 'sideEffects' in tags
        assert 'Logs processing steps' in tags

        # Verify all dependencies
        assert '<pdd-dependency>logger.prompt</pdd-dependency>' in tags
        assert '<pdd-dependency>metrics.prompt</pdd-dependency>' in tags
        assert '<pdd-dependency>notifier.prompt</pdd-dependency>' in tags

    def test_empty_dependencies_not_injected(self):
        """Test that empty dependencies don't create empty tags."""
        arch_entry = {
            "reason": "Module with no deps",
            "interface": {"type": "module", "module": {"functions": []}},
            "dependencies": []  # Empty
        }

        tags = generate_tags_from_architecture(arch_entry)

        assert '<pdd-reason>' in tags
        assert '<pdd-interface>' in tags
        assert '<pdd-dependency>' not in tags  # No dependency tags for empty list


# --- Test detection of existing PDD tags ---

class TestHasPddTags:
    """Tests for has_pdd_tags function."""

    def test_detects_reason_tag(self):
        """Test detection of <pdd-reason> tag."""
        content = "Some text <pdd-reason>reason</pdd-reason> more text"
        assert has_pdd_tags(content) is True

    def test_detects_interface_tag(self):
        """Test detection of <pdd-interface> tag."""
        content = "<pdd-interface>{}</pdd-interface>"
        assert has_pdd_tags(content) is True

    def test_detects_dependency_tag(self):
        """Test detection of <pdd-dependency> tag."""
        content = "<pdd-dependency>dep.prompt</pdd-dependency>"
        assert has_pdd_tags(content) is True

    def test_no_tags(self):
        """Test when no PDD tags present."""
        content = "Regular prompt content without any special tags"
        assert has_pdd_tags(content) is False

    def test_similar_but_not_pdd_tags(self):
        """Test that similar but different tags are not detected."""
        content = """
        <reason>Not a PDD tag</reason>
        <interface>Also not PDD</interface>
        <dependency>Still not PDD</dependency>
        """
        assert has_pdd_tags(content) is False

    def test_pdd_tag_in_comment(self):
        """Test detection of PDD tag even in comments."""
        content = "% Comment with <pdd-reason>tag</pdd-reason> in it"
        # Should still detect it (we check string presence)
        assert has_pdd_tags(content) is True


# --- Test generate_tags_from_architecture ---

class TestGenerateTagsFromArchitecture:
    """Tests for generate_tags_from_architecture function."""

    def test_empty_entry(self):
        """Test with empty architecture entry."""
        tags = generate_tags_from_architecture({})
        assert tags == ""

    def test_reason_only(self):
        """Test with only reason field."""
        entry = {"reason": "Test reason"}
        tags = generate_tags_from_architecture(entry)
        assert '<pdd-reason>Test reason</pdd-reason>' in tags
        assert '<pdd-interface>' not in tags
        assert '<pdd-dependency>' not in tags

    def test_interface_only(self):
        """Test with only interface field."""
        entry = {"interface": {"type": "cli", "cli": {"commands": []}}}
        tags = generate_tags_from_architecture(entry)
        assert '<pdd-interface>' in tags
        assert '"type": "cli"' in tags

    def test_dependencies_only(self):
        """Test with only dependencies field."""
        entry = {"dependencies": ["a.prompt", "b.prompt"]}
        tags = generate_tags_from_architecture(entry)
        assert '<pdd-dependency>a.prompt</pdd-dependency>' in tags
        assert '<pdd-dependency>b.prompt</pdd-dependency>' in tags

    def test_all_fields(self):
        """Test with all fields."""
        entry = {
            "reason": "Full entry",
            "interface": {"type": "module", "module": {"functions": []}},
            "dependencies": ["dep.prompt"]
        }
        tags = generate_tags_from_architecture(entry)
        assert '<pdd-reason>Full entry</pdd-reason>' in tags
        assert '<pdd-interface>' in tags
        assert '<pdd-dependency>dep.prompt</pdd-dependency>' in tags

    def test_json_formatting(self):
        """Test that interface JSON is properly formatted (pretty-printed)."""
        entry = {
            "interface": {
                "type": "module",
                "module": {
                    "functions": [{"name": "test"}]
                }
            }
        }
        tags = generate_tags_from_architecture(entry)

        # Should be pretty-printed (multi-line)
        assert '\n' in tags
        # Should have proper indentation
        assert '  ' in tags or '    ' in tags


# --- Test get_architecture_entry_for_prompt ---

class TestGetArchitectureEntryForPrompt:
    """Tests for get_architecture_entry_for_prompt function."""

    def test_finds_existing_entry(self):
        """Test finding an existing entry."""
        with tempfile.TemporaryDirectory() as tmpdir:
            tmppath = Path(tmpdir)
            arch_file = tmppath / "architecture.json"
            arch_data = [
                {"filename": "target.prompt", "reason": "Found"},
                {"filename": "other.prompt", "reason": "Other"}
            ]
            arch_file.write_text(json.dumps(arch_data))

            entry = get_architecture_entry_for_prompt(
                "target.prompt",
                architecture_path=arch_file
            )

            assert entry is not None
            assert entry['filename'] == 'target.prompt'
            assert entry['reason'] == 'Found'

    def test_returns_none_for_missing(self):
        """Test returning None for missing entry."""
        with tempfile.TemporaryDirectory() as tmpdir:
            tmppath = Path(tmpdir)
            arch_file = tmppath / "architecture.json"
            arch_file.write_text('[{"filename": "other.prompt"}]')

            entry = get_architecture_entry_for_prompt(
                "missing.prompt",
                architecture_path=arch_file
            )

            assert entry is None

    def test_returns_none_for_empty_architecture(self):
        """Test returning None when architecture is empty."""
        with tempfile.TemporaryDirectory() as tmpdir:
            tmppath = Path(tmpdir)
            arch_file = tmppath / "architecture.json"
            arch_file.write_text("[]")

            entry = get_architecture_entry_for_prompt(
                "any.prompt",
                architecture_path=arch_file
            )

            assert entry is None

    def test_returns_none_for_missing_file(self):
        """Test returning None when architecture file doesn't exist."""
        with tempfile.TemporaryDirectory() as tmpdir:
            tmppath = Path(tmpdir)
            nonexistent = tmppath / "nonexistent.json"

            entry = get_architecture_entry_for_prompt(
                "any.prompt",
                architecture_path=nonexistent
            )

            assert entry is None

    def test_case_sensitive_matching(self):
        """Test that filename matching is case-sensitive."""
        with tempfile.TemporaryDirectory() as tmpdir:
            tmppath = Path(tmpdir)
            arch_file = tmppath / "architecture.json"
            arch_data = [{"filename": "MyModule.prompt", "reason": "Test"}]
            arch_file.write_text(json.dumps(arch_data))

            # Exact match should work
            entry = get_architecture_entry_for_prompt(
                "MyModule.prompt",
                architecture_path=arch_file
            )
            assert entry is not None

            # Different case should not match
            entry = get_architecture_entry_for_prompt(
                "mymodule.prompt",
                architecture_path=arch_file
            )
            assert entry is None
