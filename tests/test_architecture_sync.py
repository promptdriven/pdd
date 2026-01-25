"""
Unit tests for architecture_sync module.

Tests bidirectional sync between architecture.json and prompt file metadata tags.
"""

import json
import tempfile
from pathlib import Path

import pytest

from pdd.architecture_sync import (
    generate_tags_from_architecture,
    get_architecture_entry_for_prompt,
    has_pdd_tags,
    parse_prompt_tags,
    sync_all_prompts_to_architecture,
    update_architecture_from_prompt,
    validate_dependencies,
    validate_interface_structure,
)


# --- Test parse_prompt_tags ---

def test_parse_tags_with_all_fields():
    """Test parsing prompt with reason, interface, and dependencies."""
    content = """
    <pdd-reason>Provides unified LLM invocation</pdd-reason>

    <pdd-interface>
    {
      "type": "module",
      "module": {
        "functions": [
          {"name": "llm_invoke", "signature": "(...)", "returns": "Dict"}
        ]
      }
    }
    </pdd-interface>

    <pdd-dependency>path_resolution_python.prompt</pdd-dependency>
    <pdd-dependency>construct_paths_python.prompt</pdd-dependency>

    % Rest of prompt content...
    """

    result = parse_prompt_tags(content)

    assert result['reason'] == 'Provides unified LLM invocation'
    assert result['interface'] is not None
    assert result['interface']['type'] == 'module'
    assert len(result['interface']['module']['functions']) == 1
    assert result['dependencies'] == [
        'path_resolution_python.prompt',
        'construct_paths_python.prompt'
    ]


def test_parse_tags_lenient_missing_fields():
    """Test lenient parsing with missing tags (only reason present)."""
    content = """
    <pdd-reason>Only reason tag present</pdd-reason>

    % Rest of prompt without interface or dependencies
    """

    result = parse_prompt_tags(content)

    assert result['reason'] == 'Only reason tag present'
    assert result['interface'] is None
    assert result['dependencies'] == []


def test_parse_tags_only_dependencies():
    """Test parsing with only dependency tags."""
    content = """
    <pdd-dependency>dep1.prompt</pdd-dependency>
    <pdd-dependency>dep2.prompt</pdd-dependency>
    """

    result = parse_prompt_tags(content)

    assert result['reason'] is None
    assert result['interface'] is None
    assert result['dependencies'] == ['dep1.prompt', 'dep2.prompt']


def test_parse_tags_malformed_xml():
    """Test lenient parsing with malformed XML (unclosed tag)."""
    content = "<pdd-reason>Unclosed tag without ending"

    result = parse_prompt_tags(content)

    # Lenient parser (recover=True) actually extracts content from malformed XML
    # This is better than returning None - it extracts what it can
    assert result['reason'] == 'Unclosed tag without ending'
    assert result['interface'] is None
    assert result['dependencies'] == []


def test_parse_tags_invalid_json_in_interface():
    """Test lenient parsing with invalid JSON in interface tag."""
    content = """
    <pdd-reason>Valid reason</pdd-reason>
    <pdd-interface>
    {invalid json here, missing quotes}
    </pdd-interface>
    """

    result = parse_prompt_tags(content)

    # Reason should parse, interface should be None (lenient)
    assert result['reason'] == 'Valid reason'
    assert result['interface'] is None
    assert result['dependencies'] == []


def test_parse_tags_double_brace_escaped_json():
    """Test parsing interface with double-brace escaping (used in LLM prompts for Python .format())."""
    content = """
    <pdd-reason>Fixes validation errors in architecture.json</pdd-reason>
    <pdd-interface>
    {{
      "type": "module",
      "module": {{
        "functions": [
          {{"name": "fix_architecture", "signature": "(current_architecture: str, step7_output: str)", "returns": "str"}}
        ]
      }}
    }}
    </pdd-interface>
    <pdd-dependency>agentic_arch_step7_validate_LLM.prompt</pdd-dependency>
    """

    result = parse_prompt_tags(content)

    # Should successfully parse double-brace escaped JSON
    assert result['reason'] == 'Fixes validation errors in architecture.json'
    assert result['interface'] is not None
    assert result['interface']['type'] == 'module'
    assert result['interface']['module']['functions'][0]['name'] == 'fix_architecture'
    assert result['dependencies'] == ['agentic_arch_step7_validate_LLM.prompt']
    assert result.get('interface_parse_error') is None


def test_parse_tags_empty_content():
    """Test parsing empty content."""
    result = parse_prompt_tags("")

    assert result['reason'] is None
    assert result['interface'] is None
    assert result['dependencies'] == []


def test_parse_tags_no_pdd_tags():
    """Test parsing content without any PDD tags."""
    content = """
    % This is a regular prompt file
    % with no PDD metadata tags

    Your goal is to implement...
    """

    result = parse_prompt_tags(content)

    assert result['reason'] is None
    assert result['interface'] is None
    assert result['dependencies'] == []


# --- Test update_architecture_from_prompt ---

def test_update_architecture_from_prompt_success():
    """Test successful update of architecture entry from prompt."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        # Create test prompt file with tags
        prompt_file = prompts_dir / "test_module_python.prompt"
        prompt_file.write_text("""
<pdd-reason>Updated reason from prompt</pdd-reason>
<pdd-interface>{"type": "module", "module": {"functions": []}}</pdd-interface>
<pdd-dependency>dependency1.prompt</pdd-dependency>
""")

        # Create test architecture.json
        arch_file = tmppath / "architecture.json"
        arch_data = [
            {
                "filename": "test_module_python.prompt",
                "filepath": "pdd/test_module.py",
                "reason": "Old reason",
                "description": "Test module",
                "dependencies": [],
                "priority": 1,
                "tags": ["module"],
                "interface": None
            }
        ]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        # Update from prompt
        result = update_architecture_from_prompt(
            "test_module_python.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_file,
            dry_run=False
        )

        # Check result
        assert result['success'] is True
        assert result['updated'] is True
        assert 'reason' in result['changes']
        assert result['changes']['reason']['old'] == 'Old reason'
        assert result['changes']['reason']['new'] == 'Updated reason from prompt'

        # Verify architecture.json was updated
        updated_arch = json.loads(arch_file.read_text())
        assert updated_arch[0]['reason'] == 'Updated reason from prompt'
        assert updated_arch[0]['interface'] == {"type": "module", "module": {"functions": []}}
        assert updated_arch[0]['dependencies'] == ['dependency1.prompt']


def test_update_architecture_from_prompt_dry_run():
    """Test dry run mode doesn't write to architecture.json."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        prompt_file = prompts_dir / "test_module_python.prompt"
        prompt_file.write_text("<pdd-reason>New reason</pdd-reason>")

        arch_file = tmppath / "architecture.json"
        arch_data = [
            {
                "filename": "test_module_python.prompt",
                "filepath": "pdd/test.py",
                "reason": "Old reason",
                "description": "Test",
                "dependencies": [],
                "priority": 1,
                "tags": []
            }
        ]
        original_content = json.dumps(arch_data, indent=2)
        arch_file.write_text(original_content)

        # Dry run
        result = update_architecture_from_prompt(
            "test_module_python.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_file,
            dry_run=True
        )

        assert result['success'] is True
        assert result['updated'] is True

        # Verify architecture.json NOT modified
        assert arch_file.read_text() == original_content


def test_update_architecture_from_prompt_missing_file():
    """Test error when prompt file doesn't exist."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()
        arch_file = tmppath / "architecture.json"
        arch_file.write_text("[]")

        result = update_architecture_from_prompt(
            "nonexistent.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_file
        )

        assert result['success'] is False
        assert 'not found' in result['error'].lower()


def test_update_architecture_from_prompt_no_entry():
    """Test error when no architecture entry exists for prompt."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        prompt_file = prompts_dir / "orphan.prompt"
        prompt_file.write_text("<pdd-reason>Test</pdd-reason>")

        arch_file = tmppath / "architecture.json"
        arch_file.write_text("[]")  # Empty architecture

        result = update_architecture_from_prompt(
            "orphan.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_file
        )

        assert result['success'] is False
        assert 'no architecture entry' in result['error'].lower()


def test_sync_preserves_other_fields():
    """Test that sync only updates specified fields (reason, interface, dependencies)."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        prompt_file = prompts_dir / "test.prompt"
        prompt_file.write_text("<pdd-reason>Updated reason</pdd-reason>")

        arch_file = tmppath / "architecture.json"
        arch_data = [
            {
                "filename": "test.prompt",
                "filepath": "pdd/test.py",
                "reason": "Old reason",
                "description": "Original description",
                "dependencies": [],
                "priority": 42,
                "tags": ["module", "python"],
                "interface": None
            }
        ]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        # Update
        update_architecture_from_prompt(
            "test.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_file
        )

        # Verify other fields preserved
        updated = json.loads(arch_file.read_text())
        assert updated[0]['filename'] == "test.prompt"
        assert updated[0]['filepath'] == "pdd/test.py"
        assert updated[0]['description'] == "Original description"
        assert updated[0]['priority'] == 42
        assert updated[0]['tags'] == ["module", "python"]


# --- Test sync_all_prompts_to_architecture ---

def test_sync_all_prompts_to_architecture():
    """Test syncing all prompts to architecture."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        # Create multiple prompts
        (prompts_dir / "module1.prompt").write_text("<pdd-reason>Module 1</pdd-reason>")
        (prompts_dir / "module2.prompt").write_text("<pdd-reason>Module 2</pdd-reason>")
        (prompts_dir / "module3.prompt").write_text("% No tags")

        # Create architecture
        arch_file = tmppath / "architecture.json"
        arch_data = [
            {"filename": "module1.prompt", "filepath": "m1.py", "reason": "Old 1",
             "description": "D1", "dependencies": [], "priority": 1, "tags": []},
            {"filename": "module2.prompt", "filepath": "m2.py", "reason": "Old 2",
             "description": "D2", "dependencies": [], "priority": 2, "tags": []},
            {"filename": "module3.prompt", "filepath": "m3.py", "reason": "Old 3",
             "description": "D3", "dependencies": [], "priority": 3, "tags": []},
        ]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        # Sync all
        result = sync_all_prompts_to_architecture(
            prompts_dir=prompts_dir,
            architecture_path=arch_file
        )

        assert result['success'] is True
        assert result['updated_count'] == 2  # module1 and module2 have tags
        assert len(result['results']) == 3


# --- Test validate_dependencies ---

def test_validate_dependencies_valid():
    """Test validation of valid dependencies."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        # Create dependency files
        (prompts_dir / "dep1.prompt").write_text("test")
        (prompts_dir / "dep2.prompt").write_text("test")

        result = validate_dependencies(
            ["dep1.prompt", "dep2.prompt"],
            prompts_dir=prompts_dir
        )

        assert result['valid'] is True
        assert result['missing'] == []
        assert result['duplicates'] == []


def test_validate_dependencies_missing():
    """Test validation detects missing dependencies."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        (prompts_dir / "exists.prompt").write_text("test")

        result = validate_dependencies(
            ["exists.prompt", "missing.prompt"],
            prompts_dir=prompts_dir
        )

        assert result['valid'] is False
        assert "missing.prompt" in result['missing']
        assert "exists.prompt" not in result['missing']


def test_validate_dependencies_duplicates():
    """Test validation detects duplicate dependencies."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        (prompts_dir / "dep.prompt").write_text("test")

        result = validate_dependencies(
            ["dep.prompt", "dep.prompt", "dep.prompt"],
            prompts_dir=prompts_dir
        )

        assert result['valid'] is False
        assert "dep.prompt" in result['duplicates']


# --- Test validate_interface_structure ---

def test_validate_interface_structure_module_valid():
    """Test validation of valid module interface."""
    interface = {
        "type": "module",
        "module": {
            "functions": [
                {"name": "func1", "signature": "(...)", "returns": "str"}
            ]
        }
    }

    result = validate_interface_structure(interface)

    assert result['valid'] is True
    assert result['errors'] == []


def test_validate_interface_structure_cli_valid():
    """Test validation of valid CLI interface."""
    interface = {
        "type": "cli",
        "cli": {
            "commands": [
                {"name": "cmd1", "description": "Test command"}
            ]
        }
    }

    result = validate_interface_structure(interface)

    assert result['valid'] is True


def test_validate_interface_structure_invalid_type():
    """Test validation detects invalid type."""
    interface = {
        "type": "invalid_type",
        "module": {"functions": []}
    }

    result = validate_interface_structure(interface)

    assert result['valid'] is False
    assert len(result['errors']) > 0
    assert 'invalid type' in result['errors'][0].lower()


def test_validate_interface_structure_missing_nested_key():
    """Test validation detects missing nested key."""
    interface = {
        "type": "module"
        # Missing 'module' key
    }

    result = validate_interface_structure(interface)

    assert result['valid'] is False
    assert any('missing' in err.lower() for err in result['errors'])


def test_validate_interface_structure_missing_functions():
    """Test validation detects missing functions in module."""
    interface = {
        "type": "module",
        "module": {}  # Missing 'functions' key
    }

    result = validate_interface_structure(interface)

    assert result['valid'] is False
    assert any('functions' in err.lower() for err in result['errors'])


# --- Test helper functions ---

def test_has_pdd_tags_with_tags():
    """Test detection of PDD tags in content."""
    content = """
    <pdd-reason>Test</pdd-reason>
    Rest of content
    """
    assert has_pdd_tags(content) is True


def test_has_pdd_tags_no_tags():
    """Test detection when no tags present."""
    content = "Regular prompt content without tags"
    assert has_pdd_tags(content) is False


def test_get_architecture_entry_for_prompt():
    """Test retrieving architecture entry by prompt filename."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        arch_file = tmppath / "architecture.json"

        arch_data = [
            {"filename": "test.prompt", "reason": "Test module"},
            {"filename": "other.prompt", "reason": "Other module"}
        ]
        arch_file.write_text(json.dumps(arch_data))

        entry = get_architecture_entry_for_prompt(
            "test.prompt",
            architecture_path=arch_file
        )

        assert entry is not None
        assert entry['filename'] == "test.prompt"
        assert entry['reason'] == "Test module"


def test_get_architecture_entry_for_prompt_not_found():
    """Test retrieving non-existent architecture entry."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        arch_file = tmppath / "architecture.json"
        arch_file.write_text("[]")

        entry = get_architecture_entry_for_prompt(
            "nonexistent.prompt",
            architecture_path=arch_file
        )

        assert entry is None


def test_generate_tags_from_architecture_all_fields():
    """Test generating tags from complete architecture entry."""
    arch_entry = {
        "reason": "Test module for validation",
        "interface": {
            "type": "module",
            "module": {"functions": []}
        },
        "dependencies": ["dep1.prompt", "dep2.prompt"]
    }

    tags = generate_tags_from_architecture(arch_entry)

    assert '<pdd-reason>Test module for validation</pdd-reason>' in tags
    assert '<pdd-interface>' in tags
    assert '<pdd-dependency>dep1.prompt</pdd-dependency>' in tags
    assert '<pdd-dependency>dep2.prompt</pdd-dependency>' in tags


def test_generate_tags_from_architecture_partial():
    """Test generating tags from partial architecture entry."""
    arch_entry = {
        "reason": "Only reason field",
        "dependencies": []
    }

    tags = generate_tags_from_architecture(arch_entry)

    assert '<pdd-reason>Only reason field</pdd-reason>' in tags
    assert '<pdd-interface>' not in tags
    assert '<pdd-dependency>' not in tags


def test_generate_tags_from_architecture_empty():
    """Test generating tags from empty architecture entry."""
    arch_entry = {}

    tags = generate_tags_from_architecture(arch_entry)

    assert tags == ""


# --- Test reverse direction (architecture.json → prompt generation) ---

def test_reverse_direction_tag_injection():
    """Test that tags are injected when generating new prompts."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)

        # Create architecture.json
        arch_file = tmppath / "architecture.json"
        arch_data = [{
            "filename": "new_module.prompt",
            "filepath": "pdd/new_module.py",
            "reason": "This is a new module",
            "description": "New module for testing",
            "dependencies": ["dep1.prompt", "dep2.prompt"],
            "priority": 1,
            "tags": ["module"],
            "interface": {
                "type": "module",
                "module": {
                    "functions": [
                        {"name": "test_func", "signature": "()", "returns": "None"}
                    ]
                }
            }
        }]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        # Simulate prompt generation: create content without tags
        generated_content = "% New Module Prompt\n\nYour goal is to implement..."

        # Check that content doesn't have tags
        assert not has_pdd_tags(generated_content)

        # Get architecture entry
        entry = get_architecture_entry_for_prompt(
            "new_module.prompt",
            architecture_path=arch_file
        )

        assert entry is not None

        # Generate tags
        tags = generate_tags_from_architecture(entry)

        # Inject tags (simulating what code_generator_main does)
        final_content = tags + '\n\n' + generated_content

        # Verify tags were injected
        assert has_pdd_tags(final_content)
        assert '<pdd-reason>This is a new module</pdd-reason>' in final_content
        assert '<pdd-interface>' in final_content
        assert '<pdd-dependency>dep1.prompt</pdd-dependency>' in final_content
        assert '<pdd-dependency>dep2.prompt</pdd-dependency>' in final_content

        # Verify original content is preserved
        assert 'Your goal is to implement' in final_content


def test_reverse_direction_preserve_existing_tags():
    """Test that existing tags are NOT overwritten (preserve manual edits)."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)

        # Create architecture.json with one reason
        arch_file = tmppath / "architecture.json"
        arch_data = [{
            "filename": "existing.prompt",
            "filepath": "pdd/existing.py",
            "reason": "Architecture reason",
            "description": "Test",
            "dependencies": [],
            "priority": 1,
            "tags": []
        }]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        # Content already has manually edited tags
        existing_content = """<pdd-reason>Manually edited reason</pdd-reason>

% Module Prompt

Your goal is to implement..."""

        # Should detect existing tags
        assert has_pdd_tags(existing_content)

        # Should NOT inject tags because they already exist
        entry = get_architecture_entry_for_prompt(
            "existing.prompt",
            architecture_path=arch_file
        )

        if not has_pdd_tags(existing_content):
            tags = generate_tags_from_architecture(entry)
            final_content = tags + '\n\n' + existing_content
        else:
            final_content = existing_content

        # Verify original tags preserved (not overwritten with architecture.json version)
        assert '<pdd-reason>Manually edited reason</pdd-reason>' in final_content
        assert 'Architecture reason' not in final_content


def test_reverse_direction_no_architecture_entry():
    """Test that no tags are injected if no architecture entry exists."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)

        # Empty architecture.json
        arch_file = tmppath / "architecture.json"
        arch_file.write_text("[]")

        # Prompt content
        content = "% Orphan Prompt\n\nNo architecture entry exists..."

        # Try to get architecture entry
        entry = get_architecture_entry_for_prompt(
            "orphan.prompt",
            architecture_path=arch_file
        )

        assert entry is None

        # Should not inject any tags
        if entry and not has_pdd_tags(content):
            tags = generate_tags_from_architecture(entry)
            final_content = tags + '\n\n' + content
        else:
            final_content = content

        # Verify no tags added
        assert not has_pdd_tags(final_content)
        assert final_content == content


def test_reverse_direction_partial_tags():
    """Test injection with partial architecture data (only some fields)."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)

        # Architecture with only reason (no interface or dependencies)
        arch_file = tmppath / "architecture.json"
        arch_data = [{
            "filename": "partial.prompt",
            "filepath": "pdd/partial.py",
            "reason": "Only has reason field",
            "description": "Test",
            "dependencies": [],
            "priority": 1,
            "tags": []
        }]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        # Get entry and generate tags
        entry = get_architecture_entry_for_prompt(
            "partial.prompt",
            architecture_path=arch_file
        )

        tags = generate_tags_from_architecture(entry)

        # Should only have reason tag
        assert '<pdd-reason>Only has reason field</pdd-reason>' in tags
        assert '<pdd-interface>' not in tags
        assert '<pdd-dependency>' not in tags


# --- Test has_dependency_tags flag ---

def test_parse_tags_has_dependency_tags_true():
    """Test that has_dependency_tags is True when dependency tags are present."""
    content = """
    <pdd-reason>Test module</pdd-reason>
    <pdd-dependency>dep1.prompt</pdd-dependency>
    """

    result = parse_prompt_tags(content)

    assert result['has_dependency_tags'] is True
    assert result['dependencies'] == ['dep1.prompt']


def test_parse_tags_has_dependency_tags_false():
    """Test that has_dependency_tags is False when no dependency tags present."""
    content = """
    <pdd-reason>Test module</pdd-reason>
    % No dependency tags here
    """

    result = parse_prompt_tags(content)

    assert result.get('has_dependency_tags', False) is False
    assert result['dependencies'] == []


def test_parse_tags_empty_dependency_tag():
    """Test that has_dependency_tags is True even for empty dependency tag."""
    content = """
    <pdd-reason>Test module</pdd-reason>
    <pdd-dependency></pdd-dependency>
    """

    result = parse_prompt_tags(content)

    # has_dependency_tags should be True (tag exists even if empty)
    assert result['has_dependency_tags'] is True
    # But dependencies list should be empty (no valid content)
    assert result['dependencies'] == []


# --- Test dependency clearing behavior ---

def test_dependency_clearing_when_tags_removed():
    """Test that removing all dependency tags clears dependencies in architecture."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        # Create prompt with reason but NO dependency tags
        # (simulating user removed all dependency tags)
        prompt_file = prompts_dir / "test.prompt"
        prompt_file.write_text("""
<pdd-reason>Module with dependencies removed</pdd-reason>
<pdd-interface>{"type": "module", "module": {"functions": []}}</pdd-interface>
% No dependency tags - they were removed by user
""")

        # Architecture has existing dependencies
        arch_file = tmppath / "architecture.json"
        arch_data = [{
            "filename": "test.prompt",
            "filepath": "pdd/test.py",
            "reason": "Old reason",
            "description": "Test",
            "dependencies": ["old_dep1.prompt", "old_dep2.prompt"],  # Should be cleared
            "priority": 1,
            "tags": []
        }]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        # Sync
        result = update_architecture_from_prompt(
            "test.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_file
        )

        # Verify dependencies were cleared
        assert result['success'] is True
        assert result['updated'] is True
        assert 'dependencies' in result['changes']
        assert result['changes']['dependencies']['old'] == ['old_dep1.prompt', 'old_dep2.prompt']
        assert result['changes']['dependencies']['new'] == []

        # Verify architecture.json updated
        updated = json.loads(arch_file.read_text())
        assert updated[0]['dependencies'] == []


def test_no_dependency_clearing_for_legacy_prompt():
    """Test that prompts without ANY PDD tags don't clear dependencies."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        # Legacy prompt without ANY PDD tags
        prompt_file = prompts_dir / "legacy.prompt"
        prompt_file.write_text("""
% Legacy prompt without PDD tags
Your goal is to implement...
""")

        # Architecture has dependencies
        arch_file = tmppath / "architecture.json"
        arch_data = [{
            "filename": "legacy.prompt",
            "filepath": "pdd/legacy.py",
            "reason": "Legacy module",
            "description": "Test",
            "dependencies": ["should_not_be_cleared.prompt"],
            "priority": 1,
            "tags": []
        }]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        # Sync
        result = update_architecture_from_prompt(
            "legacy.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_file
        )

        # Verify: no updates (legacy prompt has no PDD tags)
        assert result['success'] is True
        assert result['updated'] is False  # No changes made
        assert 'dependencies' not in result['changes']

        # Verify architecture.json NOT modified
        updated = json.loads(arch_file.read_text())
        assert updated[0]['dependencies'] == ["should_not_be_cleared.prompt"]


def test_dependency_add_and_remove():
    """Test adding and removing dependencies in sequence."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        arch_file = tmppath / "architecture.json"
        prompt_file = prompts_dir / "test.prompt"

        # Initial state: no dependencies in architecture
        arch_data = [{
            "filename": "test.prompt",
            "filepath": "pdd/test.py",
            "reason": "Test",
            "description": "Test",
            "dependencies": [],
            "priority": 1,
            "tags": []
        }]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        # Step 1: Add dependencies via prompt
        prompt_file.write_text("""
<pdd-reason>Test</pdd-reason>
<pdd-dependency>dep1.prompt</pdd-dependency>
<pdd-dependency>dep2.prompt</pdd-dependency>
""")

        result = update_architecture_from_prompt(
            "test.prompt", prompts_dir=prompts_dir, architecture_path=arch_file
        )
        assert result['updated'] is True
        updated = json.loads(arch_file.read_text())
        assert set(updated[0]['dependencies']) == {'dep1.prompt', 'dep2.prompt'}

        # Step 2: Remove one dependency
        prompt_file.write_text("""
<pdd-reason>Test</pdd-reason>
<pdd-dependency>dep1.prompt</pdd-dependency>
""")

        result = update_architecture_from_prompt(
            "test.prompt", prompts_dir=prompts_dir, architecture_path=arch_file
        )
        assert result['updated'] is True
        updated = json.loads(arch_file.read_text())
        assert updated[0]['dependencies'] == ['dep1.prompt']

        # Step 3: Remove ALL dependencies (keep reason tag)
        prompt_file.write_text("""
<pdd-reason>Test</pdd-reason>
% All dependencies removed
""")

        result = update_architecture_from_prompt(
            "test.prompt", prompts_dir=prompts_dir, architecture_path=arch_file
        )
        assert result['updated'] is True
        updated = json.loads(arch_file.read_text())
        assert updated[0]['dependencies'] == []


# --- Test interface JSON parse error reporting ---

def test_interface_parse_error_reported():
    """Test that JSON parse errors in interface are reported in warnings."""
    content = """
    <pdd-reason>Valid reason</pdd-reason>
    <pdd-interface>
    {invalid json - missing quotes and colons}
    </pdd-interface>
    """

    result = parse_prompt_tags(content)

    assert result['reason'] == 'Valid reason'
    assert result['interface'] is None  # Failed to parse
    assert 'interface_parse_error' in result
    assert 'Invalid JSON' in result['interface_parse_error']


def test_interface_parse_error_in_sync_result():
    """Test that interface parse errors appear in sync warnings."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        # Create prompt with invalid JSON in interface
        prompt_file = prompts_dir / "test.prompt"
        prompt_file.write_text("""
<pdd-reason>Valid reason</pdd-reason>
<pdd-interface>
{this is not valid JSON}
</pdd-interface>
""")

        arch_file = tmppath / "architecture.json"
        arch_data = [{
            "filename": "test.prompt",
            "filepath": "pdd/test.py",
            "reason": "Old reason",
            "description": "Test",
            "dependencies": [],
            "priority": 1,
            "tags": [],
            "interface": {"type": "module", "module": {"functions": []}}
        }]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        result = update_architecture_from_prompt(
            "test.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_file
        )

        # Should succeed but with warnings
        assert result['success'] is True
        assert 'warnings' in result
        assert len(result['warnings']) > 0
        assert any('Invalid JSON' in w for w in result['warnings'])


# --- Test interface update scenarios ---

def test_interface_update_from_none_to_value():
    """Test updating interface from None to a value."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        prompt_file = prompts_dir / "test.prompt"
        prompt_file.write_text("""
<pdd-reason>Test</pdd-reason>
<pdd-interface>
{"type": "module", "module": {"functions": [{"name": "test", "signature": "()", "returns": "None"}]}}
</pdd-interface>
""")

        arch_file = tmppath / "architecture.json"
        arch_data = [{
            "filename": "test.prompt",
            "filepath": "pdd/test.py",
            "reason": "Test",
            "description": "Test",
            "dependencies": [],
            "priority": 1,
            "tags": [],
            "interface": None  # Start with no interface
        }]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        result = update_architecture_from_prompt(
            "test.prompt", prompts_dir=prompts_dir, architecture_path=arch_file
        )

        assert result['updated'] is True
        assert 'interface' in result['changes']
        assert result['changes']['interface']['old'] is None

        updated = json.loads(arch_file.read_text())
        assert updated[0]['interface'] is not None
        assert updated[0]['interface']['type'] == 'module'


def test_interface_update_changes_detected():
    """Test that interface changes are properly detected."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        # New interface with additional function
        prompt_file = prompts_dir / "test.prompt"
        prompt_file.write_text("""
<pdd-reason>Test</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "func1", "signature": "()", "returns": "None"},
      {"name": "func2", "signature": "(x: int)", "returns": "int"}
    ]
  }
}
</pdd-interface>
""")

        arch_file = tmppath / "architecture.json"
        arch_data = [{
            "filename": "test.prompt",
            "filepath": "pdd/test.py",
            "reason": "Test",
            "description": "Test",
            "dependencies": [],
            "priority": 1,
            "tags": [],
            "interface": {
                "type": "module",
                "module": {
                    "functions": [
                        {"name": "func1", "signature": "()", "returns": "None"}
                    ]
                }
            }
        }]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        result = update_architecture_from_prompt(
            "test.prompt", prompts_dir=prompts_dir, architecture_path=arch_file
        )

        assert result['updated'] is True
        assert 'interface' in result['changes']

        updated = json.loads(arch_file.read_text())
        funcs = updated[0]['interface']['module']['functions']
        assert len(funcs) == 2
        assert any(f['name'] == 'func2' for f in funcs)


def test_interface_no_update_when_same():
    """Test that no update occurs when interface is identical."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        interface_json = {"type": "module", "module": {"functions": []}}

        prompt_file = prompts_dir / "test.prompt"
        prompt_file.write_text(f"""
<pdd-reason>Same reason</pdd-reason>
<pdd-interface>
{json.dumps(interface_json)}
</pdd-interface>
""")

        arch_file = tmppath / "architecture.json"
        arch_data = [{
            "filename": "test.prompt",
            "filepath": "pdd/test.py",
            "reason": "Same reason",
            "description": "Test",
            "dependencies": [],
            "priority": 1,
            "tags": [],
            "interface": interface_json
        }]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        result = update_architecture_from_prompt(
            "test.prompt", prompts_dir=prompts_dir, architecture_path=arch_file
        )

        # No changes should be detected
        assert result['success'] is True
        assert result['updated'] is False
        assert result['changes'] == {}


# --- Test edge cases ---

def test_whitespace_in_tags():
    """Test that whitespace in tags is properly handled."""
    content = """
    <pdd-reason>
        Reason with leading and trailing whitespace
    </pdd-reason>
    <pdd-dependency>  dep1.prompt  </pdd-dependency>
    <pdd-dependency>
        dep2.prompt
    </pdd-dependency>
    """

    result = parse_prompt_tags(content)

    assert result['reason'] == 'Reason with leading and trailing whitespace'
    assert 'dep1.prompt' in result['dependencies']
    assert 'dep2.prompt' in result['dependencies']


def test_special_characters_in_reason():
    """Test that special characters in reason are handled."""
    content = """
    <pdd-reason>Module for &amp; handling "special" <characters></pdd-reason>
    """

    result = parse_prompt_tags(content)

    # XML entities should be decoded
    assert result['reason'] is not None
    assert 'special' in result['reason']


def test_multiline_interface_json():
    """Test parsing of multiline prettified JSON in interface."""
    content = """
<pdd-interface>
{
    "type": "module",
    "module": {
        "functions": [
            {
                "name": "complex_func",
                "signature": "(arg1: str, arg2: int, arg3: Optional[Dict] = None) -> Tuple[bool, str]",
                "returns": "Tuple[bool, str]",
                "sideEffects": [
                    "Logs to file",
                    "Updates cache",
                    "Sends notification"
                ]
            }
        ]
    }
}
</pdd-interface>
"""

    result = parse_prompt_tags(content)

    assert result['interface'] is not None
    assert result['interface']['type'] == 'module'
    funcs = result['interface']['module']['functions']
    assert len(funcs) == 1
    assert funcs[0]['name'] == 'complex_func'
    assert len(funcs[0]['sideEffects']) == 3


def test_concurrent_updates_different_modules():
    """Test that updating different modules doesn't interfere."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        # Create two prompts
        (prompts_dir / "module1.prompt").write_text("<pdd-reason>Module 1 Updated</pdd-reason>")
        (prompts_dir / "module2.prompt").write_text("<pdd-reason>Module 2 Updated</pdd-reason>")

        arch_file = tmppath / "architecture.json"
        arch_data = [
            {"filename": "module1.prompt", "filepath": "m1.py", "reason": "Old 1",
             "description": "D1", "dependencies": [], "priority": 1, "tags": []},
            {"filename": "module2.prompt", "filepath": "m2.py", "reason": "Old 2",
             "description": "D2", "dependencies": [], "priority": 2, "tags": []},
        ]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        # Update module1
        result1 = update_architecture_from_prompt(
            "module1.prompt", prompts_dir=prompts_dir, architecture_path=arch_file
        )

        # Update module2
        result2 = update_architecture_from_prompt(
            "module2.prompt", prompts_dir=prompts_dir, architecture_path=arch_file
        )

        assert result1['success'] and result1['updated']
        assert result2['success'] and result2['updated']

        # Verify both were updated correctly
        final = json.loads(arch_file.read_text())
        m1 = next(m for m in final if m['filename'] == 'module1.prompt')
        m2 = next(m for m in final if m['filename'] == 'module2.prompt')
        assert m1['reason'] == 'Module 1 Updated'
        assert m2['reason'] == 'Module 2 Updated'


def test_sync_all_with_mixed_prompts():
    """Test sync_all with mix of prompts with and without tags."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmppath = Path(tmpdir)
        prompts_dir = tmppath / "prompts"
        prompts_dir.mkdir()

        # Prompt with all tags
        (prompts_dir / "full.prompt").write_text("""
<pdd-reason>Full module</pdd-reason>
<pdd-interface>{"type": "module", "module": {"functions": []}}</pdd-interface>
<pdd-dependency>dep.prompt</pdd-dependency>
""")
        # Prompt with only reason
        (prompts_dir / "partial.prompt").write_text("<pdd-reason>Partial</pdd-reason>")
        # Prompt with no tags
        (prompts_dir / "legacy.prompt").write_text("% No tags")
        # Prompt not in architecture
        (prompts_dir / "orphan.prompt").write_text("<pdd-reason>Orphan</pdd-reason>")

        arch_file = tmppath / "architecture.json"
        arch_data = [
            {"filename": "full.prompt", "filepath": "f.py", "reason": "Old",
             "description": "F", "dependencies": [], "priority": 1, "tags": []},
            {"filename": "partial.prompt", "filepath": "p.py", "reason": "Old",
             "description": "P", "dependencies": ["old_dep.prompt"], "priority": 2, "tags": []},
            {"filename": "legacy.prompt", "filepath": "l.py", "reason": "Legacy",
             "description": "L", "dependencies": ["should_keep.prompt"], "priority": 3, "tags": []},
        ]
        arch_file.write_text(json.dumps(arch_data, indent=2))

        result = sync_all_prompts_to_architecture(
            prompts_dir=prompts_dir,
            architecture_path=arch_file
        )

        assert result['success'] is True

        final = json.loads(arch_file.read_text())
        full = next(m for m in final if m['filename'] == 'full.prompt')
        partial = next(m for m in final if m['filename'] == 'partial.prompt')
        legacy = next(m for m in final if m['filename'] == 'legacy.prompt')

        # Full should have all updates
        assert full['reason'] == 'Full module'
        assert full['dependencies'] == ['dep.prompt']
        assert full['interface'] is not None

        # Partial should have reason updated and deps cleared (has other PDD tags)
        assert partial['reason'] == 'Partial'
        assert partial['dependencies'] == []  # Cleared because has <pdd-reason> but no deps

        # Legacy should be unchanged (no PDD tags)
        assert legacy['reason'] == 'Legacy'
        assert legacy['dependencies'] == ['should_keep.prompt']


# --- Test JSON trailing comma handling ---

def test_interface_json_trailing_comma():
    """Test that JSON with trailing comma fails gracefully."""
    content = """
<pdd-interface>
{
    "type": "module",
    "module": {
        "functions": [
            {"name": "func1", "signature": "()", "returns": "None"},
        ]
    }
}
</pdd-interface>
"""

    result = parse_prompt_tags(content)

    # Should fail to parse due to trailing comma
    assert result['interface'] is None
    assert 'interface_parse_error' in result
