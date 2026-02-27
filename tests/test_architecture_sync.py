"""
Unit tests for architecture_sync module.

Tests bidirectional sync between architecture.json and prompt file metadata tags.
"""

import json
import tempfile
from pathlib import Path

import pytest

from pdd.architecture_sync import (
    _find_renamed_prompt_file,
    _infer_filepath,
    _infer_module_tags,
    generate_tags_from_architecture,
    get_architecture_entry_for_prompt,
    has_pdd_tags,
    parse_prompt_tags,
    register_untracked_prompts,
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


# --- Regression tests for issue #550: corrupted dependency values ---

def test_parse_tags_rejects_multiline_dependency():
    """Dependency containing newlines (prompt content blob) must be rejected.

    Regression for issue #550: pdd change step 10 wrote the entire prompt file
    content as a dependency string when it confused example tags with real ones.
    """
    corrupted_dep = "` tags:\n      - Extract from `<include>` directives\n      - Only include .prompt files\nllm_invoke_python.prompt"
    content = f"<pdd-dependency>{corrupted_dep}</pdd-dependency>"

    result = parse_prompt_tags(content)

    assert result['dependencies'] == [], (
        "Multiline dependency value should be rejected"
    )


def test_parse_tags_rejects_dependency_over_100_chars():
    """Dependency longer than 100 chars must be rejected.

    Regression for issue #550: the corrupted value was hundreds of characters long.
    """
    long_dep = "a" * 101 + ".prompt"
    content = f"<pdd-dependency>{long_dep}</pdd-dependency>"

    result = parse_prompt_tags(content)

    assert result['dependencies'] == [], (
        "Dependency value over 100 chars should be rejected"
    )


def test_parse_tags_rejects_dependency_not_ending_in_prompt():
    """Dependency not ending in .prompt must be rejected."""
    content = "<pdd-dependency>some_python_file.py</pdd-dependency>"

    result = parse_prompt_tags(content)

    assert result['dependencies'] == [], (
        "Non-.prompt dependency should be rejected"
    )


def test_parse_tags_accepts_valid_dependency_alongside_corrupted():
    """Valid .prompt dependency is kept even when another dep is corrupted.

    Regression for issue #550: architecture.json had one corrupted dep and one
    valid dep (path_resolution_python.prompt). The valid one must be preserved.
    """
    corrupted = "` tags:\n      - Extract from includes\nllm_invoke_python.prompt"
    content = (
        f"<pdd-dependency>{corrupted}</pdd-dependency>\n"
        "<pdd-dependency>path_resolution_python.prompt</pdd-dependency>"
    )

    result = parse_prompt_tags(content)

    assert result['dependencies'] == ['path_resolution_python.prompt']


# --- Regression tests for _sanitize_architecture_dependencies ---

def test_sanitize_architecture_dependencies_removes_corrupted_dep():
    """_sanitize_architecture_dependencies cleans corrupted deps from architecture.json.

    Regression for issue #550: after step 10 writes a corrupted dependency,
    the sanitizer must strip it so Dev Units validation passes.
    """
    import json
    import tempfile
    from pathlib import Path
    from pdd.agentic_change_orchestrator import _sanitize_architecture_dependencies

    corrupted_dep = "` tags:\n      - Extract from `<include>` directives\nllm_invoke_python.prompt"
    arch_data = [
        {
            "filename": "agentic_change_step10_architecture_update_LLM.prompt",
            "dependencies": [corrupted_dep, "path_resolution_python.prompt"],
        }
    ]

    with tempfile.TemporaryDirectory() as tmpdir:
        arch_path = Path(tmpdir) / "architecture.json"
        arch_path.write_text(json.dumps(arch_data, indent=2))

        _sanitize_architecture_dependencies(Path(tmpdir))

        result = json.loads(arch_path.read_text())
        assert result[0]["dependencies"] == ["path_resolution_python.prompt"]


def test_sanitize_architecture_dependencies_leaves_valid_deps_untouched():
    """_sanitize_architecture_dependencies must not modify clean architecture.json."""
    import json
    import tempfile
    from pathlib import Path
    from pdd.agentic_change_orchestrator import _sanitize_architecture_dependencies

    arch_data = [
        {
            "filename": "llm_invoke_python.prompt",
            "dependencies": ["path_resolution_python.prompt", "construct_paths_python.prompt"],
        }
    ]

    with tempfile.TemporaryDirectory() as tmpdir:
        arch_path = Path(tmpdir) / "architecture.json"
        arch_path.write_text(json.dumps(arch_data, indent=2))

        _sanitize_architecture_dependencies(Path(tmpdir))

        result = json.loads(arch_path.read_text())
        assert result[0]["dependencies"] == [
            "path_resolution_python.prompt",
            "construct_paths_python.prompt",
        ]


def test_sanitize_architecture_dependencies_no_file_is_noop():
    """_sanitize_architecture_dependencies must not crash if no architecture.json."""
    import tempfile
    from pathlib import Path
    from pdd.agentic_change_orchestrator import _sanitize_architecture_dependencies

    with tempfile.TemporaryDirectory() as tmpdir:
        _sanitize_architecture_dependencies(Path(tmpdir))  # should not raise


# --- Tests for issue #566: parse_prompt_tags must ignore tags inside code fences ---


def test_parse_tags_ignores_fenced_example_prefers_real_tag():
    """Tags inside code fences must be ignored; real tag in header is extracted.

    Regression for issue #566: parse_prompt_tags() used to scan the entire file,
    picking up example tags in code fences as real metadata.

    Fix: only parse content before the first % section marker. Real tags are
    always declared in the header (before any % section); examples live in the
    body sections.
    """
    content = """<pdd-reason>Real reason for this module</pdd-reason>

% Examples

Here is an example of how to use pdd-reason:

```xml
<pdd-reason>Example reason shown in docs</pdd-reason>
```
"""

    result = parse_prompt_tags(content)

    # The real tag (in header) should be extracted, not the fenced example
    assert result['reason'] == 'Real reason for this module', (
        f"Expected 'Real reason for this module' but got '{result['reason']}' — "
        "parser is extracting example tags from inside code fences"
    )


def test_parse_tags_ignores_all_tag_types_in_fences():
    """All pdd-* tag types inside code fences must be ignored.

    Regression for issue #566: the actual prompt file
    agentic_change_step10_architecture_update_LLM.prompt has example
    <pdd-reason>, <pdd-interface>, and <pdd-dependency> tags inside
    code fences that get incorrectly extracted.
    """
    content = """<pdd-reason>Real module reason</pdd-reason>
<pdd-interface>{"type": "module", "module": {"functions": []}}</pdd-interface>
<pdd-dependency>real_dep.prompt</pdd-dependency>

% Examples

Here are examples of how to format the tags in your output:

```xml
<pdd-reason>The reason for this module's existence</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "example_func", "signature": "()", "returns": "None"}
    ]
  }
}
</pdd-interface>
<pdd-dependency>example_dep.prompt</pdd-dependency>
<pdd-dependency>another_example.prompt</pdd-dependency>
```
"""

    result = parse_prompt_tags(content)

    assert result['reason'] == 'Real module reason'
    assert result['interface'] is not None
    assert result['interface']['type'] == 'module'
    # Only the real dependency should be extracted, not the fenced examples
    assert result['dependencies'] == ['real_dep.prompt'], (
        f"Expected ['real_dep.prompt'] but got {result['dependencies']} — "
        "parser is extracting example dependencies from inside code fences"
    )


def test_parse_tags_returns_empty_when_all_tags_in_fences():
    """When ALL pdd-* tags are inside code fences, parser should return empty results.

    Regression for issue #566: the step10 prompt file has no real top-level tags,
    only examples inside code fences. The parser should return None/empty for all
    fields, not extract the fenced examples as real metadata.
    """
    content = """
% This prompt instructs the LLM how to generate architecture tags.

Your output should follow this structure:

```xml
<pdd-reason>Describe the module's purpose</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "my_func", "signature": "(arg: str)", "returns": "str"}
    ]
  }
}
</pdd-interface>
<pdd-dependency>some_module.prompt</pdd-dependency>
```

Make sure to include all relevant tags.
"""

    result = parse_prompt_tags(content)

    assert result['reason'] is None, (
        f"Expected None but got '{result['reason']}' — "
        "parser extracted a reason from inside a code fence"
    )
    assert result['interface'] is None, (
        "Parser extracted an interface from inside a code fence"
    )
    assert result['dependencies'] == [], (
        f"Expected [] but got {result['dependencies']} — "
        "parser extracted dependencies from inside a code fence"
    )


def test_parse_tags_ignores_inline_backtick_references():
    """Inline backtick references in body prose must not be extracted as tags.

    Regression for issue #566: inline backtick references like `<pdd-reason>`
    in instructional body text get recovered by lxml as actual XML elements with
    garbled text content, corrupting the extracted metadata.

    Fix: only parse the header (before first % section). Instructional prose with
    inline backtick references lives in body sections, never in the header.
    """
    content = """<pdd-reason>Real reason value</pdd-reason>

% Instructions

Generate a `<pdd-reason>` tag with the module's purpose.
Also generate `<pdd-interface>` and `<pdd-dependency>` tags.
"""

    result = parse_prompt_tags(content)

    # Only the real header tag should be extracted, not the backtick references
    assert result['reason'] == 'Real reason value', (
        f"Expected 'Real reason value' but got '{result['reason']}' — "
        "parser is confused by inline backtick references in body"
    )
    # Inline backtick references to interface/dependency should not produce results
    assert result['interface'] is None
    assert result['dependencies'] == []


def test_parse_tags_extracts_real_tags_adjacent_to_fences():
    """Real tags in the header are extracted even when fenced examples exist in body.

    Ensures the fix doesn't over-strip — real tags declared in the header
    (before the first % section) must still be extracted correctly, while
    fenced example tags in body sections are ignored.
    """
    content = """<pdd-reason>Reason at top</pdd-reason>
<pdd-dependency>real_dep.prompt</pdd-dependency>

% Examples

```xml
<pdd-reason>Fenced example reason</pdd-reason>
<pdd-dependency>fenced_dep.prompt</pdd-dependency>
```
"""

    result = parse_prompt_tags(content)

    assert result['reason'] == 'Reason at top', (
        f"Expected 'Reason at top' but got '{result['reason']}'"
    )
    assert result['dependencies'] == ['real_dep.prompt'], (
        f"Expected ['real_dep.prompt'] but got {result['dependencies']} — "
        "parser should only extract real header dependencies, not fenced examples"
    )


def test_parse_tags_real_world_step10_prompt_pattern():
    """Regression test matching the actual step10 prompt file structure.

    The file agentic_change_step10_architecture_update_LLM.prompt has NO real
    top-level pdd-* tags — only instructional examples inside code fences.
    The parser must return empty results for this pattern.

    This directly reproduces the bug reported in issue #566.
    """
    content = """% Architecture Update Step

You are updating the architecture.json file for a PDD project.

% Instructions

For each module, generate the following tags:

```xml
<pdd-reason>Brief description of why this module exists</pdd-reason>
```

For interfaces, use this format:

```xml
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "parse_prompt_tags", "signature": "(prompt_content: str)", "returns": "Dict[str, Any]"}
    ]
  }
}
</pdd-interface>
```

For dependencies, list each one:

```xml
<pdd-dependency>path_resolution_python.prompt</pdd-dependency>
<pdd-dependency>construct_paths_python.prompt</pdd-dependency>
```

% Important: Only include dependencies that are actually used.
"""

    result = parse_prompt_tags(content)

    # No real tags exist outside code fences — all fields should be empty
    assert result['reason'] is None, (
        f"Expected None but got '{result['reason']}' — "
        "step10 prompt pattern: parser extracted example reason from code fence"
    )
    assert result['interface'] is None, (
        "step10 prompt pattern: parser extracted example interface from code fence"
    )
    assert result['dependencies'] == [], (
        f"Expected [] but got {result['dependencies']} — "
        "step10 prompt pattern: parser extracted example dependencies from code fences"
    )


def test_parse_tags_ignores_tilde_fenced_tags():
    """Tags inside tilde-style code fences (~~~) must also be ignored.

    The _extract_fence_spans utility in preprocess.py recognizes both backtick
    and tilde fences. The fix for parse_prompt_tags should be consistent.
    """
    content = """<pdd-reason>Real reason outside tilde fence</pdd-reason>

% Examples

~~~xml
<pdd-reason>Tilde-fenced example reason</pdd-reason>
<pdd-dependency>tilde_fenced_dep.prompt</pdd-dependency>
~~~
"""

    result = parse_prompt_tags(content)

    assert result['reason'] == 'Real reason outside tilde fence', (
        f"Expected 'Real reason outside tilde fence' but got '{result['reason']}' — "
        "parser is extracting tags from inside tilde code fences"
    )
    assert result['dependencies'] == [], (
        f"Expected [] but got {result['dependencies']} — "
        "parser is extracting dependencies from inside tilde code fences"
    )


# --- Tests for auto-rename and auto-register features ---

def test_find_renamed_prompt_file_finds_step_file():
    """_find_renamed_prompt_file returns renamed path when exactly one step-numbered variant exists."""
    with tempfile.TemporaryDirectory() as tmp:
        prompts_dir = Path(tmp)
        # step5_design exists on disk but step4_design does not
        (prompts_dir / 'agentic_arch_step5_design_LLM.prompt').write_text('content')

        result = _find_renamed_prompt_file('agentic_arch_step4_design_LLM.prompt', prompts_dir)

        assert result is not None
        assert result.name == 'agentic_arch_step5_design_LLM.prompt'


def test_find_renamed_prompt_file_no_match():
    """_find_renamed_prompt_file returns None when no similarly-named file exists."""
    with tempfile.TemporaryDirectory() as tmp:
        prompts_dir = Path(tmp)
        # No files at all

        result = _find_renamed_prompt_file('agentic_arch_step4_design_LLM.prompt', prompts_dir)

        assert result is None


def test_find_renamed_prompt_file_ambiguous():
    """_find_renamed_prompt_file returns None when multiple step-number variants exist."""
    with tempfile.TemporaryDirectory() as tmp:
        prompts_dir = Path(tmp)
        (prompts_dir / 'agentic_arch_step5_design_LLM.prompt').write_text('content')
        (prompts_dir / 'agentic_arch_step6_design_LLM.prompt').write_text('content')

        result = _find_renamed_prompt_file('agentic_arch_step4_design_LLM.prompt', prompts_dir)

        assert result is None


def test_find_renamed_prompt_file_no_step_pattern():
    """_find_renamed_prompt_file returns None for filenames without step number pattern."""
    with tempfile.TemporaryDirectory() as tmp:
        prompts_dir = Path(tmp)
        (prompts_dir / 'cli_detector_python.prompt').write_text('content')

        result = _find_renamed_prompt_file('cli_detector_python.prompt', prompts_dir)

        assert result is None


def test_update_uses_renamed_file():
    """update_architecture_from_prompt auto-renames arch.json entry and syncs from the found file."""
    with tempfile.TemporaryDirectory() as tmp:
        prompts_dir = Path(tmp)
        arch_path = Path(tmp) / 'architecture.json'

        # Disk has step5 but arch.json references step4
        step5_content = '<pdd-reason>Design step 5</pdd-reason>\n% body'
        (prompts_dir / 'agentic_arch_step5_design_LLM.prompt').write_text(step5_content)

        arch_data = [
            {
                'filename': 'agentic_arch_step4_design_LLM.prompt',
                'filepath': 'prompts/agentic_arch_step4_design_LLM.prompt',
                'reason': 'Old reason',
                'dependencies': [],
                'priority': 1,
            }
        ]
        arch_path.write_text(json.dumps(arch_data, indent=2) + '\n')

        result = update_architecture_from_prompt(
            'agentic_arch_step4_design_LLM.prompt',
            prompts_dir=prompts_dir,
            architecture_path=arch_path,
        )

        assert result['success'] is True
        # Should have updated filename and reason
        updated_arch = json.loads(arch_path.read_text())
        assert updated_arch[0]['filename'] == 'agentic_arch_step5_design_LLM.prompt'
        assert updated_arch[0]['filepath'] == 'prompts/agentic_arch_step5_design_LLM.prompt'
        assert updated_arch[0]['reason'] == 'Design step 5'


def test_update_uses_renamed_file_dry_run():
    """update_architecture_from_prompt dry_run does not write changes."""
    with tempfile.TemporaryDirectory() as tmp:
        prompts_dir = Path(tmp)
        arch_path = Path(tmp) / 'architecture.json'

        (prompts_dir / 'agentic_arch_step5_design_LLM.prompt').write_text(
            '<pdd-reason>Design step 5</pdd-reason>\n% body'
        )

        arch_data = [
            {
                'filename': 'agentic_arch_step4_design_LLM.prompt',
                'filepath': 'prompts/agentic_arch_step4_design_LLM.prompt',
                'reason': 'Old reason',
                'dependencies': [],
                'priority': 1,
            }
        ]
        original_text = json.dumps(arch_data, indent=2) + '\n'
        arch_path.write_text(original_text)

        result = update_architecture_from_prompt(
            'agentic_arch_step4_design_LLM.prompt',
            prompts_dir=prompts_dir,
            architecture_path=arch_path,
            dry_run=True,
        )

        assert result['success'] is True
        # File should be unchanged in dry_run mode
        assert arch_path.read_text() == original_text


def test_infer_filepath_python():
    """_infer_filepath returns pdd/<module>.py for _python.prompt files."""
    assert _infer_filepath('cli_detector_python.prompt') == 'pdd/cli_detector.py'


def test_infer_filepath_llm():
    """_infer_filepath returns prompts/<filename> for _LLM.prompt files."""
    assert _infer_filepath('agentic_arch_step5_design_LLM.prompt') == 'prompts/agentic_arch_step5_design_LLM.prompt'


def test_infer_module_tags_python():
    """_infer_module_tags returns ['module', 'python'] for _python.prompt files."""
    assert _infer_module_tags('cli_detector_python.prompt') == ['module', 'python']


def test_infer_module_tags_llm():
    """_infer_module_tags returns ['llm'] for _LLM.prompt files."""
    assert _infer_module_tags('agentic_arch_step5_design_LLM.prompt') == ['llm']


def test_register_untracked_prompts_adds_entry():
    """register_untracked_prompts registers a prompt with PDD tags not in arch.json."""
    with tempfile.TemporaryDirectory() as tmp:
        prompts_dir = Path(tmp)
        arch_path = Path(tmp) / 'architecture.json'

        # cli_detector_python.prompt has PDD tags but no arch.json entry
        (prompts_dir / 'cli_detector_python.prompt').write_text(
            '<pdd-reason>Detects CLI invocation context</pdd-reason>\n% body'
        )
        # Already-registered module
        (prompts_dir / 'existing_python.prompt').write_text(
            '<pdd-reason>Existing module</pdd-reason>\n% body'
        )

        arch_data = [
            {
                'filename': 'existing_python.prompt',
                'filepath': 'pdd/existing.py',
                'reason': 'Existing module',
                'dependencies': [],
                'priority': 1,
            }
        ]
        arch_path.write_text(json.dumps(arch_data, indent=2) + '\n')

        result = register_untracked_prompts(prompts_dir=prompts_dir, architecture_path=arch_path)

        assert 'cli_detector_python.prompt' in result['registered']
        assert 'existing_python.prompt' not in result['registered']

        # Verify written to arch.json
        updated = json.loads(arch_path.read_text())
        filenames = [m['filename'] for m in updated]
        assert 'cli_detector_python.prompt' in filenames

        # Check inferred fields
        cli_entry = next(m for m in updated if m['filename'] == 'cli_detector_python.prompt')
        assert cli_entry['filepath'] == 'pdd/cli_detector.py'
        assert cli_entry['reason'] == 'Detects CLI invocation context'
        assert 'python' in cli_entry['tags']


def test_register_skips_file_without_tags():
    """register_untracked_prompts skips prompt files with no PDD tags."""
    with tempfile.TemporaryDirectory() as tmp:
        prompts_dir = Path(tmp)
        arch_path = Path(tmp) / 'architecture.json'

        # No PDD tags
        (prompts_dir / 'bare_module_python.prompt').write_text('% Just a body, no tags\n')

        arch_path.write_text(json.dumps([], indent=2) + '\n')

        result = register_untracked_prompts(prompts_dir=prompts_dir, architecture_path=arch_path)

        assert 'bare_module_python.prompt' not in result['registered']
        assert 'bare_module_python.prompt' in result['skipped']

        # Arch.json should remain empty
        assert json.loads(arch_path.read_text()) == []


def test_register_untracked_prompts_dry_run():
    """register_untracked_prompts dry_run does not write to arch.json."""
    with tempfile.TemporaryDirectory() as tmp:
        prompts_dir = Path(tmp)
        arch_path = Path(tmp) / 'architecture.json'

        (prompts_dir / 'cli_detector_python.prompt').write_text(
            '<pdd-reason>Detects CLI</pdd-reason>\n% body'
        )
        arch_path.write_text(json.dumps([], indent=2) + '\n')

        result = register_untracked_prompts(
            prompts_dir=prompts_dir, architecture_path=arch_path, dry_run=True
        )

        assert 'cli_detector_python.prompt' in result['registered']
        # File should be unchanged
        assert json.loads(arch_path.read_text()) == []


def test_sync_all_auto_registers_before_syncing():
    """sync_all_prompts_to_architecture registers untracked files and handles renamed files."""
    with tempfile.TemporaryDirectory() as tmp:
        prompts_dir = Path(tmp)
        arch_path = Path(tmp) / 'architecture.json'

        # Disk: step5_design exists, cli_detector exists
        (prompts_dir / 'agentic_arch_step5_design_LLM.prompt').write_text(
            '<pdd-reason>Design step</pdd-reason>\n% body'
        )
        (prompts_dir / 'cli_detector_python.prompt').write_text(
            '<pdd-reason>Detects CLI</pdd-reason>\n% body'
        )
        (prompts_dir / 'existing_python.prompt').write_text(
            '<pdd-reason>Existing updated</pdd-reason>\n% body'
        )

        # arch.json: step4_design (stale name), existing (registered), no cli_detector
        arch_data = [
            {
                'filename': 'agentic_arch_step4_design_LLM.prompt',
                'filepath': 'prompts/agentic_arch_step4_design_LLM.prompt',
                'reason': 'Old design',
                'dependencies': [],
                'priority': 1,
            },
            {
                'filename': 'existing_python.prompt',
                'filepath': 'pdd/existing.py',
                'reason': 'Old reason',
                'dependencies': [],
                'priority': 2,
            },
        ]
        arch_path.write_text(json.dumps(arch_data, indent=2) + '\n')

        result = sync_all_prompts_to_architecture(
            prompts_dir=prompts_dir,
            architecture_path=arch_path,
        )

        assert result['success'] is True

        # Check registered field is present
        assert 'registered' in result
        assert 'cli_detector_python.prompt' in result['registered']

        # Verify arch.json has all three modules
        updated = json.loads(arch_path.read_text())
        filenames = [m['filename'] for m in updated]
        assert 'cli_detector_python.prompt' in filenames
        assert 'agentic_arch_step5_design_LLM.prompt' in filenames
        assert 'agentic_arch_step4_design_LLM.prompt' not in filenames
        assert 'existing_python.prompt' in filenames
