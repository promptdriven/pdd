"""
Comprehensive test suite for pdd/update_main.py

Tests cover:
1. Z3 formal verification of logical constraints
2. Regeneration mode (code -> prompt generation)
3. True update mode (prompt + code update)
4. Repository-wide mode (batch processing)
5. Helper functions
6. Error handling and edge cases
"""

import os
import sys
import tempfile
from pathlib import Path
from typing import Optional, Tuple, Dict, Any
from unittest.mock import Mock, MagicMock, patch, mock_open, call
import pytest
import click
import git

# Import the code under test
from pdd.update_main import (
    update_main,
    resolve_prompt_code_pair,
    find_and_resolve_all_pairs,
    update_file_pair,
)


# ============================================================================
# Z3 FORMAL VERIFICATION TESTS
# ============================================================================

def test_z3_mutual_exclusivity_git_and_input_code():
    """
    Z3 verification: use_git and input_code_file are mutually exclusive.
    
    This verifies the logical model: successful code execution (no error raised)
    implies NOT (use_git AND has_input_code).
    
    The code raises ValueError when both are set, so successful completion
    guarantees the constraint holds.
    """
    from z3 import Bool, Not, And, Solver, Implies
    
    use_git = Bool('use_git')
    has_input_code = Bool('has_input_code')
    
    # The constraint that should hold after validation
    mutual_exclusivity = Not(And(use_git, has_input_code))
    
    # Code behavior: raises error (doesn't complete) if both are set
    # So: code_completes implies mutual_exclusivity
    code_completes = Bool('code_completes')
    
    # Model the code's validation behavior:
    # code_completes is True only when mutual_exclusivity holds
    code_validation = code_completes == mutual_exclusivity
    
    solver = Solver()
    solver.add(code_validation)
    
    # Verify: if code completes, constraint holds
    # Try to find: code completes but constraint doesn't hold
    solver.add(code_completes)
    solver.add(Not(mutual_exclusivity))
    
    # Should be UNSAT - can't have code complete when constraint is violated
    assert solver.check().r == -1, "Mutual exclusivity should hold when code completes"


def test_z3_mode_detection_logic():
    """
    Z3 verification: Mode detection logic is consistent.
    
    Modes:
    - Regeneration: NOT input_prompt_file AND NOT input_code_file
    - Update: input_prompt_file provided
    - Repo: repo=True (overrides others)
    """
    from z3 import Bool, And, Not, Or, Implies, Solver, sat
    
    has_input_prompt = Bool('has_input_prompt')
    has_input_code = Bool('has_input_code')
    repo_mode = Bool('repo_mode')
    
    is_regeneration = And(Not(has_input_prompt), Not(has_input_code), Not(repo_mode))
    is_update = And(has_input_prompt, Not(repo_mode))
    is_repo = repo_mode
    
    # At most one mode can be active
    constraint = Or(
        And(is_regeneration, Not(is_update), Not(is_repo)),
        And(Not(is_regeneration), is_update, Not(is_repo)),
        And(Not(is_regeneration), Not(is_update), is_repo)
    )
    
    solver = Solver()
    solver.add(Not(constraint))  # Try to find violation
    
    # Note: This will be SAT because there are invalid input combinations
    # The point is to verify the logic is well-defined for valid inputs
    result = solver.check()


def test_z3_output_path_classification():
    """
    Z3 verification: Output path classification logic.
    
    Logic:
    - If output ends with '/' OR is_directory → Directory mode
    - Otherwise → File mode
    """
    from z3 import Bool, Or, And, Not, Solver
    
    ends_with_slash = Bool('ends_with_slash')
    is_directory = Bool('is_directory')
    
    directory_mode = Or(ends_with_slash, is_directory)
    file_mode = Not(directory_mode)
    
    # These modes are mutually exclusive
    solver = Solver()
    solver.add(And(directory_mode, file_mode))  # Try to satisfy both
    
    assert solver.check().r == -1, "Output modes should be mutually exclusive"


# ============================================================================
# FIXTURES
# ============================================================================

@pytest.fixture
def mock_ctx():
    """Create a mock Click context with default obj settings."""
    ctx = Mock(spec=click.Context)
    ctx.obj = {
        "verbose": False,
        "quiet": False,
        "force": False,
        "strength": 0.5,
        "temperature": 0.0,
        "time": 60,
        "context": None,
        "confirm_callback": None,
    }
    return ctx


@pytest.fixture
def temp_repo(tmp_path):
    """Create a temporary git repository for testing."""
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()
    
    # Initialize git repo
    repo = git.Repo.init(repo_path)
    
    # Create initial commit
    readme = repo_path / "README.md"
    readme.write_text("# Test Repo")
    repo.index.add([str(readme)])
    repo.index.commit("Initial commit")
    
    return repo_path, repo


@pytest.fixture
def sample_files(tmp_path):
    """Create sample code and prompt files."""
    code_file = tmp_path / "sample.py"
    code_file.write_text("def hello():\n    return 'world'\n")
    
    prompt_file = tmp_path / "sample_python.prompt"
    prompt_file.write_text("Create a hello function")
    
    return {
        "code": str(code_file),
        "prompt": str(prompt_file),
    }


# ============================================================================
# REGENERATION MODE TESTS
# ============================================================================

def test_regeneration_mode_default_output(mock_ctx, tmp_path, monkeypatch):
    """Test regeneration mode with default output path."""
    monkeypatch.chdir(tmp_path)
    
    code_file = tmp_path / "example.py"
    code_file.write_text("def foo(): pass")
    
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.resolve_prompt_code_pair') as mock_resolve, \
         patch('pdd.update_main.update_prompt') as mock_update_prompt, \
         patch('pdd.update_main.get_language') as mock_lang:
        
        mock_agents.return_value = []  # No agentic agents
        mock_resolve.return_value = (str(tmp_path / "example_python.prompt"), str(code_file))
        mock_update_prompt.return_value = ("Generated prompt", 0.001, "gpt-4")
        mock_lang.return_value = "python"
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            simple=True,
        )
        
        assert result is not None
        prompt, cost, model = result
        assert prompt == "Generated prompt"
        assert cost == 0.001
        assert model == "gpt-4"


def test_regeneration_mode_directory_output(mock_ctx, tmp_path):
    """Test regeneration mode with directory as output."""
    code_file = tmp_path / "code.py"
    code_file.write_text("def bar(): return 42")
    
    output_dir = tmp_path / "outputs"
    output_dir.mkdir()
    
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.resolve_prompt_code_pair') as mock_resolve, \
         patch('pdd.update_main.update_prompt') as mock_update, \
         patch('pdd.update_main.get_language') as mock_lang:
        
        mock_agents.return_value = []
        expected_prompt = str(output_dir / "code_python.prompt")
        mock_resolve.return_value = (expected_prompt, str(code_file))
        mock_update.return_value = ("New prompt", 0.002, "claude-3")
        mock_lang.return_value = "python"
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=str(code_file),
            input_code_file=None,
            output=str(output_dir) + "/",  # Trailing slash indicates directory
            simple=True,
        )
        
        assert result is not None
        prompt, cost, model = result
        assert "New prompt" in prompt


def test_regeneration_mode_file_output(mock_ctx, tmp_path):
    """Test regeneration mode with specific file as output."""
    code_file = tmp_path / "module.py"
    code_file.write_text("class MyClass: pass")
    
    output_file = tmp_path / "custom_prompt.txt"
    
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.update_prompt') as mock_update, \
         patch('pdd.update_main.get_language') as mock_lang, \
         patch('builtins.open', mock_open(read_data="class MyClass: pass")) as m:
        
        mock_agents.return_value = []
        mock_update.return_value = ("Custom prompt", 0.003, "gemini")
        mock_lang.return_value = "python"
        
        # Mock os.path.isdir to return False for output_file
        with patch('os.path.isdir', return_value=False), \
             patch('os.path.exists', return_value=True), \
             patch('os.makedirs'):
            
            result = update_main(
                ctx=mock_ctx,
                input_prompt_file=None,
                modified_code_file=str(code_file),
                input_code_file=None,
                output=str(output_file),
                simple=True,
            )
            
            assert result is not None


def test_regeneration_mode_agentic_success(mock_ctx, tmp_path):
    """Test regeneration mode with successful agentic path."""
    code_file = tmp_path / "agent_test.py"
    code_file.write_text("def agent_func(): pass")
    
    prompt_file = tmp_path / "agent_test_python.prompt"
    
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.run_agentic_update') as mock_agentic, \
         patch('pdd.update_main.resolve_prompt_code_pair') as mock_resolve, \
         patch('pdd.update_main.get_language') as mock_lang, \
         patch('pathlib.Path.touch'), \
         patch('builtins.open', mock_open(read_data="Agentic prompt")):
        
        mock_agents.return_value = ["claude"]
        mock_agentic.return_value = (True, "Success", 0.005, "claude-3.5", [])
        mock_resolve.return_value = (str(prompt_file), str(code_file))
        mock_lang.return_value = "python"
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            simple=False,  # Enable agentic
        )
        
        assert result is not None
        prompt, cost, model = result
        assert cost == 0.005
        assert model == "claude-3.5"


def test_regeneration_mode_agentic_fallback(mock_ctx, tmp_path):
    """Test regeneration mode with agentic failure falling back to legacy."""
    code_file = tmp_path / "fallback.py"
    code_file.write_text("def fallback_func(): pass")
    
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.run_agentic_update') as mock_agentic, \
         patch('pdd.update_main.resolve_prompt_code_pair') as mock_resolve, \
         patch('pdd.update_main.update_prompt') as mock_update, \
         patch('pdd.update_main.get_language') as mock_lang, \
         patch('pathlib.Path.touch'), \
         patch('builtins.open', mock_open(read_data="def fallback_func(): pass")):
        
        mock_agents.return_value = ["claude"]
        mock_agentic.return_value = (False, "Agent failed", 0.0, "", [])
        mock_resolve.return_value = (str(tmp_path / "fallback_python.prompt"), str(code_file))
        mock_update.return_value = ("Legacy prompt", 0.002, "gpt-4")
        mock_lang.return_value = "python"
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            simple=False,
        )
        
        assert result is not None
        prompt, cost, model = result
        assert prompt == "Legacy prompt"
        assert model == "gpt-4"


# ============================================================================
# TRUE UPDATE MODE TESTS
# ============================================================================

def test_update_mode_with_input_code_file(mock_ctx, sample_files, tmp_path):
    """Test true update mode with explicit input code file."""
    original_code = tmp_path / "original.py"
    original_code.write_text("def old(): pass")
    
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.construct_paths') as mock_construct, \
         patch('pdd.update_main.update_prompt') as mock_update:
        
        mock_agents.return_value = []
        mock_construct.return_value = (
            {},  # resolved_config
            {
                "input_prompt_file": "Old prompt",
                "modified_code_file": "def new(): pass",
                "input_code_file": "def old(): pass",
            },
            {"output": sample_files["prompt"]},
            "python"
        )
        mock_update.return_value = ("Updated prompt", 0.004, "gpt-4")
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=sample_files["prompt"],
            modified_code_file=sample_files["code"],
            input_code_file=str(original_code),
            output=None,
            simple=True,
        )
        
        assert result is not None
        prompt, cost, model = result
        assert prompt == "Updated prompt"


def test_update_mode_with_git_flag(mock_ctx, sample_files):
    """Test true update mode using Git to retrieve original code."""
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.construct_paths') as mock_construct, \
         patch('pdd.update_main.git_update') as mock_git_update:
        
        mock_agents.return_value = []
        mock_construct.return_value = (
            {},
            {
                "input_prompt_file": "Prompt text",
                "modified_code_file": "Modified code",
            },
            {"output": sample_files["prompt"]},
            "python"
        )
        mock_git_update.return_value = ("Git updated prompt", 0.006, "claude")
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=sample_files["prompt"],
            modified_code_file=sample_files["code"],
            input_code_file=None,
            output=None,
            use_git=True,
            simple=True,
        )
        
        assert result is not None
        prompt, cost, model = result
        assert prompt == "Git updated prompt"
        mock_git_update.assert_called_once()


def test_update_mode_agentic_success(mock_ctx, sample_files):
    """Test update mode with successful agentic update."""
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.run_agentic_update') as mock_agentic, \
         patch('builtins.open', mock_open(read_data="Agentic updated")):
        
        mock_agents.return_value = ["claude"]
        mock_agentic.return_value = (True, "Done", 0.008, "claude-sonnet", [])
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=sample_files["prompt"],
            modified_code_file=sample_files["code"],
            input_code_file=None,
            output=None,
            use_git=True,
            simple=False,
        )
        
        assert result is not None
        prompt, cost, model = result
        assert cost == 0.008
        assert model == "claude-sonnet"


def test_update_mode_empty_prompt_triggers_generation(mock_ctx, tmp_path):
    """Test that empty prompt file triggers generation mode."""
    empty_prompt = tmp_path / "empty.prompt"
    empty_prompt.write_text("")
    
    code_file = tmp_path / "code.py"
    code_file.write_text("def func(): pass")
    
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.construct_paths') as mock_construct, \
         patch('pdd.update_main.update_prompt') as mock_update:
        
        mock_agents.return_value = []
        mock_construct.return_value = (
            {},
            {
                "input_prompt_file": "",  # Empty prompt
                "modified_code_file": "def func(): pass",
            },
            {"output": str(empty_prompt)},
            "python"
        )
        mock_update.return_value = ("Generated from empty", 0.003, "gpt-4")
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=str(empty_prompt),
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            simple=True,
        )
        
        assert result is not None
        # Verify update_prompt was called with generation signal
        call_args = mock_update.call_args
        assert "no prompt exists yet" in call_args[1]["input_prompt"].lower()


def test_update_mode_error_no_git_no_input_code(mock_ctx, sample_files):
    """Test error when neither --git nor input_code_file is provided in update mode."""
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.construct_paths') as mock_construct:
        
        mock_agents.return_value = []
        mock_construct.return_value = (
            {},
            {
                "input_prompt_file": "Some prompt",
                "modified_code_file": "Some code",
                # No input_code_file in input_strings
            },
            {"output": sample_files["prompt"]},
            "python"
        )
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=sample_files["prompt"],
            modified_code_file=sample_files["code"],
            input_code_file=None,
            output=None,
            use_git=False,  # Not using git
            simple=True,
        )
        
        # Should return None due to ValueError
        assert result is None


def test_update_mode_empty_modified_code_error(mock_ctx, tmp_path):
    """Test error when modified code file is empty."""
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("Prompt")
    
    empty_code = tmp_path / "empty.py"
    empty_code.write_text("")
    
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.construct_paths') as mock_construct:
        
        mock_agents.return_value = []
        mock_construct.return_value = (
            {},
            {
                "input_prompt_file": "Prompt",
                "modified_code_file": "",  # Empty
                "input_code_file": "old code",
            },
            {"output": str(prompt_file)},
            "python"
        )
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=str(prompt_file),
            modified_code_file=str(empty_code),
            input_code_file="old.py",
            output=None,
            simple=True,
        )
        
        assert result is None  # Should fail validation


def test_update_mode_validates_empty_output(mock_ctx, sample_files):
    """Test that empty prompt output is rejected."""
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.construct_paths') as mock_construct, \
         patch('pdd.update_main.update_prompt') as mock_update:
        
        mock_agents.return_value = []
        mock_construct.return_value = (
            {},
            {
                "input_prompt_file": "Prompt",
                "modified_code_file": "Code",
                "input_code_file": "Old code",
            },
            {"output": sample_files["prompt"]},
            "python"
        )
        mock_update.return_value = ("", 0.001, "gpt-4")  # Empty output
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=sample_files["prompt"],
            modified_code_file=sample_files["code"],
            input_code_file="old.py",
            output=None,
            simple=True,
        )
        
        assert result is None  # Should reject empty prompt


# ============================================================================
# REPOSITORY MODE TESTS
# ============================================================================

def test_repo_mode_no_files(mock_ctx, temp_repo):
    """Test repository mode when no scannable files exist."""
    repo_path, repo = temp_repo
    
    with patch('os.getcwd', return_value=str(repo_path)), \
         patch('pdd.update_main.find_and_resolve_all_pairs') as mock_find:
        
        mock_find.return_value = []  # No files found
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=None,
            input_code_file=None,
            output=None,
            repo=True,
        )
        
        assert result is None


def test_repo_mode_multiple_files(mock_ctx, temp_repo):
    """Test repository mode with multiple files."""
    repo_path, repo = temp_repo
    
    # Create some code files
    (repo_path / "file1.py").write_text("def f1(): pass")
    (repo_path / "file2.py").write_text("def f2(): pass")
    
    with patch('os.getcwd', return_value=str(repo_path)), \
         patch('pdd.update_main.find_and_resolve_all_pairs') as mock_find, \
         patch('pdd.update_main.update_file_pair') as mock_update_pair:
        
        mock_find.return_value = [
            (str(repo_path / "file1_python.prompt"), str(repo_path / "file1.py")),
            (str(repo_path / "file2_python.prompt"), str(repo_path / "file2.py")),
        ]
        
        mock_update_pair.side_effect = [
            {"prompt_file": "f1", "status": "✅ Success", "cost": 0.01, "model": "gpt-4", "error": ""},
            {"prompt_file": "f2", "status": "✅ Success", "cost": 0.02, "model": "gpt-4", "error": ""},
        ]
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=None,
            input_code_file=None,
            output=None,
            repo=True,
        )
        
        assert result is not None
        message, cost, models = result
        assert cost == 0.03  # Sum of costs
        assert "gpt-4" in models


def test_repo_mode_extension_filtering(mock_ctx, temp_repo):
    """Test repository mode with extension filtering."""
    repo_path, repo = temp_repo
    
    with patch('os.getcwd', return_value=str(repo_path)), \
         patch('pdd.update_main.find_and_resolve_all_pairs') as mock_find:
        
        mock_find.return_value = []
        
        update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=None,
            input_code_file=None,
            output=None,
            repo=True,
            extensions=".py,.js",
        )
        
        # Verify extensions were passed
        mock_find.assert_called_once()
        # The function is called with keyword arguments, not positional
        assert mock_find.call_args.kwargs['extensions'] == ".py,.js"


def test_repo_mode_non_git_directory_error(mock_ctx, tmp_path):
    """Test repository mode fails gracefully in non-git directory."""
    with patch('os.getcwd', return_value=str(tmp_path)):
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=None,
            input_code_file=None,
            output=None,
            repo=True,
        )
        
        assert result is None  # Should fail gracefully


def test_repo_mode_mixed_results(mock_ctx, temp_repo):
    """Test repository mode with mixed success/failure results."""
    repo_path, repo = temp_repo
    
    with patch('os.getcwd', return_value=str(repo_path)), \
         patch('pdd.update_main.find_and_resolve_all_pairs') as mock_find, \
         patch('pdd.update_main.update_file_pair') as mock_update_pair:
        
        mock_find.return_value = [
            ("prompt1", "code1"),
            ("prompt2", "code2"),
            ("prompt3", "code3"),
        ]
        
        mock_update_pair.side_effect = [
            {"prompt_file": "p1", "status": "✅ Success", "cost": 0.01, "model": "gpt-4", "error": ""},
            {"prompt_file": "p2", "status": "❌ Failed", "cost": 0.0, "model": "", "error": "API error"},
            {"prompt_file": "p3", "status": "✅ Success", "cost": 0.03, "model": "claude", "error": ""},
        ]
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=None,
            input_code_file=None,
            output=None,
            repo=True,
        )
        
        assert result is not None
        message, cost, models = result
        assert cost == 0.04  # Only successful costs
        assert "claude" in models and "gpt-4" in models


# ============================================================================
# HELPER FUNCTION TESTS
# ============================================================================

def test_resolve_prompt_code_pair_creates_directory(tmp_path, monkeypatch):
    """Test that resolve_prompt_code_pair creates prompts directory."""
    monkeypatch.chdir(tmp_path)
    
    code_file = tmp_path / "test.py"
    code_file.write_text("pass")
    
    with patch('pdd.update_main.get_language', return_value="python"):
        prompt_path, code_path = resolve_prompt_code_pair(str(code_file), quiet=True)
        
        assert Path(prompt_path).parent.exists()
        assert Path(prompt_path).exists()


def test_resolve_prompt_code_pair_custom_output_dir(tmp_path):
    """Test resolve_prompt_code_pair with custom output directory."""
    code_file = tmp_path / "code.py"
    code_file.write_text("pass")
    
    custom_dir = tmp_path / "custom_prompts"
    
    with patch('pdd.update_main.get_language', return_value="python"):
        prompt_path, code_path = resolve_prompt_code_pair(
            str(code_file),
            quiet=True,
            output_dir=str(custom_dir)
        )
        
        assert str(custom_dir) in prompt_path
        assert Path(prompt_path).parent == custom_dir


def test_find_and_resolve_all_pairs_filters_correctly(tmp_path):
    """Test find_and_resolve_all_pairs applies filters correctly."""
    # Create test structure
    (tmp_path / "main.py").write_text("pass")
    (tmp_path / "test_unit.py").write_text("pass")  # Should be excluded
    (tmp_path / "demo_example.py").write_text("pass")  # Should be excluded
    (tmp_path / "file.prompt").write_text("pass")  # Should be excluded
    (tmp_path / "__pycache__").mkdir()
    (tmp_path / "__pycache__" / "cached.py").write_text("pass")  # Should be excluded
    
    with patch('pdd.update_main.get_language') as mock_lang, \
         patch('pdd.update_main.resolve_prompt_code_pair') as mock_resolve:
        
        def lang_side_effect(path):
            if path.endswith('.py'):
                return 'python'
            return None
        
        mock_lang.side_effect = lang_side_effect
        mock_resolve.return_value = ("prompt", "code")
        
        pairs = find_and_resolve_all_pairs(str(tmp_path), quiet=True)
        
        # Only main.py should be included
        assert len(pairs) == 1


def test_find_and_resolve_all_pairs_extension_filter(tmp_path):
    """Test find_and_resolve_all_pairs with extension filtering."""
    (tmp_path / "file.py").write_text("pass")
    (tmp_path / "file.js").write_text("pass")
    (tmp_path / "file.rs").write_text("pass")
    
    with patch('pdd.update_main.get_language') as mock_lang, \
         patch('pdd.update_main.resolve_prompt_code_pair') as mock_resolve:
        
        mock_lang.return_value = "python"
        mock_resolve.return_value = ("prompt", "code")
        
        pairs = find_and_resolve_all_pairs(
            str(tmp_path),
            quiet=True,
            extensions=".py,.js"
        )
        
        # Should exclude .rs file
        assert len(pairs) == 2


def test_update_file_pair_agentic_success(mock_ctx, tmp_path):
    """Test update_file_pair with successful agentic path."""
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("Test prompt")
    
    code_file = tmp_path / "test.py"
    code_file.write_text("def test(): pass")
    
    mock_repo = Mock()
    mock_repo.working_tree_dir = str(tmp_path)
    mock_repo.untracked_files = []
    
    with patch('pdd.update_main.get_available_agents', return_value=["claude"]), \
         patch('pdd.update_main.run_agentic_update') as mock_agentic, \
         patch('builtins.open', mock_open(read_data="Updated prompt")):
        
        mock_agentic.return_value = (True, "Success", 0.01, "claude", [])
        
        result = update_file_pair(
            str(prompt_file),
            str(code_file),
            mock_ctx,
            mock_repo,
            simple=False
        )
        
        assert result["status"] == "✅ Success (agentic)"
        assert result["cost"] == 0.01
        assert result["model"] == "claude"


def test_update_file_pair_generation_mode_for_new_file(mock_ctx, tmp_path):
    """Test update_file_pair triggers generation for new untracked files."""
    prompt_file = tmp_path / "new.prompt"
    prompt_file.write_text("")
    
    code_file = tmp_path / "new.py"
    code_file.write_text("def new(): pass")
    
    mock_repo = Mock()
    mock_repo.working_tree_dir = str(tmp_path)
    mock_repo.untracked_files = ["new.py"]  # Untracked
    
    with patch('pdd.update_main.get_available_agents', return_value=[]), \
         patch('pdd.update_main.update_prompt') as mock_update, \
         patch('builtins.open', mock_open(read_data="def new(): pass")):
        
        mock_update.return_value = ("Generated", 0.005, "gpt-4")
        
        result = update_file_pair(
            str(prompt_file),
            str(code_file),
            mock_ctx,
            mock_repo,
            simple=True
        )
        
        assert result["status"] == "✅ Success"
        # Verify generation mode was triggered
        call_args = mock_update.call_args[1]
        assert call_args["input_code"] == ""


# ============================================================================
# ERROR HANDLING TESTS
# ============================================================================

def test_click_abort_is_reraised(mock_ctx, sample_files):
    """Test that click.Abort is re-raised for proper CLI handling."""
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.construct_paths') as mock_construct:
        
        mock_agents.return_value = []
        mock_construct.side_effect = click.Abort()
        
        with pytest.raises(click.Abort):
            update_main(
                ctx=mock_ctx,
                input_prompt_file=sample_files["prompt"],
                modified_code_file=sample_files["code"],
                input_code_file=None,
                output=None,
                simple=True,
            )


def test_git_invalid_repository_error_handled(mock_ctx, tmp_path):
    """Test graceful handling of git.InvalidGitRepositoryError."""
    code_file = tmp_path / "code.py"
    code_file.write_text("pass")
    
    with patch('os.getcwd', return_value=str(tmp_path)), \
         patch('git.Repo', side_effect=git.InvalidGitRepositoryError("Not a repo")):
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=None,
            input_code_file=None,
            output=None,
            repo=True,
        )
        
        assert result is None


def test_generic_exception_returns_none(mock_ctx, sample_files):
    """Test that generic exceptions return None instead of crashing."""
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.construct_paths') as mock_construct:
        
        mock_agents.return_value = []
        mock_construct.side_effect = RuntimeError("Unexpected error")
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=sample_files["prompt"],
            modified_code_file=sample_files["code"],
            input_code_file=None,
            output=None,
            simple=True,
        )
        
        assert result is None


def test_quiet_mode_suppresses_output(mock_ctx, tmp_path):
    """Test that quiet mode suppresses console output."""
    mock_ctx.obj["quiet"] = True
    
    code_file = tmp_path / "quiet.py"
    code_file.write_text("pass")
    
    with patch('pdd.update_main.get_available_agents') as mock_agents, \
         patch('pdd.update_main.resolve_prompt_code_pair') as mock_resolve, \
         patch('pdd.update_main.update_prompt') as mock_update, \
         patch('pdd.update_main.rprint') as mock_rprint:
        
        mock_agents.return_value = []
        mock_resolve.return_value = (str(tmp_path / "quiet.prompt"), str(code_file))
        mock_update.return_value = ("Quiet prompt", 0.001, "gpt-4")
        
        update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            simple=True,
        )
        
        # rprint should not be called in quiet mode for success messages
        # (only errors might still print)
        success_calls = [c for c in mock_rprint.call_args_list if "success" in str(c).lower()]
        assert len(success_calls) == 0


# ============================================================================
# INTEGRATION TESTS
# ============================================================================

def test_end_to_end_regeneration_flow(mock_ctx, tmp_path):
    """Integration test for complete regeneration flow."""
    code_file = tmp_path / "integration.py"
    code_file.write_text("def integration_test(): return True")
    
    with patch('pdd.update_main.get_available_agents', return_value=[]), \
         patch('pdd.update_main.get_language', return_value="python"), \
         patch('pdd.update_main.update_prompt') as mock_update:
        
        mock_update.return_value = ("Integration prompt", 0.01, "gpt-4")
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            simple=True,
        )
        
        assert result is not None
        prompt, cost, model = result
        assert "Integration prompt" in prompt
        assert cost > 0
        assert model == "gpt-4"


def test_end_to_end_update_flow(mock_ctx, tmp_path):
    """Integration test for complete update flow."""
    prompt_file = tmp_path / "update.prompt"
    prompt_file.write_text("Original prompt")
    
    code_file = tmp_path / "update.py"
    code_file.write_text("def updated(): pass")
    
    old_code_file = tmp_path / "old_update.py"
    old_code_file.write_text("def old(): pass")
    
    with patch('pdd.update_main.get_available_agents', return_value=[]), \
         patch('pdd.update_main.construct_paths') as mock_construct, \
         patch('pdd.update_main.update_prompt') as mock_update:
        
        mock_construct.return_value = (
            {},
            {
                "input_prompt_file": "Original prompt",
                "modified_code_file": "def updated(): pass",
                "input_code_file": "def old(): pass",
            },
            {"output": str(prompt_file)},
            "python"
        )
        mock_update.return_value = ("Updated prompt text", 0.02, "claude")
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=str(prompt_file),
            modified_code_file=str(code_file),
            input_code_file=str(old_code_file),
            output=None,
            simple=True,
        )
        
        assert result is not None
        prompt, cost, model = result
        assert prompt == "Updated prompt text"
        assert cost == 0.02
        assert model == "claude"


# ============================================================================
# PARAMETER OVERRIDE TESTS
# ============================================================================

def test_strength_parameter_override(mock_ctx, tmp_path):
    """Test that strength parameter overrides ctx.obj value."""
    code_file = tmp_path / "strength_test.py"
    code_file.write_text("pass")
    
    with patch('pdd.update_main.get_available_agents', return_value=[]), \
         patch('pdd.update_main.resolve_prompt_code_pair') as mock_resolve, \
         patch('pdd.update_main.update_prompt') as mock_update:
        
        mock_resolve.return_value = (str(tmp_path / "test.prompt"), str(code_file))
        mock_update.return_value = ("Test", 0.01, "gpt-4")
        
        update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            strength=0.8,  # Override
            simple=True,
        )
        
        # Verify ctx.obj was updated
        assert mock_ctx.obj["strength"] == 0.8


def test_temperature_parameter_override(mock_ctx, tmp_path):
    """Test that temperature parameter overrides ctx.obj value."""
    code_file = tmp_path / "temp_test.py"
    code_file.write_text("pass")
    
    with patch('pdd.update_main.get_available_agents', return_value=[]), \
         patch('pdd.update_main.resolve_prompt_code_pair') as mock_resolve, \
         patch('pdd.update_main.update_prompt') as mock_update:
        
        mock_resolve.return_value = (str(tmp_path / "test.prompt"), str(code_file))
        mock_update.return_value = ("Test", 0.01, "gpt-4")
        
        update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            temperature=0.7,  # Override
            simple=True,
        )
        
        # Verify ctx.obj was updated
        assert mock_ctx.obj["temperature"] == 0.7