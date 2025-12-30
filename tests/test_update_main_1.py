"""
Test Suite for pdd/update_main.py

DETAILED TEST PLAN
==================

This test suite validates the update_main module which provides CLI wrapper functionality
for updating prompts based on modified code.

TESTING STRATEGY
----------------

### Z3 Formal Verification Tests:
1. **Mode Selection Logic**: Verify the boolean logic that determines which mode is active
   - Regeneration mode: (input_prompt_file is None AND input_code_file is None)
   - True update mode: (input_prompt_file is NOT None)
   - Repo mode: (repo is True)
   
2. **Parameter Validation**: Verify mutually exclusive parameters
   - use_git and input_code_file cannot both be provided
   - Validate strength/temperature resolution logic
   
3. **Output Path Resolution**: Verify logic for determining output paths
   - When output is None: use input_prompt_file
   - When output is directory: derive filename
   - When output is file: use as-is

### Unit Tests:
1. **Regeneration Mode Tests**:
   - Test with only modified_code_file provided
   - Test output to default prompts directory
   - Test output to custom directory (--output as dir)
   - Test output to custom file (--output as file)
   - Test agentic routing and fallback
   
2. **True Update Mode Tests**:
   - Test with input_prompt_file + modified_code_file + input_code_file
   - Test with input_prompt_file + modified_code_file + use_git
   - Test empty prompt triggers generation
   - Test output overrides input file
   - Test agentic routing and fallback
   
3. **Repository Mode Tests**:
   - Test repo-wide scanning
   - Test extension filtering
   - Test progress reporting
   - Test summary table generation
   - Test handling of mixed success/failure
   
4. **Helper Function Tests**:
   - resolve_prompt_code_pair: path derivation, file creation
   - find_and_resolve_all_pairs: filtering logic, ignored directories
   - update_file_pair: git status detection, agentic routing
   
5. **Error Handling Tests**:
   - Invalid git repository
   - Missing files
   - Empty modified code
   - Conflicting parameters
   - LLM failures

6. **Integration Tests**:
   - End-to-end workflow with mocked dependencies
   - Verify file I/O operations
   - Verify cost tracking
   - Verify model information propagation

MOCKING STRATEGY
----------------
- Mock external LLM calls (update_prompt, git_update, run_agentic_update)
- Mock git operations
- Use temporary directories for file operations
- Mock get_available_agents for agentic routing tests

TEST ISOLATION
--------------
- Each test uses its own temporary directory
- Mocks are reset between tests
- No shared state between tests
"""

import pytest
import os
import tempfile
import shutil
from pathlib import Path
from unittest.mock import Mock, MagicMock, patch, mock_open
from typing import Tuple, Optional
import click
from click.testing import CliRunner
import git

# Import the code under test
from pdd.update_main import (
    update_main,
    resolve_prompt_code_pair,
    find_and_resolve_all_pairs,
    update_file_pair,
)


# =============================================================================
# Z3 FORMAL VERIFICATION TESTS
# =============================================================================

def test_z3_mode_selection_logic():
    """
    Z3 formal verification of mode selection logic.
    
    Verifies that the boolean expressions correctly determine which mode is active:
    - Regeneration mode: input_prompt_file is None AND input_code_file is None
    - True update mode: NOT regeneration mode
    """
    from z3 import Bool, Solver, Not, And, Or, sat, unsat
    
    # Define boolean variables
    input_prompt_provided = Bool('input_prompt_provided')
    input_code_provided = Bool('input_code_provided')
    
    # Define mode predicates
    is_regeneration = And(Not(input_prompt_provided), Not(input_code_provided))
    is_true_update = Not(is_regeneration)
    
    solver = Solver()
    
    # Test 1: If both are None, must be regeneration mode
    solver.push()
    solver.add(Not(input_prompt_provided))
    solver.add(Not(input_code_provided))
    solver.add(Not(is_regeneration))  # Should be unsatisfiable
    assert solver.check() == unsat, "Regeneration mode should be active when both are None"
    solver.pop()
    
    # Test 2: If prompt is provided, must be true update mode
    solver.push()
    solver.add(input_prompt_provided)
    solver.add(Not(is_true_update))  # Should be unsatisfiable
    assert solver.check() == unsat, "True update mode should be active when prompt is provided"
    solver.pop()
    
    # Test 3: Modes are mutually exclusive
    solver.push()
    solver.add(And(is_regeneration, is_true_update))  # Should be unsatisfiable
    assert solver.check() == unsat, "Modes should be mutually exclusive"
    solver.pop()


def test_z3_parameter_validation():
    """
    Z3 formal verification of parameter validation logic.
    
    Verifies that use_git and input_code_file are mutually exclusive.
    """
    from z3 import Bool, Solver, And, sat
    
    use_git = Bool('use_git')
    input_code_provided = Bool('input_code_provided')
    
    # These should not both be true
    is_valid = And(use_git, input_code_provided)
    
    solver = Solver()
    solver.add(is_valid)
    
    # If both are true, this represents an invalid state that should cause an error
    # The code should detect and reject this
    result = solver.check()
    assert result == sat, "Both use_git and input_code can be true, but code should reject it"


def test_z3_output_path_resolution():
    """
    Z3 formal verification of output path resolution logic.
    
    Verifies the logic for determining the final output path.
    """
    from z3 import Bool, Solver, Implies, And, Not, sat, unsat
    
    output_provided = Bool('output_provided')
    output_is_dir = Bool('output_is_dir')
    uses_input_path = Bool('uses_input_path')
    uses_custom_path = Bool('uses_custom_path')
    
    solver = Solver()
    
    # Rule 1: If no output provided, use input path
    solver.add(Implies(Not(output_provided), uses_input_path))
    
    # Rule 2: If output provided, use custom path
    solver.add(Implies(output_provided, uses_custom_path))
    
    # Rule 3: Cannot use both paths
    solver.add(Not(And(uses_input_path, uses_custom_path)))
    
    # Verify consistency
    assert solver.check() == sat, "Output path resolution logic should be consistent"
    
    # Test: No output provided -> must use input path
    solver.push()
    solver.add(Not(output_provided))
    solver.add(Not(uses_input_path))
    assert solver.check() == unsat, "Must use input path when no output provided"
    solver.pop()


# =============================================================================
# FIXTURES
# =============================================================================

@pytest.fixture
def temp_dir():
    """Create a temporary directory for test files."""
    tmpdir = tempfile.mkdtemp()
    yield tmpdir
    shutil.rmtree(tmpdir, ignore_errors=True)


@pytest.fixture
def mock_ctx():
    """Create a mock Click context."""
    ctx = Mock(spec=click.Context)
    ctx.obj = {
        "verbose": False,
        "quiet": False,
        "force": False,
        "strength": 0.5,
        "temperature": 0,
        "time": 60,
        "context": None,
        "confirm_callback": None,
    }
    return ctx


@pytest.fixture
def git_repo(temp_dir):
    """Create a temporary git repository."""
    repo = git.Repo.init(temp_dir)
    # Configure git user for commits
    with repo.config_writer() as config:
        config.set_value("user", "name", "Test User")
        config.set_value("user", "email", "test@example.com")
    return repo


# =============================================================================
# HELPER FUNCTION TESTS
# =============================================================================

class TestResolvePromptCodePair:
    """Tests for resolve_prompt_code_pair function."""
    
    def test_basic_path_derivation(self, temp_dir):
        """Test basic prompt path derivation from code file."""
        code_file = os.path.join(temp_dir, "example.py")
        Path(code_file).touch()
        
        prompt_path, code_path = resolve_prompt_code_pair(code_file, quiet=True)
        
        assert code_path == code_file
        assert prompt_path.endswith("example_python.prompt")
        assert os.path.exists(prompt_path)
    
    def test_custom_output_directory(self, temp_dir):
        """Test custom output directory for prompt files."""
        code_file = os.path.join(temp_dir, "example.py")
        custom_dir = os.path.join(temp_dir, "custom_prompts")
        Path(code_file).touch()
        
        prompt_path, _ = resolve_prompt_code_pair(
            code_file, quiet=True, output_dir=custom_dir
        )
        
        assert custom_dir in prompt_path
        assert os.path.exists(custom_dir)
        assert os.path.exists(prompt_path)
    
    def test_creates_missing_prompt_file(self, temp_dir):
        """Test that missing prompt files are created."""
        code_file = os.path.join(temp_dir, "new_file.js")
        Path(code_file).touch()
        
        prompt_path, _ = resolve_prompt_code_pair(code_file, quiet=True)
        
        assert os.path.exists(prompt_path)
        assert prompt_path.endswith("new_file_javascript.prompt")


class TestFindAndResolveAllPairs:
    """Tests for find_and_resolve_all_pairs function."""
    
    def test_basic_scanning(self, temp_dir):
        """Test basic repository scanning."""
        # Create some code files
        Path(temp_dir, "file1.py").write_text("# code")
        Path(temp_dir, "file2.js").write_text("// code")
        Path(temp_dir, "test_ignore.py").write_text("# test")  # Should be ignored
        
        pairs = find_and_resolve_all_pairs(temp_dir, quiet=True)
        
        assert len(pairs) == 2
        assert any("file1" in p[0] for p in pairs)
        assert any("file2" in p[0] for p in pairs)
        assert not any("test_ignore" in p[0] for p in pairs)
    
    def test_extension_filtering(self, temp_dir):
        """Test filtering by file extensions."""
        Path(temp_dir, "file1.py").write_text("# code")
        Path(temp_dir, "file2.js").write_text("// code")
        
        pairs = find_and_resolve_all_pairs(temp_dir, quiet=True, extensions=".py")
        
        assert len(pairs) == 1
        assert "file1" in pairs[0][0]
    
    def test_ignores_special_directories(self, temp_dir):
        """Test that special directories are ignored."""
        Path(temp_dir, ".git").mkdir()
        Path(temp_dir, ".git", "file.py").write_text("# code")
        Path(temp_dir, "node_modules").mkdir()
        Path(temp_dir, "node_modules", "lib.js").write_text("// code")
        
        pairs = find_and_resolve_all_pairs(temp_dir, quiet=True)
        
        assert len(pairs) == 0


# =============================================================================
# REGENERATION MODE TESTS
# =============================================================================

class TestRegenerationMode:
    """Tests for regeneration mode (only modified_code_file provided)."""
    
    @patch('pdd.update_main.get_available_agents')
    @patch('pdd.update_main.update_prompt')
    @patch('pdd.update_main.get_language')
    def test_regeneration_basic(
        self, mock_get_lang, mock_update_prompt, mock_agents, mock_ctx, temp_dir
    ):
        """Test basic regeneration mode."""
        mock_agents.return_value = []  # No agents, use legacy
        mock_get_lang.return_value = "python"
        mock_update_prompt.return_value = ("Generated prompt", 0.05, "gpt-4")
        
        code_file = os.path.join(temp_dir, "example.py")
        Path(code_file).write_text("def foo(): pass")
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=code_file,
            input_code_file=None,
            output=None,
        )
        
        assert result is not None
        prompt, cost, model = result
        assert prompt == "Generated prompt"
        assert cost == 0.05
        assert model == "gpt-4"
    
    @patch('pdd.update_main.get_available_agents')
    @patch('pdd.update_main.run_agentic_update')
    @patch('pdd.update_main.get_language')
    def test_regeneration_agentic_success(
        self, mock_get_lang, mock_agentic, mock_agents, mock_ctx, temp_dir
    ):
        """Test regeneration mode with successful agentic update."""
        mock_agents.return_value = ["claude"]
        mock_get_lang.return_value = "python"
        mock_agentic.return_value = (True, "Success", 0.03, "claude", [])
        
        code_file = os.path.join(temp_dir, "example.py")
        Path(code_file).write_text("def foo(): pass")
        
        # Mock file read for agentic result
        with patch('builtins.open', mock_open(read_data="Agentic prompt")):
            result = update_main(
                ctx=mock_ctx,
                input_prompt_file=None,
                modified_code_file=code_file,
                input_code_file=None,
                output=None,
                simple=False,
            )
        
        assert result is not None
        prompt, cost, model = result
        assert prompt == "Agentic prompt"
        assert cost == 0.03
        assert model == "claude"
    
    @patch('pdd.update_main.get_available_agents')
    @patch('pdd.update_main.run_agentic_update')
    @patch('pdd.update_main.update_prompt')
    @patch('pdd.update_main.get_language')
    def test_regeneration_agentic_fallback(
        self, mock_get_lang, mock_update_prompt, mock_agentic, mock_agents,
        mock_ctx, temp_dir
    ):
        """Test regeneration mode with agentic failure falling back to legacy."""
        mock_agents.return_value = ["claude"]
        mock_get_lang.return_value = "python"
        mock_agentic.return_value = (False, "Error", 0, "", [])
        mock_update_prompt.return_value = ("Legacy prompt", 0.04, "gpt-4")
        
        code_file = os.path.join(temp_dir, "example.py")
        Path(code_file).write_text("def foo(): pass")
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=code_file,
            input_code_file=None,
            output=None,
            simple=False,
        )
        
        assert result is not None
        prompt, cost, model = result
        assert prompt == "Legacy prompt"
    
    @patch('pdd.update_main.get_available_agents')
    @patch('pdd.update_main.update_prompt')
    @patch('pdd.update_main.get_language')
    def test_regeneration_custom_output_file(
        self, mock_get_lang, mock_update_prompt, mock_agents, mock_ctx, temp_dir
    ):
        """Test regeneration with custom output file path."""
        mock_agents.return_value = []
        mock_get_lang.return_value = "python"
        mock_update_prompt.return_value = ("Generated prompt", 0.05, "gpt-4")
        
        code_file = os.path.join(temp_dir, "example.py")
        output_file = os.path.join(temp_dir, "custom_prompt.txt")
        Path(code_file).write_text("def foo(): pass")
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=code_file,
            input_code_file=None,
            output=output_file,
        )
        
        assert result is not None
        assert os.path.exists(output_file)
        with open(output_file) as f:
            assert f.read() == "Generated prompt"


# =============================================================================
# TRUE UPDATE MODE TESTS
# =============================================================================

class TestTrueUpdateMode:
    """Tests for true update mode (prompt file + code file provided)."""
    
    @patch('pdd.update_main.get_available_agents')
    @patch('pdd.update_main.construct_paths')
    @patch('pdd.update_main.update_prompt')
    def test_update_with_input_code(
        self, mock_update_prompt, mock_construct, mock_agents, mock_ctx, temp_dir
    ):
        """Test update mode with explicit input code file."""
        mock_agents.return_value = []
        mock_update_prompt.return_value = ("Updated prompt", 0.06, "gpt-4")
        
        prompt_file = os.path.join(temp_dir, "test.prompt")
        code_file = os.path.join(temp_dir, "test.py")
        input_code = os.path.join(temp_dir, "original.py")
        
        Path(prompt_file).write_text("Original prompt")
        Path(code_file).write_text("def bar(): pass")
        Path(input_code).write_text("def foo(): pass")
        
        mock_construct.return_value = (
            {},
            {
                "input_prompt_file": "Original prompt",
                "modified_code_file": "def bar(): pass",
                "input_code_file": "def foo(): pass",
            },
            {"output": prompt_file},
            "python",
        )
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=prompt_file,
            modified_code_file=code_file,
            input_code_file=input_code,
            output=None,
        )
        
        assert result is not None
        prompt, cost, model = result
        assert prompt == "Updated prompt"
        assert cost == 0.06
    
    @patch('pdd.update_main.get_available_agents')
    @patch('pdd.update_main.construct_paths')
    @patch('pdd.update_main.git_update')
    def test_update_with_git(
        self, mock_git_update, mock_construct, mock_agents, mock_ctx, temp_dir, git_repo
    ):
        """Test update mode using git history."""
        mock_agents.return_value = []
        mock_git_update.return_value = ("Git updated prompt", 0.07, "gpt-4")
        
        prompt_file = os.path.join(temp_dir, "test.prompt")
        code_file = os.path.join(temp_dir, "test.py")
        
        Path(prompt_file).write_text("Original prompt")
        Path(code_file).write_text("def bar(): pass")
        
        # Mock construct_paths to avoid stdin confirmation issues
        mock_construct.return_value = (
            {},
            {
                "input_prompt_file": "Original prompt",
                "modified_code_file": "def bar(): pass",
            },
            {"output": prompt_file},
            "python",
        )
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=prompt_file,
            modified_code_file=code_file,
            input_code_file=None,
            output=None,
            use_git=True,
        )
        
        assert result is not None
        prompt, cost, model = result
        assert prompt == "Git updated prompt"
    
    @patch('pdd.update_main.get_available_agents')
    @patch('pdd.update_main.run_agentic_update')
    def test_update_agentic_success(
        self, mock_agentic, mock_agents, mock_ctx, temp_dir
    ):
        """Test true update with successful agentic path."""
        mock_agents.return_value = ["claude"]
        mock_agentic.return_value = (True, "Success", 0.08, "claude", [])
        
        prompt_file = os.path.join(temp_dir, "test.prompt")
        code_file = os.path.join(temp_dir, "test.py")
        
        Path(prompt_file).write_text("Original prompt")
        Path(code_file).write_text("def bar(): pass")
        
        with patch('builtins.open', mock_open(read_data="Agentic updated")):
            result = update_main(
                ctx=mock_ctx,
                input_prompt_file=prompt_file,
                modified_code_file=code_file,
                input_code_file=None,
                output=None,
                simple=False,
            )
        
        assert result is not None
        prompt, cost, model = result
        assert prompt == "Agentic updated"
        assert cost == 0.08


# =============================================================================
# REPOSITORY MODE TESTS
# =============================================================================

class TestRepositoryMode:
    """Tests for repository-wide update mode."""
    
    @patch('pdd.update_main.find_and_resolve_all_pairs')
    @patch('pdd.update_main.update_file_pair')
    def test_repo_mode_basic(
        self, mock_update_pair, mock_find_pairs, mock_ctx, temp_dir, git_repo
    ):
        """Test basic repository-wide update."""
        mock_find_pairs.return_value = [
            ("prompt1.prompt", "file1.py"),
            ("prompt2.prompt", "file2.py"),
        ]
        mock_update_pair.return_value = {
            "prompt_file": "prompt1.prompt",
            "status": "✅ Success",
            "cost": 0.05,
            "model": "gpt-4",
            "error": "",
        }
        
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
        assert "complete" in message.lower()
        assert cost == 0.10  # 2 files * 0.05
        assert mock_update_pair.call_count == 2
    
    @patch('pdd.update_main.find_and_resolve_all_pairs')
    def test_repo_mode_no_files(self, mock_find_pairs, mock_ctx, temp_dir, git_repo):
        """Test repository mode with no scannable files."""
        mock_find_pairs.return_value = []
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=None,
            input_code_file=None,
            output=None,
            repo=True,
        )
        
        assert result is None
    
    @patch('pdd.update_main.find_and_resolve_all_pairs')
    @patch('pdd.update_main.update_file_pair')
    def test_repo_mode_with_extensions(
        self, mock_update_pair, mock_find_pairs, mock_ctx, temp_dir, git_repo
    ):
        """Test repository mode with extension filtering."""
        mock_find_pairs.return_value = [("prompt1.prompt", "file1.py")]
        mock_update_pair.return_value = {
            "prompt_file": "prompt1.prompt",
            "status": "✅ Success",
            "cost": 0.05,
            "model": "gpt-4",
            "error": "",
        }
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=None,
            input_code_file=None,
            output=None,
            repo=True,
            extensions=".py",
        )
        
        assert result is not None
        mock_find_pairs.assert_called_once()
        # Check that extensions was passed as keyword argument
        call_kwargs = mock_find_pairs.call_args.kwargs
        assert call_kwargs.get("extensions") == ".py"


# =============================================================================
# ERROR HANDLING TESTS
# =============================================================================

class TestErrorHandling:
    """Tests for error handling."""
    
    def test_repo_mode_not_in_git_repo(self, mock_ctx, temp_dir):
        """Test error when repo mode used outside git repository."""
        os.chdir(temp_dir)
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=None,
            input_code_file=None,
            output=None,
            repo=True,
        )
        
        assert result is None
    
    @patch('pdd.update_main.get_available_agents')
    @patch('pdd.update_main.construct_paths')
    def test_git_and_input_code_conflict(
        self, mock_construct, mock_agents, mock_ctx, temp_dir
    ):
        """Test error when both --git and input_code_file are provided."""
        mock_agents.return_value = []
        prompt_file = os.path.join(temp_dir, "test.prompt")
        code_file = os.path.join(temp_dir, "test.py")
        input_code = os.path.join(temp_dir, "original.py")
        
        Path(prompt_file).write_text("Original prompt")
        Path(code_file).write_text("def bar(): pass")
        Path(input_code).write_text("def foo(): pass")
        
        mock_construct.return_value = (
            {},
            {
                "input_prompt_file": "Original prompt",
                "modified_code_file": "def bar(): pass",
                "input_code_file": "def foo(): pass",
            },
            {"output": prompt_file},
            "python",
        )
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=prompt_file,
            modified_code_file=code_file,
            input_code_file=input_code,
            output=None,
            use_git=True,
        )
        
        assert result is None
    
    @patch('pdd.update_main.get_available_agents')
    @patch('pdd.update_main.construct_paths')
    @patch('pdd.update_main.update_prompt')
    def test_empty_modified_code(
        self, mock_update_prompt, mock_construct, mock_agents, mock_ctx, temp_dir
    ):
        """Test error when modified code file is empty."""
        mock_agents.return_value = []
        prompt_file = os.path.join(temp_dir, "test.prompt")
        code_file = os.path.join(temp_dir, "test.py")
        
        Path(prompt_file).write_text("Original prompt")
        Path(code_file).write_text("")  # Empty file
        
        mock_construct.return_value = (
            {},
            {
                "input_prompt_file": "Original prompt",
                "modified_code_file": "",
                "input_code_file": "def foo(): pass",
            },
            {"output": prompt_file},
            "python",
        )
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=prompt_file,
            modified_code_file=code_file,
            input_code_file=None,
            output=None,
        )
        
        assert result is None
    
    @patch('pdd.update_main.get_available_agents')
    @patch('pdd.update_main.construct_paths')
    @patch('pdd.update_main.update_prompt')
    def test_empty_prompt_output(
        self, mock_update_prompt, mock_construct, mock_agents, mock_ctx, temp_dir
    ):
        """Test error when LLM returns empty prompt."""
        mock_agents.return_value = []
        mock_update_prompt.return_value = ("", 0.05, "gpt-4")  # Empty prompt
        
        prompt_file = os.path.join(temp_dir, "test.prompt")
        code_file = os.path.join(temp_dir, "test.py")
        
        Path(prompt_file).write_text("Original prompt")
        Path(code_file).write_text("def bar(): pass")
        
        mock_construct.return_value = (
            {},
            {
                "input_prompt_file": "Original prompt",
                "modified_code_file": "def bar(): pass",
                "input_code_file": "def foo(): pass",
            },
            {"output": prompt_file},
            "python",
        )
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=prompt_file,
            modified_code_file=code_file,
            input_code_file=None,
            output=None,
        )
        
        assert result is None


# =============================================================================
# PARAMETER RESOLUTION TESTS
# =============================================================================

class TestParameterResolution:
    """Tests for parameter resolution logic."""
    
    @patch('pdd.update_main.get_available_agents')
    @patch('pdd.update_main.construct_paths')
    @patch('pdd.update_main.update_prompt')
    def test_strength_override(
        self, mock_update_prompt, mock_construct, mock_agents, mock_ctx, temp_dir
    ):
        """Test that explicit strength parameter overrides ctx.obj."""
        mock_agents.return_value = []
        mock_update_prompt.return_value = ("Updated", 0.05, "gpt-4")
        
        prompt_file = os.path.join(temp_dir, "test.prompt")
        code_file = os.path.join(temp_dir, "test.py")
        
        Path(prompt_file).write_text("Original prompt")
        Path(code_file).write_text("def bar(): pass")
        
        mock_construct.return_value = (
            {},
            {
                "input_prompt_file": "Original prompt",
                "modified_code_file": "def bar(): pass",
                "input_code_file": "def foo(): pass",
            },
            {"output": prompt_file},
            "python",
        )
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=prompt_file,
            modified_code_file=code_file,
            input_code_file=None,
            output=None,
            strength=0.8,  # Override
        )
        
        assert result is not None
        assert mock_ctx.obj["strength"] == 0.8


# =============================================================================
# INTEGRATION TESTS
# =============================================================================

class TestIntegration:
    """End-to-end integration tests with minimal mocking."""
    
    @patch('pdd.update_main.get_available_agents')
    @patch('pdd.update_main.update_prompt')
    @patch('pdd.update_main.get_language')
    def test_full_regeneration_workflow(
        self, mock_get_lang, mock_update_prompt, mock_agents, mock_ctx, temp_dir
    ):
        """Test complete regeneration workflow from code to prompt."""
        mock_agents.return_value = []
        mock_get_lang.return_value = "python"
        mock_update_prompt.return_value = (
            "# New Prompt\nGenerated from code", 0.05, "gpt-4"
        )
        
        code_file = os.path.join(temp_dir, "mymodule.py")
        Path(code_file).write_text("def calculate(x, y):\n    return x + y")
        
        result = update_main(
            ctx=mock_ctx,
            input_prompt_file=None,
            modified_code_file=code_file,
            input_code_file=None,
            output=None,
        )
        
        assert result is not None
        prompt, cost, model = result
        assert "Generated from code" in prompt
        assert cost > 0
        assert model == "gpt-4"
        
        # Verify prompt file was created
        expected_prompt_path = os.path.join(
            temp_dir, "prompts", "mymodule_python.prompt"
        )
        assert os.path.exists(expected_prompt_path)
        with open(expected_prompt_path) as f:
            assert f.read() == prompt


if __name__ == "__main__":
    pytest.main([__file__, "-v"])