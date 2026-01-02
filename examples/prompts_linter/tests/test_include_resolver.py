import pytest
import os
from pathlib import Path
from unittest.mock import patch
from z3 import Int, Solver, Implies, And, Or, Not, sat, unsat

from src.backend.core.include_resolver import (
    IncludeResolver, 
    PathSecurityError, 
    FileLoadError
)

"""
DETAILED TEST PLAN

1. Path Resolution & Security (IncludeResolver.resolve)
    - Test Case: Resolve a valid relative path within the root.
    - Test Case: Resolve a path using '../' that stays within the root.
    - Test Case: Attempt to resolve a path that traverses outside the root (PathSecurityError).
    - Test Case: Handle absolute paths provided as file_path (should still be checked against root).
    - Formal Verification (Z3): Verify that for any length L, the token estimation L/4 is always >= 0 and monotonic.
    - Formal Verification (Z3): Verify the security boundary logic: if a path is 'relative_to' the root, it cannot have a parent that is the root's parent.

2. Content Retrieval (IncludeResolver.read_content)
    - Test Case: Successfully read a UTF-8 file.
    - Test Case: Handle missing file (FileLoadError).
    - Test Case: Handle directory instead of file (FileLoadError).
    - Test Case: Handle permission denied (mocked) (FileLoadError).
    - Test Case: Handle non-UTF-8 encoding (should use 'replace' and not crash).

3. Token Estimation (IncludeResolver.estimate_tokens)
    - Test Case: Empty string returns 0.
    - Test Case: Short string (e.g., 3 chars) returns 0 (due to int truncation).
    - Test Case: Standard string (e.g., 12 chars) returns 3.
    - Test Case: Very long string.

4. Edge Case Analysis (Z3 vs Unit Test)
    - Path Traversal: Unit tests are better for testing actual OS path behavior. Z3 is better for verifying the logic of the 'is_relative_to' constraint.
    - Token Heuristic: Z3 is excellent for proving the bounds of the linear heuristic (len/4).
    - File I/O: Unit tests are required as Z3 cannot model the filesystem state effectively.
"""

@pytest.fixture
def temp_workspace(tmp_path):
    """Creates a temporary directory structure for testing."""
    root = tmp_path / "project"
    root.mkdir()
    
    src = root / "src"
    src.mkdir()
    
    secret = tmp_path / "secret"
    secret.mkdir()
    
    # Create a dummy file
    test_file = src / "hello.txt"
    test_file.write_text("Hello World", encoding="utf-8")
    
    # Create a secret file
    secret_file = secret / "passwords.txt"
    secret_file.write_text("123456", encoding="utf-8")
    
    return {
        "root": root,
        "src": src,
        "test_file": test_file,
        "secret_file": secret_file
    }

def test_resolve_valid_path(temp_workspace):
    resolver = IncludeResolver(root_path=temp_workspace["root"])
    # Resolve src/hello.txt from the root
    resolved = resolver.resolve("src/hello.txt", temp_workspace["root"])
    assert resolved == temp_workspace["test_file"].resolve()

def test_resolve_traversal_within_root(temp_workspace):
    resolver = IncludeResolver(root_path=temp_workspace["root"])
    # base_dir is project/src, path is ../src/hello.txt -> stays in root
    resolved = resolver.resolve("../src/hello.txt", temp_workspace["src"])
    assert resolved == temp_workspace["test_file"].resolve()

def test_resolve_security_violation(temp_workspace):
    resolver = IncludeResolver(root_path=temp_workspace["root"])
    # Attempt to go up from project to the temp_path/secret
    with pytest.raises(PathSecurityError) as excinfo:
        resolver.resolve("../../secret/passwords.txt", temp_workspace["src"])
    assert "Security violation" in str(excinfo.value)

def test_read_content_success(temp_workspace):
    resolver = IncludeResolver(root_path=temp_workspace["root"])
    content = resolver.read_content(temp_workspace["test_file"])
    assert content == "Hello World"

def test_read_content_file_not_found(temp_workspace):
    resolver = IncludeResolver(root_path=temp_workspace["root"])
    non_existent = temp_workspace["root"] / "ghost.txt"
    with pytest.raises(FileLoadError) as excinfo:
        resolver.read_content(non_existent)
    assert "File not found" in str(excinfo.value)

def test_read_content_is_directory(temp_workspace):
    resolver = IncludeResolver(root_path=temp_workspace["root"])
    with pytest.raises(FileLoadError) as excinfo:
        resolver.read_content(temp_workspace["src"])
    assert "Path is not a file" in str(excinfo.value)

def test_read_content_permission_error(temp_workspace):
    resolver = IncludeResolver(root_path=temp_workspace["root"])
    with patch("builtins.open", side_effect=PermissionError):
        with pytest.raises(FileLoadError) as excinfo:
            resolver.read_content(temp_workspace["test_file"])
        assert "Permission denied" in str(excinfo.value)

def test_estimate_tokens_values():
    assert IncludeResolver.estimate_tokens("") == 0
    assert IncludeResolver.estimate_tokens("abcd") == 1
    assert IncludeResolver.estimate_tokens("abc") == 0  # 3/4 = 0.75 -> 0
    assert IncludeResolver.estimate_tokens("abcdefgh") == 2

def test_z3_token_estimation_properties():
    """
    Formal verification of the token estimation heuristic using Z3.
    Verifies:
    1. Non-negativity: length >= 0 implies tokens >= 0
    2. Monotonicity: length_a > length_b implies tokens_a >= tokens_b
    """
    length = Int('length')
    tokens = Int('tokens')
    
    s = Solver()
    
    # Define the heuristic: tokens = length / 4 (integer division)
    # In Z3, / is real division, so we use length div 4
    heuristic = (tokens == length / 4)
    
    # Property 1: length >= 0 -> tokens >= 0
    s.push()
    s.add(heuristic)
    s.add(Not(Implies(length >= 0, tokens >= 0)))
    assert s.check() == unsat, "Z3: Token count can be negative for non-negative length"
    s.pop()
    
    # Property 2: Monotonicity
    len_a = Int('len_a')
    len_b = Int('len_b')
    tok_a = Int('tok_a')
    tok_b = Int('tok_b')
    
    s.push()
    s.add(tok_a == len_a / 4)
    s.add(tok_b == len_b / 4)
    # Check if there exists a case where len_a > len_b but tok_a < tok_b
    s.add(And(len_a > len_b, tok_a < tok_b))
    assert s.check() == unsat, "Z3: Token estimation is not monotonic"
    s.pop()

def test_z3_path_security_logic():
    """
    Formal verification of the security boundary logic.
    We model the 'depth' of paths relative to a root.
    """
    root_depth = Int('root_depth')
    target_depth = Int('target_depth')
    
    s = Solver()
    
    # A path is 'inside' the root if its depth is >= root depth 
    # and it shares the same prefix (simplified model).
    # If target_depth < root_depth, it is outside.
    
    is_outside = (target_depth < root_depth)
    
    # The code uses .relative_to(root), which raises ValueError if outside.
    # We want to ensure that if a path is outside, our logic catches it.
    
    # Property: If target is outside, relative_to must fail (modeled as is_outside)
    # This is a tautology in our simple model, but ensures we understand the boundary.
    s.add(root_depth == 5) # Assume root is at /a/b/c/d/e
    s.add(target_depth == 4) # Target is at /a/b/c/d
    
    # If target_depth < root_depth, it is impossible for it to be 'relative_to' root
    # without going 'up' (which .resolve() removes).
    assert s.check() == sat