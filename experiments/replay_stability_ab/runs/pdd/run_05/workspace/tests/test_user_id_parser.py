"""
Test Plan:

1. Unit Tests:
    - Test valid string input format "user:<id>".
    - Test valid dict input format {"user_id": "<id>"}.
    - Test valid nested dict input format {"user": {"id": "<id>"}}.
    - Test normalization: whitespace trimming and lowercasing.
    - Test regex validation: length constraints (3-20 chars) and allowed characters.
    - Test reserved words rejection (admin, root, system).
    - Test invalid input types (int, list, None).
    - Test malformed dictionaries (missing keys, wrong nesting).
    - Test input immutability (ensure dicts aren't modified).

2. Formal Verification (Z3):
    - Model the validation logic (length, allowed chars, reserved words).
    - Use Z3 to generate a set of valid IDs and verify the function accepts them.
    - Use Z3 to generate a set of invalid IDs (too short, too long, invalid chars) and verify rejection.
"""

import pytest
import sys
import os
# Fix: Import necessary Z3 regex functions directly
from z3 import Solver, String, Length, And, Or, Not, Re, StringVal, InRe, Range, Union, Star, Loop

# Add the src directory to the path so we can import the module
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

try:
    from user_id_parser import parse_user_id
except ImportError:
    # Fallback for environments where the module structure isn't pre-defined
    def parse_user_id(data):
        pass

# --- Unit Tests ---

def test_valid_string_input():
    """Test parsing valid string input 'user:<id>'."""
    assert parse_user_id("user:jdoe") == "jdoe"
    assert parse_user_id("user:alice123") == "alice123"

def test_valid_dict_flat_input():
    """Test parsing valid dict input {'user_id': '<id>'}."""
    assert parse_user_id({"user_id": "jdoe"}) == "jdoe"

def test_valid_dict_nested_input():
    """Test parsing valid dict input {'user': {'id': '<id>'}}."""
    assert parse_user_id({"user": {"id": "jdoe"}}) == "jdoe"

def test_normalization_whitespace():
    """Test that IDs are trimmed of whitespace."""
    assert parse_user_id("user:  jdoe  ") == "jdoe"
    assert parse_user_id({"user_id": "\talice\n"}) == "alice"

def test_normalization_lowercase():
    """Test that IDs are converted to lowercase."""
    assert parse_user_id("user:JDOE") == "jdoe"
    assert parse_user_id({"user_id": "Alice123"}) == "alice123"

def test_regex_valid_chars():
    """Test IDs with allowed special characters (hyphen, underscore)."""
    assert parse_user_id("user:my-name") == "my-name"
    assert parse_user_id("user:my_name") == "my_name"

def test_regex_length_constraints():
    """Test boundary conditions for ID length (3 to 20 characters)."""
    # Minimum length (3)
    assert parse_user_id("user:abc") == "abc"
    # Maximum length (20)
    assert parse_user_id("user:" + "a" * 20) == "a" * 20
    
    # Too short (2)
    assert parse_user_id("user:ab") is None
    # Too long (21)
    assert parse_user_id("user:" + "a" * 21) is None

def test_reserved_ids():
    """Test that reserved IDs are rejected."""
    reserved = ["admin", "root", "system"]
    for rid in reserved:
        assert parse_user_id(f"user:{rid}") is None
        assert parse_user_id(f"user:{rid.upper()}") is None  # Case insensitive check

def test_invalid_string_format():
    """Test strings that do not start with 'user:'."""
    assert parse_user_id("u:jdoe") is None
    assert parse_user_id("jdoe") is None
    assert parse_user_id("user_id:jdoe") is None

def test_invalid_dict_structure():
    """Test dictionaries with missing or wrong keys."""
    assert parse_user_id({}) is None
    assert parse_user_id({"id": "jdoe"}) is None
    assert parse_user_id({"user": "jdoe"}) is None  # 'user' is not a dict
    assert parse_user_id({"user": {}}) is None      # 'user' dict missing 'id'

def test_invalid_types_inside_dict():
    """Test dictionaries containing non-string values where strings are expected."""
    assert parse_user_id({"user_id": 12345}) is None
    assert parse_user_id({"user": {"id": None}}) is None
    assert parse_user_id({"user": {"id": ["list"]}}) is None

def test_invalid_input_types():
    """Test completely invalid input types."""
    assert parse_user_id(None) is None
    assert parse_user_id(123) is None
    assert parse_user_id(["user:jdoe"]) is None

def test_immutability():
    """Test that the input dictionary is not mutated."""
    data = {"user": {"id": "  JDOE  "}}
    original_data = {"user": {"id": "  JDOE  "}}
    
    result = parse_user_id(data)
    
    assert result == "jdoe"
    assert data == original_data

# --- Z3 Formal Verification Tests ---

def test_z3_verify_valid_ids():
    """
    Use Z3 to generate valid strings matching the regex and constraints,
    then verify the python function accepts them.
    """
    s = Solver()
    val = String('val')
    
    # Regex: ^[a-z0-9_-]{3,20}$
    # Fix: Use Union, Range, Re directly. Re is a function, not a namespace.
    allowed_chars = Union(Range('a', 'z'), Range('0', '9'), Re("_"), Re("-"))
    
    # Construct regex for 3 to 20 repetitions
    # Fix: Use Loop directly
    pattern = Loop(allowed_chars, 3, 20)
    
    # Constraints
    s.add(InRe(val, pattern))
    
    # Exclude reserved words
    s.add(val != StringVal("admin"))
    s.add(val != StringVal("root"))
    s.add(val != StringVal("system"))
    
    # Generate 5 examples
    for _ in range(5):
        if s.check() == str(pytest.approx(1)) or s.check().r == 1: # sat
            model = s.model()
            generated_id = model[val].as_string()
            # Z3 strings might come out as unicode literals in python, ensure standard str
            generated_id = generated_id.replace('"', '') 
            
            # Test against our function
            # We wrap it in "user:" to simulate valid input
            assert parse_user_id(f"user:{generated_id}") == generated_id
            
            # Add constraint to find a different solution next time
            s.add(val != StringVal(generated_id))
        else:
            break

def test_z3_verify_invalid_length_short():
    """Use Z3 to generate IDs that are too short and verify rejection."""
    s = Solver()
    val = String('val')
    
    # Fix: Use Union, Range, Re directly
    allowed_chars = Union(Range('a', 'z'), Range('0', '9'), Re("_"), Re("-"))
    
    # Length < 3
    s.add(Length(val) < 3)
    # But only contains valid chars
    # Fix: Use Star directly
    s.add(InRe(val, Star(allowed_chars)))
    
    if s.check() == str(pytest.approx(1)) or s.check().r == 1: # sat
        model = s.model()
        generated_id = model[val].as_string().replace('"', '')
        assert parse_user_id(f"user:{generated_id}") is None

def test_z3_verify_invalid_length_long():
    """Use Z3 to generate IDs that are too long and verify rejection."""
    s = Solver()
    val = String('val')
    
    # Fix: Use Union, Range, Re directly
    allowed_chars = Union(Range('a', 'z'), Range('0', '9'), Re("_"), Re("-"))
    
    # Length > 20
    s.add(Length(val) > 20)
    # Limit search space slightly to avoid infinite search for "long" strings
    s.add(Length(val) < 30) 
    # Only contains valid chars
    # Fix: Use Star directly
    s.add(InRe(val, Star(allowed_chars)))
    
    if s.check() == str(pytest.approx(1)) or s.check().r == 1: # sat
        model = s.model()
        generated_id = model[val].as_string().replace('"', '')
        assert parse_user_id(f"user:{generated_id}") is None

def test_z3_verify_reserved_words_logic():
    """
    Verify that if Z3 picks a reserved word, the function rejects it.
    This is a sanity check on the reserved word logic specifically.
    """
    s = Solver()
    val = String('val')
    
    # Force Z3 to pick a reserved word
    s.add(Or(
        val == StringVal("admin"),
        val == StringVal("root"),
        val == StringVal("system")
    ))
    
    # Check all 3
    count = 0
    while s.check() == str(pytest.approx(1)) or s.check().r == 1 and count < 3: # sat
        model = s.model()
        generated_id = model[val].as_string().replace('"', '')
        
        assert parse_user_id(f"user:{generated_id}") is None
        
        s.add(val != StringVal(generated_id))
        count += 1