"""
Test Plan:

1. Unit Tests (Pytest):
    - Test String Input:
        - Valid format "user:abc"
        - Invalid prefix "u:abc"
        - Just prefix "user:"
    - Test Dictionary Input:
        - Flat: {"user_id": "abc"}
        - Nested: {"user": {"id": "abc"}}
        - Missing keys
        - Invalid value types (int, None)
    - Test Normalization:
        - Trimming whitespace "  abc  "
        - Lowercasing "ABC"
    - Test Validation Rules:
        - Length boundaries (2 chars -> fail, 3 chars -> pass, 20 chars -> pass, 21 chars -> fail)
        - Allowed characters (a-z, 0-9, _, -)
        - Invalid characters (spaces, symbols)
    - Test Reserved IDs:
        - "admin", "root", "system" (and mixed case variants)
    - Test Robustness:
        - None input
        - Empty structures
        - Malformed nested dicts (e.g. raw["user"] is not a dict)
    - Test Immutability:
        - Ensure input dict is not modified

2. Formal Verification (Z3):
    - Verify that the set of constraints (Length 3-20, Allowed Chars) does not theoretically exclude valid IDs that aren't reserved.
    - (Note: Full string manipulation verification in Z3 is complex; we will focus on verifying the logic of the constraints themselves).
"""

import pytest
import sys
import os
from z3 import Solver, String, Length, And, Or, Not, Re, InRe, Range, Union, Star, StringVal

# Add the src directory to the path so we can import the module
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

from user_id_parser import parse_user_id

# --- Unit Tests ---

def test_parse_string_valid():
    """Test parsing valid string format 'user:<id>'."""
    assert parse_user_id("user:jdoe") == "jdoe"
    assert parse_user_id("user:123_abc") == "123_abc"

def test_parse_string_invalid_prefix():
    """Test string inputs with incorrect prefixes."""
    assert parse_user_id("u:jdoe") is None
    assert parse_user_id("userid:jdoe") is None
    assert parse_user_id("jdoe") is None

def test_parse_dict_flat_valid():
    """Test parsing flat dictionary format {'user_id': '<id>'}."""
    assert parse_user_id({"user_id": "jdoe"}) == "jdoe"

def test_parse_dict_nested_valid():
    """Test parsing nested dictionary format {'user': {'id': '<id>'}}."""
    assert parse_user_id({"user": {"id": "jdoe"}}) == "jdoe"

def test_parse_dict_missing_keys():
    """Test dictionaries with missing keys return None."""
    assert parse_user_id({"other": "value"}) is None
    assert parse_user_id({"user": {}}) is None
    assert parse_user_id({}) is None

def test_normalization_whitespace():
    """Test that whitespace is trimmed."""
    assert parse_user_id("user:  jdoe  ") == "jdoe"
    assert parse_user_id({"user_id": "\t jdoe \n"}) == "jdoe"

def test_normalization_case():
    """Test that IDs are converted to lowercase."""
    assert parse_user_id("user:JDOE") == "jdoe"
    assert parse_user_id({"user_id": "MixedCase"}) == "mixedcase"

def test_validation_length():
    """Test length constraints (3-20 characters)."""
    # Too short
    assert parse_user_id("user:ab") is None
    # Boundary (3)
    assert parse_user_id("user:abc") == "abc"
    # Boundary (20)
    long_id = "a" * 20
    assert parse_user_id(f"user:{long_id}") == long_id
    # Too long (21)
    too_long = "a" * 21
    assert parse_user_id(f"user:{too_long}") is None

def test_validation_characters():
    """Test allowed and disallowed characters."""
    # Allowed: a-z, 0-9, _, -
    assert parse_user_id("user:valid-user_1") == "valid-user_1"
    
    # Disallowed
    assert parse_user_id("user:invalid.user") is None # dot
    assert parse_user_id("user:user@name") is None    # @
    assert parse_user_id("user:user name") is None    # space inside

def test_reserved_ids():
    """Test that reserved IDs are rejected."""
    reserved = ["admin", "root", "system"]
    for rid in reserved:
        assert parse_user_id(f"user:{rid}") is None
        assert parse_user_id({"user_id": rid}) is None
        # Case insensitive check
        assert parse_user_id(f"user:{rid.upper()}") is None

def test_invalid_types_in_dict():
    """Test that non-string values in dictionaries are handled gracefully."""
    assert parse_user_id({"user_id": 12345}) is None
    assert parse_user_id({"user_id": None}) is None
    assert parse_user_id({"user": {"id": 123}}) is None

def test_malformed_nested_structure():
    """Test structures that don't match the expected schema types."""
    # "user" exists but is not a dict, so raw["user"]["id"] would fail if not careful
    # The code uses isinstance checks or .get safely
    assert parse_user_id({"user": "not_a_dict"}) is None
    assert parse_user_id({"user": None}) is None

def test_input_immutability():
    """Test that the input dictionary is not mutated."""
    data = {"user_id": "  JDOE  "}
    original_data = data.copy()
    
    result = parse_user_id(data)
    
    assert result == "jdoe"
    assert data == original_data
    assert data["user_id"] == "  JDOE  " # Ensure value wasn't stripped in place

def test_none_input():
    """Test None input."""
    assert parse_user_id(None) is None

# --- Z3 Formal Verification Tests ---

def test_z3_reserved_words_logic():
    """
    Use Z3 to verify that if a string matches the regex pattern but is a reserved word,
    it is correctly identified as 'invalid' by our logical model of the function.
    
    This tests the consistency of our requirements: 
    Is it possible to have a string that is both a valid regex match AND a reserved word?
    Yes, and we want to ensure our logic catches it.
    """
    s = Solver()
    
    # The string variable representing the normalized ID
    user_id = String('user_id')
    
    # 1. Define the Regex constraint: ^[a-z0-9_-]{3,20}$
    # Z3 Regex construction
    lowercase = Range('a', 'z')
    digits = Range('0', '9')
    underscore = Re('_')
    hyphen = Re('-')
    allowed_chars = Union(lowercase, digits, underscore, hyphen)
    
    # Length constraint is hard to do purely with Regex in Z3 sometimes, 
    # so we combine Regex structure with Length function.
    # Pattern: Star(allowed_chars) means 0 or more allowed chars.
    pattern = Star(allowed_chars)
    
    # Apply constraints
    s.add(InRe(user_id, pattern))
    s.add(Length(user_id) >= 3)
    s.add(Length(user_id) <= 20)
    
    # 2. Define Reserved Words constraint
    is_reserved = Or(
        user_id == StringVal("admin"),
        user_id == StringVal("root"),
        user_id == StringVal("system")
    )
    
    # 3. We want to find a case where it IS a valid pattern AND it IS reserved.
    # This proves that the reserved word check is NECESSARY because the regex alone permits them.
    s.add(is_reserved)
    
    # Check satisfiability
    result = s.check()
    
    # We expect SAT (Satisfiable), meaning "admin", "root", etc. are indeed valid regex matches
    # and thus MUST be explicitly filtered by the code.
    assert result == str(result) == "sat" or result.r == 1 # Z3 result handling
    
    # Get a model to see which one it found (e.g., "admin")
    model = s.model()
    found_id = model[user_id].as_string()
    assert found_id in ["admin", "root", "system"]

def test_z3_valid_id_existence():
    """
    Verify that there exists a string that is valid (matches regex) AND is NOT reserved.
    This ensures our constraints aren't so tight that no user ID is possible.
    """
    s = Solver()
    user_id = String('user_id')
    
    # Regex components
    lowercase = Range('a', 'z')
    digits = Range('0', '9')
    underscore = Re('_')
    hyphen = Re('-')
    allowed_chars = Union(lowercase, digits, underscore, hyphen)
    pattern = Star(allowed_chars)
    
    # Constraints
    s.add(InRe(user_id, pattern))
    s.add(Length(user_id) >= 3)
    s.add(Length(user_id) <= 20)
    
    # Not reserved
    s.add(Not(Or(
        user_id == StringVal("admin"),
        user_id == StringVal("root"),
        user_id == StringVal("system")
    )))
    
    # Check
    assert str(s.check()) == "sat"
    
    # Verify the model produces something valid for the python function
    model = s.model()
    generated_id = model[user_id].as_string()
    
    # Cross-verify with actual function
    # We wrap it in "user:" to simulate raw input
    assert parse_user_id(f"user:{generated_id}") == generated_id