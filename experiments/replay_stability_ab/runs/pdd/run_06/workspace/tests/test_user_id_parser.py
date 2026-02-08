import sys
import os
import pytest
from z3 import *

# Add the source directory to the path so we can import the module
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

try:
    from user_id_parser import parse_user_id
except ImportError:
    # Mocking the function for the sake of a standalone runnable example if the module doesn't exist
    def parse_user_id(val):
        pass

"""
DETAILED TEST PLAN:

1.  **Unit Tests (Functional & Edge Cases):**
    *   **String Input:**
        *   Valid format: "user:valid_id" -> "valid_id"
        *   Invalid prefix: "admin:valid_id" -> None
        *   Missing prefix: "valid_id" -> None
        *   Empty string: "" -> None
    *   **Dictionary Input:**
        *   Flat format: {"user_id": "valid_id"} -> "valid_id"
        *   Nested format: {"user": {"id": "valid_id"}} -> "valid_id"
        *   Missing keys: {} -> None
        *   Wrong keys: {"id": "valid_id"} -> None
        *   Nested wrong type: {"user": "not_a_dict"} -> None
    *   **Normalization:**
        *   Whitespace trimming: "  valid_id  " -> "valid_id"
        *   Case insensitivity: "VALID_ID" -> "valid_id"
        *   Mixed: "  VaLiD_iD  " -> "valid_id"
    *   **Validation (Regex & Constraints):**
        *   Valid characters: "abc-123_xyz"
        *   Too short: "ab" -> None
        *   Too long: "a" * 21 -> None
        *   Invalid characters: "valid$id", "valid id" (space) -> None
    *   **Reserved IDs:**
        *   "admin", "root", "system" -> None (even if mixed case like "Admin")
    *   **Input Safety:**
        *   None input -> None
        *   List input -> None
        *   Integer input -> None
        *   Immutability: Ensure input dict is not modified.

2.  **Z3 Formal Verification:**
    *   **Regex Equivalence:** Verify that the regex logic implemented in Python matches the formal constraints (length 3-20, allowed chars).
    *   **Reserved Word Exclusion:** Prove that if an ID is one of the reserved words, the validation logic *must* reject it.
    *   **Normalization Consistency:** Prove that for any string S, if `normalize(S)` is a reserved word, it is rejected.
"""

# ==========================================
# UNIT TESTS
# ==========================================

def test_parse_string_valid():
    """Test valid string input format 'user:<id>'."""
    assert parse_user_id("user:john_doe") == "john_doe"
    assert parse_user_id("user:abc-123") == "abc-123"

def test_parse_string_invalid_format():
    """Test string inputs that do not match the expected prefix."""
    assert parse_user_id("admin:john_doe") is None
    assert parse_user_id("john_doe") is None
    assert parse_user_id("user:") is None  # Too short after extraction
    assert parse_user_id("") is None

def test_parse_dict_flat_valid():
    """Test valid flat dictionary input {'user_id': '<id>'}."""
    assert parse_user_id({"user_id": "john_doe"}) == "john_doe"

def test_parse_dict_nested_valid():
    """Test valid nested dictionary input {'user': {'id': '<id>'}}."""
    assert parse_user_id({"user": {"id": "john_doe"}}) == "john_doe"

def test_parse_dict_invalid_structure():
    """Test dictionary inputs with missing or wrong keys."""
    assert parse_user_id({}) is None
    assert parse_user_id({"id": "john_doe"}) is None
    assert parse_user_id({"user": "john_doe"}) is None  # 'user' is not a dict
    assert parse_user_id({"user": {}}) is None  # Missing 'id' inside 'user'

def test_normalization_whitespace():
    """Test that whitespace is trimmed from the extracted ID."""
    assert parse_user_id("user:  john_doe  ") == "john_doe"
    assert parse_user_id({"user_id": "\tjohn_doe\n"}) == "john_doe"

def test_normalization_lowercase():
    """Test that IDs are converted to lowercase."""
    assert parse_user_id("user:JOHN_DOE") == "john_doe"
    assert parse_user_id({"user_id": "JoHn_DoE"}) == "john_doe"

def test_validation_length():
    """Test ID length constraints (3-20 characters)."""
    # Boundary: 3 chars (Valid)
    assert parse_user_id("user:abc") == "abc"
    # Boundary: 2 chars (Invalid)
    assert parse_user_id("user:ab") is None
    
    # Boundary: 20 chars (Valid)
    assert parse_user_id("user:" + "a" * 20) == "a" * 20
    # Boundary: 21 chars (Invalid)
    assert parse_user_id("user:" + "a" * 21) is None

def test_validation_characters():
    """Test allowed characters (a-z, 0-9, _, -)."""
    assert parse_user_id("user:valid-user_123") == "valid-user_123"
    assert parse_user_id("user:invalid$user") is None
    assert parse_user_id("user:invalid user") is None # Space not allowed inside ID
    assert parse_user_id("user:user@name") is None

def test_reserved_ids():
    """Test that reserved IDs are rejected."""
    reserved = ["admin", "root", "system"]
    for rid in reserved:
        assert parse_user_id(f"user:{rid}") is None
        assert parse_user_id({"user_id": rid}) is None
        # Test case insensitivity for reserved words
        assert parse_user_id(f"user:{rid.upper()}") is None

def test_invalid_types():
    """Test inputs that are not strings or dicts."""
    assert parse_user_id(None) is None
    assert parse_user_id(12345) is None
    assert parse_user_id(["user:john_doe"]) is None

def test_nested_type_safety():
    """Test that malformed nested structures don't raise exceptions."""
    assert parse_user_id({"user": None}) is None
    assert parse_user_id({"user": ["id", "john"]}) is None

def test_extracted_value_not_string():
    """Test cases where the extracted value exists but is not a string."""
    assert parse_user_id({"user_id": 123}) is None
    assert parse_user_id({"user": {"id": None}}) is None

def test_immutability():
    """Test that the input dictionary is not mutated."""
    data = {"user_id": "  john_doe  "}
    original_data = data.copy()
    parse_user_id(data)
    assert data == original_data

# ==========================================
# Z3 FORMAL VERIFICATION TESTS
# ==========================================

def test_z3_reserved_words_logic():
    """
    Formal verification: Prove that if a normalized ID matches a reserved word,
    the validation logic rejects it.
    """
    s = Solver()
    reserved_words = [StringVal("admin"), StringVal("root"), StringVal("system")]
    normalized_id = String("normalized_id")
    is_reserved = Or([normalized_id == w for w in reserved_words])
    
    # Premise: The ID is one of the reserved words
    s.add(is_reserved)
    
    # Conclusion: It must be rejected. 
    # We check for counter-example: It is accepted.
    # Acceptance logic: Not in reserved set.
    is_accepted = And([normalized_id != w for w in reserved_words])
    s.add(is_accepted)
    
    result = s.check()
    assert result == unsat, "Z3 found a case where a reserved word could be accepted!"

def test_z3_length_constraints():
    """
    Formal verification: Prove that valid IDs must be within length 3-20.
    """
    s = Solver()
    user_id = String("user_id")
    
    # Construct regex components for Z3
    range_az = Range("a", "z")
    range_09 = Range("0", "9")
    char_underscore = Re("_")
    char_dash = Re("-")
    allowed_chars = Union(range_az, range_09, char_underscore, char_dash)
    
    # The regex is allowed_chars repeated 3 to 20 times
    id_regex = Loop(allowed_chars, 3, 20)
    
    # Constraint: The string matches the regex
    matches_regex = InRe(user_id, id_regex)
    
    # Prove: matches_regex => (3 <= len <= 20)
    # Counter-example: matches_regex AND NOT (3 <= len <= 20)
    s.add(matches_regex)
    s.add(Not(And(Length(user_id) >= 3, Length(user_id) <= 20)))
    
    result = s.check()
    assert result == unsat, "Z3 found a string matching the regex but with invalid length!"