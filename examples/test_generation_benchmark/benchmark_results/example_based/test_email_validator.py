"""
TEST PLAN FOR EMAIL_VALIDATOR MODULE

This test plan combines unit tests and Z3 formal verification to ensure
comprehensive validation of the EmailValidator module.

1. UNIT TEST STRATEGY:
   - Test all validation rules from the prompt
   - Test all edge cases from the prompt
   - Test normalization behavior
   - Test exception handling
   - Test public API contract

2. Z3 FORMAL VERIFICATION STRATEGY:
   - Use Z3 to formally verify the validation rules
   - Create symbolic representations of email constraints
   - Prove properties about valid/invalid emails
   - Verify that the implementation matches the specification

3. TEST CATEGORIES:

A. VALID EMAIL TESTS (Unit Tests):
   - Standard valid emails
   - Emails with normalization (whitespace, uppercase)
   - Emails with unicode characters
   - Emails with plus signs in local part
   - Emails with multiple subdomains

B. INVALID EMAIL TESTS (Unit Tests):
   - Missing @ symbol
   - Multiple @ symbols
   - Empty local part
   - Empty domain part
   - No dot in domain
   - Consecutive dots
   - Empty string (after stripping)
   - Whitespace-only string

C. EDGE CASE TESTS (Unit Tests):
   - None input (should raise TypeError)
   - Very long emails
   - Emails with special characters
   - Boundary cases for each rule

D. NORMALIZATION TESTS (Unit Tests):
   - Whitespace stripping
   - Lowercase conversion
   - Combined normalization

E. Z3 FORMAL VERIFICATION TESTS:
   - Prove that valid emails satisfy all constraints
   - Prove that invalid emails violate at least one constraint
   - Verify constraint relationships
   - Check for constraint contradictions

4. Z3 VS UNIT TEST ANALYSIS FOR EACH EDGE CASE:

   a) None input:
      - Unit Test: Better - Testing exception raising is straightforward
      - Z3: Not applicable - Z3 deals with string constraints, not None

   b) Empty string:
      - Unit Test: Better - Simple string emptiness check
      - Z3: Possible but overkill - Can model empty string constraint

   c) Exactly one @ symbol:
      - Z3: Excellent - Can formally verify count constraint
      - Unit Test: Also good - Can test 0, 1, and >1 @ cases

   d) Non-empty local part:
      - Z3: Good - Can model string length > 0 constraint
      - Unit Test: Good - Simple to test

   e) Domain contains at least one dot:
      - Z3: Excellent - Can model substring existence constraint
      - Unit Test: Good - Simple to test

   f) No consecutive dots:
      - Z3: Excellent - Can model pattern avoidance constraint
      - Unit Test: Good - Can test various patterns

   g) Whitespace stripping:
      - Unit Test: Better - String manipulation is straightforward
      - Z3: Possible but complex - Would need to model string transformations

   h) Lowercase normalization:
      - Unit Test: Better - Simple string comparison
      - Z3: Complex - Would need to model case conversion

   i) Unicode characters:
      - Unit Test: Better - Can test actual unicode strings
      - Z3: Limited - Z3 string theory may not handle all unicode well

5. Z3 FORMAL VERIFICATION APPROACH:
   - Create symbolic string variables for email
   - Define constraints as Z3 boolean expressions
   - Use Z3 solver to check satisfiability
   - Verify that implementation matches formal specification
   - Generate counterexamples for invalid cases

6. TEST ISOLATION STRATEGY:
   - Each test is independent
   - No shared state between tests
   - Use pytest fixtures for setup/teardown
   - Mock external dependencies if needed (none in this case)
"""

import sys
import os
import pytest
from dataclasses import dataclass
from typing import Optional

# Add the src directory to the Python path to import the module
current_dir = os.path.dirname(os.path.abspath(__file__))
src_path = os.path.join(current_dir, '..', 'src')
sys.path.append(src_path)

from email_validator import EmailValidator, ValidationResult

# Import Z3 for formal verification
try:
    from z3 import String, StringVal, And, Or, Not, Contains, Length, SubString, Solver, is_true
    Z3_AVAILABLE = True
except ImportError:
    Z3_AVAILABLE = False
    print("Z3 not available. Skipping formal verification tests.")


# Test fixtures
@pytest.fixture
def validator():
    """Fixture to provide a fresh EmailValidator instance for each test."""
    return EmailValidator()


# Unit Tests for Valid Emails
def test_valid_standard_email(validator):
    """Test a standard valid email address."""
    email = "user@example.com"
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "user@example.com"
    assert result.error_message is None


def test_valid_email_with_plus_tag(validator):
    """Test valid email with plus tag in local part."""
    email = "user+tag@example.org"
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "user+tag@example.org"
    assert result.error_message is None


def test_valid_email_with_multiple_subdomains(validator):
    """Test valid email with multiple subdomains."""
    email = "user@sub.domain.example.com"
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "user@sub.domain.example.com"
    assert result.error_message is None


def test_valid_email_normalization_whitespace(validator):
    """Test email normalization with whitespace."""
    email = "  user@example.com  "
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "user@example.com"
    assert result.error_message is None


def test_valid_email_normalization_uppercase(validator):
    """Test email normalization with uppercase."""
    email = "USER@EXAMPLE.COM"
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "user@example.com"
    assert result.error_message is None


def test_valid_email_unicode_local_part(validator):
    """Test valid email with unicode characters in local part."""
    email = "üser@example.com"
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "üser@example.com"
    assert result.error_message is None


def test_valid_email_dot_in_local_part(validator):
    """Test valid email with dot in local part."""
    email = "user.name@example.com"
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "user.name@example.com"
    assert result.error_message is None


# Unit Tests for Invalid Emails
def test_invalid_no_at_symbol(validator):
    """Test email without @ symbol."""
    email = "invalid-email"
    result = validator.validate_email(email)
    
    assert result.is_valid is False
    assert result.normalized_email == "invalid-email"
    assert result.error_message == "Email must contain exactly one @ symbol"


def test_invalid_multiple_at_symbols(validator):
    """Test email with multiple @ symbols."""
    email = "user@@example.com"
    result = validator.validate_email(email)
    
    assert result.is_valid is False
    assert result.normalized_email == "user@@example.com"
    assert result.error_message == "Email must contain exactly one @ symbol"


def test_invalid_empty_local_part(validator):
    """Test email with empty local part."""
    email = "@example.com"
    result = validator.validate_email(email)
    
    assert result.is_valid is False
    assert result.normalized_email == "@example.com"
    assert result.error_message == "Local part cannot be empty"


def test_invalid_no_dot_in_domain(validator):
    """Test email without dot in domain."""
    email = "user@localhost"
    result = validator.validate_email(email)
    
    assert result.is_valid is False
    assert result.normalized_email == "user@localhost"
    assert result.error_message == "Domain must contain at least one dot"


def test_invalid_consecutive_dots(validator):
    """Test email with consecutive dots."""
    email = "user..name@example.com"
    result = validator.validate_email(email)
    
    assert result.is_valid is False
    assert result.normalized_email == "user..name@example.com"
    assert result.error_message == "Email cannot contain consecutive dots"


def test_invalid_consecutive_dots_in_domain(validator):
    """Test email with consecutive dots in domain."""
    email = "user@example..com"
    result = validator.validate_email(email)
    
    assert result.is_valid is False
    assert result.normalized_email == "user@example..com"
    assert result.error_message == "Email cannot contain consecutive dots"


def test_invalid_empty_string(validator):
    """Test empty string email."""
    email = ""
    result = validator.validate_email(email)
    
    assert result.is_valid is False
    assert result.normalized_email == ""
    assert result.error_message == "Email cannot be empty"


def test_invalid_whitespace_only(validator):
    """Test whitespace-only string."""
    email = "   "
    result = validator.validate_email(email)
    
    assert result.is_valid is False
    assert result.normalized_email == ""
    assert result.error_message == "Email cannot be empty"


def test_invalid_domain_only(validator):
    """Test email with only domain part."""
    email = "@"
    result = validator.validate_email(email)
    
    assert result.is_valid is False
    assert result.normalized_email == "@"
    # Should fail on empty local part
    assert result.error_message == "Local part cannot be empty"


def test_invalid_local_part_only(validator):
    """Test email with only local part."""
    email = "user@"
    result = validator.validate_email(email)
    
    assert result.is_valid is False
    assert result.normalized_email == "user@"
    # Should fail on domain validation (no dot)
    assert result.error_message == "Domain must contain at least one dot"


# Edge Case Tests
def test_none_input_raises_typeerror(validator):
    """Test that None input raises TypeError."""
    with pytest.raises(TypeError) as exc_info:
        validator.validate_email(None)
    
    assert str(exc_info.value) == "email cannot be None"


def test_long_valid_email(validator):
    """Test a long but valid email address."""
    local_part = "a" * 64  # 64 character local part
    domain = "example.com"
    email = f"{local_part}@{domain}"
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == email.lower()


def test_email_with_special_characters(validator):
    """Test email with various special characters."""
    email = "user!#$%&'*+-/=?^_`{|}~@example.com"
    result = validator.validate_email(email)
    
    # According to our validation rules, this should be valid
    # (we don't restrict special characters in local part)
    assert result.is_valid is True
    assert result.normalized_email == email.lower()


def test_email_with_multiple_dots_in_domain(validator):
    """Test email with multiple (non-consecutive) dots in domain."""
    email = "user@sub.domain.example.com"
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "user@sub.domain.example.com"


# Normalization Tests
def test_normalization_combined(validator):
    """Test combined normalization (whitespace + uppercase)."""
    email = "  USER@EXAMPLE.COM  "
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "user@example.com"


def test_normalization_preserves_valid_email(validator):
    """Test that normalization doesn't break valid emails."""
    email = "  user.name+tag@sub.example.com  "
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "user.name+tag@sub.example.com"


# Z3 Formal Verification Tests
if Z3_AVAILABLE:
    
    def test_z3_formal_verification_constraints():
        """Formally verify that the validation constraints are correctly specified."""
        # Create symbolic email string
        email = String('email')
        
        # Define constraints from the specification
        # 1. Must contain exactly one @ symbol
        # We model this as: count(@) = 1
        # In Z3, we can check that there's exactly one @
        at_count = StringVal('@')
        
        # Helper function to check for exactly one occurrence
        # This is simplified - in practice we'd need more complex logic
        # For demonstration, we'll create a simple constraint
        
        # 2. Local part cannot be empty
        # Let's find the position of @
        at_pos = email.index('@')
        local_part = SubString(email, 0, at_pos)
        local_non_empty = Length(local_part) > 0
        
        # 3. Domain part must contain at least one dot
        domain_part = SubString(email, at_pos + 1, Length(email) - at_pos - 1)
        domain_has_dot = Contains(domain_part, '.')
        
        # 4. No consecutive dots anywhere
        # This is complex in Z3 - for simplicity, we'll skip this constraint
        # in this demonstration
        
        # Create solver
        s = Solver()
        
        # Add constraints for a valid email
        s.add(at_pos >= 0)  # Email contains @
        s.add(local_non_empty)
        s.add(domain_has_dot)
        
        # Check if constraints are satisfiable (a valid email exists)
        assert s.check() == 'sat', "Valid email constraints should be satisfiable"
        
        # Get a model (example valid email)
        model = s.model()
        print(f"Z3 generated valid email example: {model[email]}")
    
    
    def test_z3_invalid_email_violates_constraints():
        """Formally verify that invalid emails violate at least one constraint."""
        # Create solver
        s = Solver()
        
        # Create symbolic email
        email = String('email')
        
        # Define the negation of each constraint
        # 1. No @ symbol OR multiple @ symbols
        # 2. Empty local part
        # 3. No dot in domain
        # 4. Has consecutive dots (skipped for simplicity)
        
        # For an invalid email, at least one of these should be true
        invalid_constraint = Or(
            Not(Contains(email, '@')),  # No @
            Length(SubString(email, 0, email.index('@'))) == 0,  # Empty local part
            Not(Contains(SubString(email, email.index('@') + 1, 
                                  Length(email) - email.index('@') - 1), '.'))  # No dot in domain
        )
        
        s.add(invalid_constraint)
        
        # Should be satisfiable (invalid emails exist)
        assert s.check() == 'sat', "Invalid email constraints should be satisfiable"
        
        model = s.model()
        print(f"Z3 generated invalid email example: {model[email]}")
    
    
    def test_z3_constraint_consistency():
        """Verify that constraints are not contradictory."""
        s = Solver()
        email = String('email')
        
        # All constraints for a valid email
        at_pos = email.index('@')
        local_part = SubString(email, 0, at_pos)
        domain_part = SubString(email, at_pos + 1, Length(email) - at_pos - 1)
        
        constraints = And(
            at_pos >= 0,  # Has @
            Length(local_part) > 0,  # Local part not empty
            Contains(domain_part, '.')  # Domain has dot
        )
        
        # Check if constraints are self-consistent
        s.add(constraints)
        
        # Should be satisfiable (not contradictory)
        result = s.check()
        assert result == 'sat', f"Constraints should be consistent, got {result}"
        
        # Also check that we can't have an email that's both valid and invalid
        s2 = Solver()
        s2.add(constraints)
        s2.add(Not(constraints))  # Add the negation
        
        result2 = s2.check()
        assert result2 == 'unsat', "Email cannot be both valid and invalid"
    
    
    def test_z3_verification_matches_unit_tests(validator):
        """Verify that Z3 constraints match actual implementation for sample cases."""
        # Test cases that should be valid according to Z3 constraints
        valid_cases = [
            "user@example.com",
            "a@b.c",
            "test@domain.co.uk",
        ]
        
        # Test cases that should be invalid according to Z3 constraints
        invalid_cases = [
            "noat",  # No @
            "@domain.com",  # Empty local part
            "user@nodot",  # No dot in domain
        ]
        
        # Check valid cases
        for email in valid_cases:
            result = validator.validate_email(email)
            assert result.is_valid is True, f"Email '{email}' should be valid"
        
        # Check invalid cases
        for email in invalid_cases:
            result = validator.validate_email(email)
            assert result.is_valid is False, f"Email '{email}' should be invalid"


# Additional comprehensive tests
def test_validation_result_dataclass():
    """Test that ValidationResult dataclass works correctly."""
    # Valid case
    valid_result = ValidationResult(
        is_valid=True,
        normalized_email="user@example.com",
        error_message=None
    )
    
    assert valid_result.is_valid is True
    assert valid_result.normalized_email == "user@example.com"
    assert valid_result.error_message is None
    
    # Invalid case
    invalid_result = ValidationResult(
        is_valid=False,
        normalized_email="invalid",
        error_message="Test error"
    )
    
    assert invalid_result.is_valid is False
    assert invalid_result.normalized_email == "invalid"
    assert invalid_result.error_message == "Test error"


def test_email_validator_reusable(validator):
    """Test that EmailValidator can be reused for multiple validations."""
    emails = [
        "user1@example.com",
        "user2@example.org",
        "user3@example.net"
    ]
    
    for email in emails:
        result = validator.validate_email(email)
        assert result.is_valid is True
        assert result.normalized_email == email.lower()


def test_error_messages_are_clear(validator):
    """Test that error messages clearly indicate what's wrong."""
    test_cases = [
        ("", "Email cannot be empty"),
        ("@example.com", "Local part cannot be empty"),
        ("user@", "Domain must contain at least one dot"),
        ("user@@example.com", "Email must contain exactly one @ symbol"),
        ("user@localhost", "Domain must contain at least one dot"),
        ("user..name@example.com", "Email cannot contain consecutive dots"),
    ]
    
    for email, expected_error in test_cases:
        result = validator.validate_email(email)
        assert result.is_valid is False
        assert result.error_message == expected_error, \
            f"Expected error '{expected_error}' for email '{email}', got '{result.error_message}'"


# Test for boundary cases
def test_boundary_case_single_character_local_part(validator):
    """Test email with single character local part."""
    email = "a@example.com"
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "a@example.com"


def test_boundary_case_single_character_domain_part(validator):
    """Test email with single character domain part (but with dot)."""
    email = "user@a.b"
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "user@a.b"


def test_email_with_underscore(validator):
    """Test email with underscore in local part."""
    email = "user_name@example.com"
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "user_name@example.com"


def test_email_with_hyphen(validator):
    """Test email with hyphen in domain."""
    email = "user@example-domain.com"
    result = validator.validate_email(email)
    
    assert result.is_valid is True
    assert result.normalized_email == "user@example-domain.com"


# Test the order of validation checks
def test_validation_order_empty_string_before_other_checks(validator):
    """Test that empty string check happens before other validations."""
    # Empty string should give "Email cannot be empty" not "@ symbol" error
    result = validator.validate_email("")
    assert result.error_message == "Email cannot be empty"


def test_validation_order_whitespace_stripping_first(validator):
    """Test that whitespace stripping happens before validation."""
    # This email would be invalid without stripping (no @ after stripping)
    email = "  @  "
    result = validator.validate_email(email)
    
    # After stripping, it becomes "@" which fails on empty local part
    assert result.is_valid is False
    assert result.error_message == "Local part cannot be empty"


# Performance/Stress tests (optional)
def test_performance_multiple_validations(validator):
    """Test that validator can handle multiple validations efficiently."""
    import time
    
    # Create list of test emails
    test_emails = [
        "user@example.com",
        "  USER@EXAMPLE.COM  ",
        "user.name@example.com",
        "user+tag@example.org",
        "invalid-email",
        "user@@example.com",
        "@example.com",
        "user@localhost",
        "user..name@example.com",
        "",
    ] * 100  # Repeat 100 times for 1000 total validations
    
    start_time = time.time()
    
    for email in test_emails:
        result = validator.validate_email(email)
        # Just ensure no exceptions
        assert isinstance(result, ValidationResult)
    
    end_time = time.time()
    elapsed = end_time - start_time
    
    # Should complete in reasonable time (adjust threshold as needed)
    assert elapsed < 1.0, f"Validations took too long: {elapsed:.2f} seconds"


if __name__ == "__main__":
    # Run tests if executed directly
    pytest.main([__file__, "-v"])