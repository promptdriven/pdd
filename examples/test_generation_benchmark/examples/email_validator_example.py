import sys
import os

# Add the src directory to the Python path so we can import the module
# This assumes the structure:
#   project_root/
#     src/
#       email_validator.py
#     examples/
#       email_validator_example.py
current_dir = os.path.dirname(os.path.abspath(__file__))
src_path = os.path.join(current_dir, '..', 'src')
sys.path.append(src_path)

from email_validator import EmailValidator, ValidationResult

def main():
    """
    Demonstrates the usage of the EmailValidator class.
    """
    # 1. Initialize the validator
    validator = EmailValidator()

    print("--- Valid Email Examples ---")
    
    # Example A: A standard valid email
    # Input: "user.name@example.com"
    # Expected: Valid, normalized same as input
    email_a = "user.name@example.com"
    result_a = validator.validate_email(email_a)
    print(f"Input: '{email_a}'")
    print(f"  Is Valid: {result_a.is_valid}")
    print(f"  Normalized: '{result_a.normalized_email}'")
    print(f"  Error: {result_a.error_message}")
    print()

    # Example B: Email needing normalization (whitespace and uppercase)
    # Input: "  USER+TAG@EXAMPLE.ORG  "
    # Expected: Valid, normalized to "user+tag@example.org"
    email_b = "  USER+TAG@EXAMPLE.ORG  "
    result_b = validator.validate_email(email_b)
    print(f"Input: '{email_b}'")
    print(f"  Is Valid: {result_b.is_valid}")
    print(f"  Normalized: '{result_b.normalized_email}'")
    print()

    # Example C: Unicode characters in local part (allowed by this validator)
    # Input: "üser@example.com"
    # Expected: Valid
    email_c = "üser@example.com"
    result_c = validator.validate_email(email_c)
    print(f"Input: '{email_c}'")
    print(f"  Is Valid: {result_c.is_valid}")
    print()

    print("--- Invalid Email Examples ---")

    # Example D: Missing @ symbol
    # Input: "invalid-email"
    # Expected: Invalid, Error: "Email must contain exactly one @ symbol"
    email_d = "invalid-email"
    result_d = validator.validate_email(email_d)
    print(f"Input: '{email_d}'")
    print(f"  Is Valid: {result_d.is_valid}")
    print(f"  Error: {result_d.error_message}")
    print()

    # Example E: Consecutive dots
    # Input: "user..name@example.com"
    # Expected: Invalid, Error: "Email cannot contain consecutive dots"
    email_e = "user..name@example.com"
    result_e = validator.validate_email(email_e)
    print(f"Input: '{email_e}'")
    print(f"  Is Valid: {result_e.is_valid}")
    print(f"  Error: {result_e.error_message}")
    print()

    # Example F: Missing domain dot
    # Input: "user@localhost"
    # Expected: Invalid, Error: "Domain must contain at least one dot"
    email_f = "user@localhost"
    result_f = validator.validate_email(email_f)
    print(f"Input: '{email_f}'")
    print(f"  Is Valid: {result_f.is_valid}")
    print(f"  Error: {result_f.error_message}")
    print()

    # Example G: Empty string
    # Input: ""
    # Expected: Invalid, Error: "Email cannot be empty"
    email_g = ""
    result_g = validator.validate_email(email_g)
    print(f"Input: '{email_g}'")
    print(f"  Is Valid: {result_g.is_valid}")
    print(f"  Error: {result_g.error_message}")
    print()

if __name__ == "__main__":
    main()