import sys
import os

# Add the directory containing the module to the Python path
# This allows importing the module regardless of where this script is run from
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../src")))

from user_id_parser import parse_user_id

def main():
    """
    Demonstrates various usage scenarios for the parse_user_id function.
    """
    
    print("--- Valid Inputs ---")
    
    # Scenario 1: String input with prefix
    # Input: "user:john_doe" -> Output: "john_doe"
    raw_str = "user:john_doe"
    result = parse_user_id(raw_str)
    print(f"String input '{raw_str}': {result}")

    # Scenario 2: Flat dictionary input
    # Input: {"user_id": "  ALICE-123  "} -> Output: "alice-123" (normalized)
    raw_dict_flat = {"user_id": "  ALICE-123  "}
    result = parse_user_id(raw_dict_flat)
    print(f"Flat dict input {raw_dict_flat}: {result}")

    # Scenario 3: Nested dictionary input
    # Input: {"user": {"id": "bob_builder"}} -> Output: "bob_builder"
    raw_dict_nested = {"user": {"id": "bob_builder"}}
    result = parse_user_id(raw_dict_nested)
    print(f"Nested dict input {raw_dict_nested}: {result}")

    print("\n--- Invalid / Rejected Inputs ---")

    # Scenario 4: Reserved keywords
    # "admin", "root", "system" are rejected
    reserved_input = "user:admin"
    result = parse_user_id(reserved_input)
    print(f"Reserved ID '{reserved_input}': {result} (Expected: None)")

    # Scenario 5: Malformed ID (too short)
    # Regex requires 3-20 characters
    short_id = {"user_id": "ab"}
    result = parse_user_id(short_id)
    print(f"Too short ID {short_id}: {result} (Expected: None)")

    # Scenario 6: Invalid characters
    # Only a-z, 0-9, _, - allowed
    invalid_chars = "user:john@doe"
    result = parse_user_id(invalid_chars)
    print(f"Invalid chars '{invalid_chars}': {result} (Expected: None)")

    # Scenario 7: Unexpected data types (Safe handling)
    # The function handles unexpected types gracefully without crashing
    garbage_input = ["not", "a", "dict"]
    result = parse_user_id(garbage_input)
    print(f"Garbage input {garbage_input}: {result} (Expected: None)")

if __name__ == "__main__":
    main()