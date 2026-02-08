import sys
import os

# Add the parent directory to sys.path to allow importing the module
# This assumes the example script is in a subdirectory (e.g., 'examples/')
# and the module is in the parent or 'src/' directory.
current_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(current_dir)
sys.path.append(parent_dir)

# Import the function from the module
# Note: Replace 'src.user_id_parser' with the actual module path if different
try:
    from src.user_id_parser import parse_user_id
except ImportError:
    # Fallback for when the script is run directly alongside the module
    from user_id_parser import parse_user_id

def main():
    print("--- Testing parse_user_id ---")

    # 1. Valid String Input
    # Format: "user:<id>"
    raw_string = "user:12345"
    result_str = parse_user_id(raw_string)
    print(f"Input: {raw_string!r} -> Output: {result_str!r}")

    # 2. Valid Dictionary Input
    # Format: {"user_id": "<id>"}
    raw_dict = {"user_id": "  alice_wonderland  "}
    result_dict = parse_user_id(raw_dict)
    print(f"Input: {raw_dict!r} -> Output: {result_dict!r}")

    # 3. Invalid Inputs (Should return None)
    invalid_inputs = [
        "admin:999",          # Wrong prefix
        {"id": "555"},        # Wrong dictionary key
        12345,                # Wrong type (int)
        None,                 # NoneType
        ["user:list"]         # List type
    ]

    print("\n--- Testing Invalid Inputs ---")
    for invalid in invalid_inputs:
        res = parse_user_id(invalid)
        print(f"Input: {invalid!r} -> Output: {res!r}")

if __name__ == "__main__":
    main()