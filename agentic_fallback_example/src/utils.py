# This file defines the utility function.
# The agentic fallback will need to read this file to fix the bug in main.py.

def get_greeting(first_name: str, last_name: str) -> str:
    """Returns a greeting string."""
    return f"Hello, {first_name} {last_name}!"
