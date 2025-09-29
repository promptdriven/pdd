# This file has a bug that can only be fixed by understanding utils.py
from utils import get_greeting

def create_user_greeting() -> str:
    """Creates a greeting for a user."""
    # 'first_name' and 'last_name', as expected by the definition in utils.py.
    return get_greeting(first_name="John", last_name="Doe")

if __name__ == "__main__":
    print(create_user_greeting())