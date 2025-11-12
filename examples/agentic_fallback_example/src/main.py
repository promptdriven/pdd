from utils import get_greeting


def create_user_greeting(first_name: str, last_name: str) -> str:
    """Creates a greeting for a user."""
    return get_greeting(first_name, last_name)


if __name__ == "__main__":
    print(create_user_greeting("John", "Doe"))
