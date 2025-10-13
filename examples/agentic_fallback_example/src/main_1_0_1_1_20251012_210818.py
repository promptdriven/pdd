from utils import get_greeting


def create_user_greeting() -> str:
    """Creates a greeting for a user."""
    return get_greeting("John", "Doe")


if __name__ == "__main__":
    print(create_user_greeting())
