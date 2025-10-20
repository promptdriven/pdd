from utils import get_greeting


def create_user_greeting() -> str:
    """Creates a greeting for John Doe.

    Returns:
        A greeting string for John Doe.
    """
    first_name = "John"
    last_name = "Doe"
    return get_greeting(first_name, last_name)


if __name__ == "__main__":
    print(create_user_greeting())
