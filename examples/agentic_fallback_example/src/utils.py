def get_greeting(first_name: str, last_name: str) -> str:
    """
    Creates a greeting message for a user.

    Args:
        first_name: The user's first name
        last_name: The user's last name

    Returns:
        A greeting string containing Hello and the user's full name
    """
    return f"Hello, {first_name} {last_name}!"