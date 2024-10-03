from pdd.conflicts_in_prompts import conflicts_in_prompts
from rich import print as rprint

def main() -> None:
    """
    Main function to demonstrate the use of the conflicts_in_prompts function.
    """
    # Example prompts
    prompt1: str = """You are an expert Python engineer and Firebase specialist working on the PDD Cloud project. Your goal is to write the `auth_helpers.py` module, which provides authentication helper functions for user validation in Firebase Cloud Functions. This module will be placed in the `backend/functions/utils/` directory.

**Requirements:**

- **Functionality**:
  - Implement functions to verify Firebase ID tokens from incoming HTTP requests.
  - Extract user information, such as UID and email, from the verified tokens.
  - Check user permissions or roles as needed.
  - Raise appropriate errors for authentication failures or insufficient permissions.

- **Dependencies**:
  - Use the `firebase_admin` library, specifically `firebase_admin.auth`, for authentication operations.
  - Include any necessary internal modules, such as error handling utilities.

- **Error Handling**:
  - Use standardized error responses for authentication errors.
  - Log unauthorized access attempts securely.

- **Security Best Practices**:
  - Securely handle and validate tokens to prevent unauthorized access.
  - Ensure that no sensitive information is exposed in error messages or logs.

- **Code Structure**:
  - Follow the project's coding standards and conventions.
  - Include docstrings and comments for clarity.
  - Organize the code into reusable functions.

**Include the following dependencies in your code where necessary:**

- `<include>context/error_handling_example.py</include>`: Functions and classes for standardized error handling.

**Instructions:**

- Write the `auth_helpers.py` module code that fulfills the above requirements.
- Make sure to import dependencies correctly, using relative imports for internal modules.
- Ensure that the code is clean, well-documented, and adheres to best practices.

**Deliverable:**

The complete code for `auth_helpers.py`, ready to be integrated into the PDD Cloud project."""
    prompt2: str = """You are an expert Python engineer. Your goal is to write a Python class named `User` that defines the user data model for the PDD Cloud platform.

**Requirements**:

- **Class Definition**:
  - Create a `User` class that encapsulates user-related fields used throughout the backend.
  - The class should be located in `backend/functions/models/user.py`.
  - The class should inherit from `dataclass` for automatic method generation.

- **Fields to Include**:
  - `uid`: `str`
  - `email`: `str`
  - `display_name`: `str`
  - `photo_url`: `str` (optional)
  - `created_at`: `datetime`
  - `last_login_at`: `datetime`
  - `credits`: `int`
  - `contributor_tier`: `str` (options: `'bronze'`, `'silver'`, `'gold'`, `'platinum'`)
  - `bio`: `str` (optional)
  - `github_username`: `str` (optional)
  - `is_admin`: `bool`
  - `settings`: `Dict[str, Any]` containing:
    - `email_notifications`: `bool`
    - `two_factor_auth`: `bool`

- **Methods to Include**:
  - **Initialization**: Constructor that sets default values where appropriate.
  - **Validation Methods**:
    - Ensure all fields meet required formats and constraints.
    - For example, validate email format, contributor tier options, and that credits are non-negative.
  - **Serialization Methods**:
    - `to_dict()`: Converts the user instance into a dictionary suitable for Firestore storage.
    - `from_dict(data: Dict[str, Any])`: Creates a user instance from a dictionary retrieved from Firestore.
  - **Firestore Interaction**:
    - Methods to save, update, and delete user documents in the Firestore `users` collection.
    - Use asynchronous Firestore methods for non-blocking operations.
  - **Credit Management**:
    - `update_credits(amount: int)`: Safely updates the user's credits.
  - **Permission Management**:
    - Methods to check and update user roles and permissions.

- **Imports and Dependencies**:
  - Import necessary modules:
    - `from dataclasses import dataclass, field`
    - `from typing import Dict, Any`
    - `from datetime import datetime`
    - `from firebase_admin import firestore`
  - Utilize utility functions from the `utils` package for Firestore interactions and error handling.
    - Include the following dependency:

<db_helpers_example>
<include>context/db_helpers_example.py</include>
</db_helpers_example>

- **Error Handling**:
  - Implement appropriate try-except blocks to handle exceptions.
  - Use custom exceptions from the `utils/error_handling.py` module.

- **Additional Requirements**:
  - Ensure all methods are well-documented with docstrings explaining their functionality.
  - Follow PEP 8 style guidelines for code style and formatting.
  - Include type hints for all function arguments and return types.
  - Avoid hardcoding any values; use class variables or configurations where necessary.

**Note**: The `User` class should be designed to ensure consistency across the backend and simplify database operations. By centralizing the user data structure, it enhances code maintainability and readability."""

    # Set strength and temperature for the LLM
    strength: float = .9  # Adjust between 0 and 1 for different model strengths
    temperature: float = 0  # Adjust between 0 and 1 for output randomness

    # Call the conflicts_in_prompts function
    changes, total_cost, model_name = conflicts_in_prompts(prompt1, prompt2, strength, temperature)

    # Print the results
    rprint("[bold]Conflict Detection Results:[/bold]")
    rprint(f"Model used: {model_name}")
    rprint(f"Total cost: ${total_cost:.6f}")
    
    if changes:
        rprint("[bold]Suggested Changes:[/bold]")
        for change in changes:
            rprint(f"Prompt: {change['prompt_name']}")
            rprint(f"Instructions: {change['change_instructions']}")
            rprint("---")
    else:
        rprint("No conflicts detected or changes suggested.")

if __name__ == "__main__":
    main()