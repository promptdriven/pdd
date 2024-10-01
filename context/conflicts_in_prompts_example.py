from pdd.conflicts_in_prompts import conflicts_in_prompts
from rich import print as rprint

def main() -> None:
    """
    Main function to demonstrate the usage of the conflicts_in_prompts function.
    It defines two example prompts, calls the function, and prints the results.
    """
    # Example prompts
    prompt1: str = """You are an expert Python engineer and Firebase specialist working on the PDD Cloud project. Your goal is to write the `auth_helpers.py` module, which provides authentication helper functions for user validation in Firebase Cloud Functions. This module will be placed in the `backend/functions/utils/` directory.
"""

    prompt2: str = """You are an expert Python engineer and Firebase specialist. Your task is to write the `db_helpers.py` module for our Firebase Cloud Functions backend. This module provides utility functions for common Firestore database operations to be used across various Cloud Functions.
    
The `db_helpers.py` module should include the following:

1. **Firestore Initialization**:
   - Import and initialize the Firestore client using the Firebase Admin SDK.
   - Ensure that the Firestore client is properly configured for use in Cloud Functions.
"""

    # Call the function
    conflicts, total_cost, model_name = conflicts_in_prompts(prompt1, prompt2, strength=0.9, temperature=0)

    # Print the results
    rprint("[bold]Conflicts found:[/bold]")
    for conflict in conflicts:
        rprint(f"Description: {conflict['description']}")
        rprint(f"Explanation: {conflict['explanation']}")
        rprint(f"Suggestion for prompt1: {conflict['suggestion1']}")
        rprint(f"Suggestion for prompt2: {conflict['suggestion2']}")
        rprint("---")

    rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
    rprint(f"[bold]Model used:[/bold] {model_name}")

if __name__ == "__main__":
    main()