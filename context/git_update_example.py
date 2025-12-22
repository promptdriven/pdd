import os
from pdd import DEFAULT_STRENGTH
from pdd.git_update import git_update


def main() -> None:
    """
    Demonstrate the usage of the git_update function.

    The function reads modified code, restores the original from Git HEAD,
    updates the prompt (via agentic or legacy path), and restores the modified code.

    Routing logic:
    - If simple=False AND prompt_file is provided AND agents are available:
      Uses run_agentic_update() for AI-powered prompt updating
    - Otherwise: Falls back to legacy update_prompt()
    """
    # Define input parameters
    name = 'fix_error_loop'
    prompt_file: str = f"prompts/{name}_python.prompt"

    # Load input prompt content from file
    with open(prompt_file, "r") as file:
        input_prompt = file.read()

    modified_code_file: str = f"pdd/{name}.py"
    strength: float = DEFAULT_STRENGTH  # Strength parameter for the LLM (0.0 to 1.0)
    temperature: float = 0  # Temperature parameter for the LLM

    try:
        # Call the git_update function
        # - simple=False: Allow agentic path if available
        # - quiet=False: Show output
        # - prompt_file: Required for agentic path to update the prompt file directly
        result = git_update(
            input_prompt=input_prompt,
            modified_code_file=modified_code_file,
            strength=strength,
            temperature=temperature,
            verbose=True,
            simple=False,   # Set True to force legacy update_prompt() path
            quiet=False,    # Set True to suppress non-error output
            prompt_file=prompt_file  # Required for agentic path
        )

        if result:
            modified_prompt, total_cost, model_name = result
            print(f"Modified Prompt: {modified_prompt}")
            print(f"Total Cost: ${total_cost:.6f}")  # Cost in dollars
            print(f"Model/Provider: {model_name}")
        else:
            print("Failed to update the prompt and code.")

        # Save the modified prompt to file (if using legacy path)
        # Note: Agentic path updates the file directly, so this may be redundant
        if modified_prompt:
            with open(prompt_file, "w") as file:
                file.write(modified_prompt)
    except ValueError as e:
        print(f"Input error: {e}")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")

if __name__ == "__main__":
    main()