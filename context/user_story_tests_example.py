"""Example for generating and validating PDD user stories."""

import os
import sys
from pathlib import Path

from pdd.user_story_tests import (
    discover_prompt_files,
    generate_user_story,
    run_user_story_tests,
)

# Check for required API key since user story validation requires LLM calls
api_key = os.environ.get("OPENAI_API_KEY")
if not api_key:
    print("OPENAI_API_KEY not set. Set it to run this example.")
    sys.exit(0)


def main():  # pylint: disable=too-many-locals
    """
    Example of using the user_story_tests module to generate and validate user stories.
    """
    # Setup output directories
    output_dir = Path("./output")
    prompts_dir = output_dir / "prompts"
    stories_dir = output_dir / "user_stories"
    src_dir = output_dir / "src"

    for directory in [prompts_dir, stories_dir, src_dir]:
        directory.mkdir(parents=True, exist_ok=True)

    # 1. Create a dummy prompt file
    prompt_path = prompts_dir / "hello_python.prompt"
    prompt_path.write_text(
        "# Hello World Prompt\n"
        "## Covers\n"
        "- R1: The generated code must print hello world.\n\n"
        "Write a Python function that prints hello world.",
        encoding="utf-8",
    )

    # 2. Discover prompt files
    print("Discovering prompt files...")
    discovered_prompts = discover_prompt_files(str(prompts_dir))
    print(f"Found prompts: {[p.name for p in discovered_prompts]}\n")

    # 3. Generate a user story based on the prompt
    # This uses a deterministic template or an LLM if available to write the story.
    print("Generating user story...")
    success, message, cost, model, story_path, linked_refs = generate_user_story(
        prompt_files=[str(prompt_path)],
        stories_dir=str(stories_dir),
        prompts_dir=str(prompts_dir),
        strength=0.0,      # Use low strength for faster/cheaper generation if LLM is used
        temperature=0.0,
        time=0.25,
        verbose=True,
    )

    print(f"Success: {success}")
    print(f"Message: {message}")
    print(f"Cost: ${cost:.6f}")
    print(f"Model: {model}")
    print(f"Generated Story Path: {story_path}")
    print(f"Linked Prompts: {linked_refs}\n")

    # 4. Run user story validation tests
    # This checks if the story requires changes to the prompt files.
    print("Running user story tests...")
    all_passed, results, total_cost, test_model = run_user_story_tests(
        prompts_dir=str(prompts_dir),
        stories_dir=str(stories_dir),
        strength=0.0,
        temperature=0.0,
        time=0.25,
        verbose=False,
        quiet=False,
        fail_fast=False,
    )

    print(f"\nAll Passed: {all_passed}")
    print(f"Total Validation Cost: ${total_cost:.6f}")
    print(f"Model Used: {test_model}")
    print("Validation Results:")
    for res in results:
        print(
            f" - Story: {res['story']}, Passed: {res['passed']}, "
            f"Changes Detected: {len(res['changes'])}"
        )


if __name__ == "__main__":
    main()
