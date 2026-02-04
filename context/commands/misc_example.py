#!/usr/bin/env python3
"""
Example demonstrating how to use the pdd.commands.misc module.

This module provides the 'preprocess' Click command for preprocessing prompt files
before they are used with LLMs. The command handles includes, comments, shell commands,
web scraping, and curly bracket doubling.

The preprocess command is a local operation (no LLM API calls), so it returns
a dummy cost tuple (processed_prompt, 0.0, "local") for callback compatibility.
"""

import os
import click
from click.testing import CliRunner
from pdd.commands.misc import preprocess


def setup_example_files():
    """
    Create example prompt files for demonstrating the preprocess command.
    
    Creates:
        - ./output/example_prompt.prompt: A sample prompt file with various directives
        - ./output/included_content.txt: A file to be included via <include> tag
    """
    os.makedirs("./output", exist_ok=True)
    
    # Create a file that will be included
    included_content = """This is included content from an external file.
It demonstrates the <include> functionality of the preprocessor.
"""
    with open("./output/included_content.txt", "w") as f:
        f.write(included_content)
    
    # Create the main prompt file with various preprocessing directives
    prompt_content = """% You are an expert Python developer.

% This is a PDD comment that will be removed during preprocessing.
<pdd>This comment block will also be removed.</pdd>

% Include external content:
<include>./output/included_content.txt</include>

% Template variables with single curly brackets:
The model is {model} and temperature is {temperature}.

% Code block example:
```python
def example():
    data = {"key": "value"}
    return data
```

% Generate a Python function that calculates factorial.
"""
    with open("./output/example_prompt.prompt", "w") as f:
        f.write(prompt_content)
    
    print("Created example files in ./output/")


def example_basic_preprocess():
    """
    Example 1: Basic preprocessing of a prompt file.
    
    This demonstrates the simplest usage - just preprocessing a prompt file
    with default settings. The output is saved to a specified location.
    
    Command equivalent:
        pdd preprocess ./output/example_prompt.prompt --output ./output/preprocessed_basic.prompt
    
    Returns:
        CliRunner.Result: The result of invoking the preprocess command
    """
    print("\n" + "="*60)
    print("Example 1: Basic Preprocessing")
    print("="*60)
    
    runner = CliRunner()
    
    # Create a mock context object that preprocess expects
    @click.group()
    @click.pass_context
    def cli(ctx):
        ctx.ensure_object(dict)
        ctx.obj["quiet"] = False
        ctx.obj["verbose"] = False
        ctx.obj["strength"] = 0.5
        ctx.obj["temperature"] = 0.0
    
    cli.add_command(preprocess)
    
    result = runner.invoke(cli, [
        "preprocess",
        "./output/example_prompt.prompt",
        "--output", "./output/preprocessed_basic.prompt"
    ])
    
    print(f"Exit code: {result.exit_code}")
    print(f"Output: {result.output}")
    
    if os.path.exists("./output/preprocessed_basic.prompt"):
        with open("./output/preprocessed_basic.prompt", "r") as f:
            print(f"\nPreprocessed content:\n{f.read()}")
    
    return result


def example_xml_preprocessing():
    """
    Example 2: Preprocessing with XML delimiter insertion.
    
    The --xml flag inserts XML delimiters for better structure in long/complex
    prompt files. This is minimal preprocessing - only XML delimiters are added.
    
    Command equivalent:
        pdd preprocess ./output/example_prompt.prompt --xml --output ./output/preprocessed_xml.prompt
    
    Returns:
        CliRunner.Result: The result of invoking the preprocess command
    """
    print("\n" + "="*60)
    print("Example 2: XML Delimiter Preprocessing")
    print("="*60)
    
    runner = CliRunner()
    
    @click.group()
    @click.pass_context
    def cli(ctx):
        ctx.ensure_object(dict)
        ctx.obj["quiet"] = False
        ctx.obj["verbose"] = True  # Enable verbose for XML tagging details
        ctx.obj["strength"] = 0.5
        ctx.obj["temperature"] = 0.0
    
    cli.add_command(preprocess)
    
    result = runner.invoke(cli, [
        "preprocess",
        "./output/example_prompt.prompt",
        "--xml",
        "--output", "./output/preprocessed_xml.prompt"
    ])
    
    print(f"Exit code: {result.exit_code}")
    print(f"Output: {result.output}")
    
    return result


def example_double_curly_brackets():
    """
    Example 3: Preprocessing with curly bracket doubling.
    
    The --double flag doubles single curly brackets (e.g., {var} becomes {{var}}).
    This is useful when preparing prompts for systems that use double brackets
    for template variables.
    
    The --exclude option specifies keys that should NOT be doubled.
    Only exact matches are excluded (e.g., --exclude model excludes {model}
    but not {model_name}).
    
    Command equivalent:
        pdd preprocess ./output/example_prompt.prompt --double --exclude model --exclude temperature --output ./output/preprocessed_double.prompt
    
    Returns:
        CliRunner.Result: The result of invoking the preprocess command
    """
    print("\n" + "="*60)
    print("Example 3: Curly Bracket Doubling with Exclusions")
    print("="*60)
    
    runner = CliRunner()
    
    @click.group()
    @click.pass_context
    def cli(ctx):
        ctx.ensure_object(dict)
        ctx.obj["quiet"] = False
        ctx.obj["verbose"] = False
        ctx.obj["strength"] = 0.5
        ctx.obj["temperature"] = 0.0
    
    cli.add_command(preprocess)
    
    result = runner.invoke(cli, [
        "preprocess",
        "./output/example_prompt.prompt",
        "--double",
        "--exclude", "model",
        "--exclude", "temperature",
        "--output", "./output/preprocessed_double.prompt"
    ])
    
    print(f"Exit code: {result.exit_code}")
    print(f"Output: {result.output}")
    
    if os.path.exists("./output/preprocessed_double.prompt"):
        with open("./output/preprocessed_double.prompt", "r") as f:
            content = f.read()
            print(f"\nPreprocessed content (note doubled brackets):")
            print(content)
    
    return result


def example_recursive_preprocessing():
    """
    Example 4: Recursive preprocessing of includes.
    
    The --recursive flag causes the preprocessor to recursively process
    all included files, resolving nested includes.
    
    Command equivalent:
        pdd preprocess ./output/example_prompt.prompt --recursive --output ./output/preprocessed_recursive.prompt
    
    Returns:
        CliRunner.Result: The result of invoking the preprocess command
    """
    print("\n" + "="*60)
    print("Example 4: Recursive Preprocessing")
    print("="*60)
    
    runner = CliRunner()
    
    @click.group()
    @click.pass_context
    def cli(ctx):
        ctx.ensure_object(dict)
        ctx.obj["quiet"] = False
        ctx.obj["verbose"] = False
        ctx.obj["strength"] = 0.5
        ctx.obj["temperature"] = 0.0
    
    cli.add_command(preprocess)
    
    result = runner.invoke(cli, [
        "preprocess",
        "./output/example_prompt.prompt",
        "--recursive",
        "--output", "./output/preprocessed_recursive.prompt"
    ])
    
    print(f"Exit code: {result.exit_code}")
    print(f"Output: {result.output}")
    
    return result


def example_combined_options():
    """
    Example 5: Combining multiple preprocessing options.
    
    This demonstrates using multiple flags together:
    - --recursive: Process includes recursively
    - --double: Double curly brackets
    - --exclude: Exclude specific keys from doubling
    
    Command equivalent:
        pdd preprocess ./output/example_prompt.prompt --recursive --double --exclude model --output ./output/preprocessed_combined.prompt
    
    Returns:
        CliRunner.Result: The result of invoking the preprocess command
    """
    print("\n" + "="*60)
    print("Example 5: Combined Preprocessing Options")
    print("="*60)
    
    runner = CliRunner()
    
    @click.group()
    @click.pass_context
    def cli(ctx):
        ctx.ensure_object(dict)
        ctx.obj["quiet"] = False
        ctx.obj["verbose"] = False
        ctx.obj["strength"] = 0.5
        ctx.obj["temperature"] = 0.0
    
    cli.add_command(preprocess)
    
    result = runner.invoke(cli, [
        "preprocess",
        "./output/example_prompt.prompt",
        "--recursive",
        "--double",
        "--exclude", "model",
        "--output", "./output/preprocessed_combined.prompt"
    ])
    
    print(f"Exit code: {result.exit_code}")
    print(f"Output: {result.output}")
    
    return result


if __name__ == "__main__":
    """
    Main entry point demonstrating all preprocess command examples.
    
    The preprocess command supports the following options:
    
    Arguments:
        PROMPT_FILE (str): Path to the prompt file to preprocess (must exist)
    
    Options:
        --output PATH: Where to save the preprocessed prompt file.
                      Can be a file path or directory.
                      Default: <basename>_<language>_preprocessed.prompt
        
        --xml: Insert XML delimiters for structure (minimal preprocessing).
               When set, only XML delimiter insertion is performed.
        
        --recursive: Recursively preprocess all included files.
                    Resolves nested <include> tags.
        
        --double: Double single curly brackets in the prompt.
                 Converts {var} to {{var}} for template systems.
        
        --exclude KEY: Keys to exclude from curly bracket doubling.
                      Can be specified multiple times.
                      Only exact matches are excluded.
    
    Returns:
        Tuple[str, float, str]: A tuple containing:
            - processed_prompt (str): The preprocessed prompt content
            - total_cost (float): Always 0.0 (local operation, no LLM cost)
            - model_name (str): Always "local" (no LLM used)
    
    Note:
        This is a local operation that does not call any LLM APIs.
        The cost tuple is returned for callback compatibility with
        other PDD commands that do use LLMs.
    """
    print("PDD Preprocess Command Examples")
    print("="*60)
    print("\nThe preprocess command prepares prompt files for LLM use by:")
    print("  - Processing <include> tags to embed external file content")
    print("  - Removing <pdd> comment blocks")
    print("  - Executing <shell> commands and including output")
    print("  - Scraping <web> URLs and including markdown content")
    print("  - Optionally inserting XML delimiters for structure")
    print("  - Optionally doubling curly brackets for template systems")
    
    # Setup example files
    setup_example_files()
    
    # Run all examples
    example_basic_preprocess()
    example_xml_preprocessing()
    example_double_curly_brackets()
    example_recursive_preprocessing()
    example_combined_options()
    
    print("\n" + "="*60)
    print("All examples completed!")
    print("Check ./output/ directory for generated files.")
    print("="*60)
