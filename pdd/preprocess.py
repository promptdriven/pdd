import os
import re
import subprocess
from typing import List
from rich import print
from rich.console import Console
from rich.panel import Panel

console = Console()

def preprocess(prompt: str, recursive: bool = False, double_curly_brackets: bool = True, exclude_keys: List[str] = None) -> str:
    """
    Preprocess the given prompt by handling includes, specific tags, and doubling curly brackets.

    :param prompt: The input text to preprocess.
    :param recursive: Whether to recursively preprocess included content.
    :param double_curly_brackets: Whether to double curly brackets in the text.
    :param exclude_keys: List of keys to exclude from curly bracket doubling.
    :return: The preprocessed text.
    """
    console.print(Panel("Starting preprocessing", style="bold green"))

    # Process includes in triple backticks
    prompt = process_backtick_includes(prompt, recursive)

    # Process specific tags without adding closing tags
    prompt = process_specific_tags(prompt, recursive)

    # Double curly brackets if needed
    if double_curly_brackets:
        prompt = double_curly(prompt, exclude_keys)

    console.print(Panel("Preprocessing complete", style="bold green"))
    return prompt


def process_backtick_includes(text: str, recursive: bool) -> str:
    """
    Process includes within triple backticks in the text.

    :param text: The input text containing backtick includes.
    :param recursive: Whether to recursively preprocess included content.
    :return: The text with includes processed.
    """
    pattern = r"```<(.*?)>```"
    matches = re.findall(pattern, text)

    for match in matches:
        console.print(f"Processing include: [cyan]{match}[/cyan]")
        file_path = get_file_path(match)
        try:
            with open(file_path, 'r') as file:
                content = file.read()
                if recursive:
                    content = preprocess(content, recursive, False)
                text = text.replace(f"```<{match}>```", f"```{content}```")
        except FileNotFoundError:
            console.print(f"[bold red]Warning:[/bold red] File not found: {file_path}")

    return text


def process_specific_tags(text: str, recursive: bool) -> str:
    """
    Process specific tags in the text without adding closing tags.

    :param text: The input text containing specific tags.
    :param recursive: Whether to recursively preprocess included content.
    :return: The text with specific tags processed.
    """
    def process_tag(match: re.Match) -> str:
        pre_whitespace = match.group(1)
        tag = match.group(2)
        content = match.group(3) if match.group(3) else ""
        post_whitespace = match.group(4)

        if tag == 'include':
            file_path = get_file_path(content.strip())
            console.print(f"Processing XML include: [cyan]{file_path}[/cyan]")
            try:
                with open(file_path, 'r') as file:
                    included_content = file.read()
                    if recursive:
                        included_content = preprocess(included_content, recursive, False)
                    return pre_whitespace + included_content + post_whitespace
            except FileNotFoundError:
                console.print(f"[bold red]Warning:[/bold red] File not found: {file_path}")
                return pre_whitespace + post_whitespace
        elif tag == 'pdd':
            return pre_whitespace + post_whitespace
        elif tag == 'shell':
            command = content.strip()
            console.print(f"Executing shell command: [cyan]{command}[/cyan]")
            try:
                result = subprocess.run(command, shell=True, check=True, capture_output=True, text=True)
                return pre_whitespace + result.stdout + post_whitespace
            except subprocess.CalledProcessError as e:
                console.print(f"[bold red]Error:[/bold red] Shell command failed: {e}")
                return pre_whitespace + f"Error: {e}" + post_whitespace
        else:
            return match.group(0)  # Return the original match for any other tags

    # Process only specific tags, capturing whitespace around them
    pattern = r'(\s*)<(include|pdd|shell)(?:\s+[^>]*)?(?:>(.*?)</\2>|/|>)(\s*)'
    return re.sub(pattern, process_tag, text, flags=re.DOTALL)


def get_file_path(file_name: str) -> str:
    """
    Get the full file path based on the current directory ('./').

    :param file_name: The name of the file to locate.
    :return: The full path to the file.
    """
    pdd_path = './'  # Using './' as the base path
    return os.path.join(pdd_path, file_name)


def double_curly(text: str, exclude_keys: List[str] = None) -> str:
    """
    Double the curly brackets in the text, excluding specified keys.
    Supports nested curly brackets and handles all code blocks uniformly.

    :param text: The input text with single curly brackets.
    :param exclude_keys: List of keys to exclude from doubling.
    :return: The text with doubled curly brackets.
    """
    console.print("Doubling curly brackets")
    if exclude_keys is None:
        exclude_keys = []

    # console.print(f"Before doubling:\n{text}")

    # Define the pattern for all code blocks (e.g., ```javascript, ```json)
    code_pattern = r"```[\w]*\n[\s\S]*?```"

    # Split the text into code and non-code segments
    parts = re.split(f"({code_pattern})", text)

    processed_parts = []
    placeholder_mapping = {}
    placeholder_prefix_excl = "__EXCLUDE_KEY_PLACEHOLDER_"
    placeholder_suffix = "__"
    placeholder_prefix_empty = "__EMPTY_BRACE_PLACEHOLDER_"

    placeholder_counter = 0

    for part in parts:
        if re.match(code_pattern, part):
            # It's a code block; process separately
            console.print("Processing code block for curly brackets")
            first_line_end = part.find('\n') + 1
            code_content = part[first_line_end:-3]  # Exclude the last ```
            # Double curly brackets inside the code block
            code_content = re.sub(r'(?<!{){(?!{)', '{{', code_content)
            code_content = re.sub(r'(?<!})}(?!})', '}}', code_content)
            # Reconstruct the code block
            processed_part = part[:first_line_end] + code_content + part[-3:]
            processed_parts.append(processed_part)
        else:
            # It's a non-code segment
            temp_part = part

            # Step 1: Protect excluded keys by replacing {exclude_key} with placeholders
            for key in exclude_keys:
                pattern_excl = r'\{' + re.escape(key) + r'\}'
                placeholder_excl = f"{placeholder_prefix_excl}{placeholder_counter}{placeholder_suffix}"
                temp_part = re.sub(pattern_excl, placeholder_excl, temp_part)
                placeholder_mapping[placeholder_excl] = f"{{{key}}}"
                placeholder_counter += 1

            # Step 2: Protect empty braces '{}' by replacing with placeholders
            pattern_empty = r'\{\}'
            placeholder_empty = f"{placeholder_prefix_empty}{placeholder_counter}{placeholder_suffix}"
            temp_part = re.sub(pattern_empty, placeholder_empty, temp_part)
            placeholder_mapping[placeholder_empty] = '{{}}'
            placeholder_counter += 1

            # Step 3: Replace single '{' with '{{' and '}' with '}}'
            temp_part = re.sub(r'(?<!{){(?!{)', '{{', temp_part)
            temp_part = re.sub(r'(?<!})}(?!})', '}}', temp_part)

            # Step 4: Restore excluded keys from placeholders
            for placeholder, original in placeholder_mapping.items():
                if original != '{{}}':
                    temp_part = temp_part.replace(placeholder, original)

            # Step 5: Restore empty braces from placeholders
            for placeholder, original in placeholder_mapping.items():
                if original == '{{}}':
                    temp_part = temp_part.replace(placeholder, original)

            processed_parts.append(temp_part)

    # Reconstruct the full text after processing
    text = ''.join(processed_parts)

    # console.print(f"After doubling:\n{text}")
    return text
