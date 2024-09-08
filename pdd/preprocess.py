import os
import re
import subprocess
from typing import List, Tuple
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
    return prompt.rstrip()  # Remove trailing whitespace only

def process_backtick_includes(text: str, recursive: bool) -> str:
    """
    Process includes within triple backticks in the text.

    :param text: The input text containing backtick includes.
    :param recursive: Whether to recursively preprocess included content.
    :return: The text with includes processed.
    """
    pattern = r"```<(.+?)>```"
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
        full_match = match.group(0)
        tag = match.group(1)
        content = match.group(2) if match.group(2) else ""
        
        if tag == 'include':
            file_path = get_file_path(content.strip())
            console.print(f"Processing XML include: [cyan]{file_path}[/cyan]")
            try:
                with open(file_path, 'r') as file:
                    included_content = file.read()
                    if recursive:
                        included_content = preprocess(included_content, recursive, False)
                    return included_content
            except FileNotFoundError:
                console.print(f"[bold red]Warning:[/bold red] File not found: {file_path}")
                return ''
        elif tag == 'pdd':
            return ''  # Remove comment tags, preserving surrounding whitespace
        elif tag == 'shell':
            command = content.strip()
            console.print(f"Executing shell command: [cyan]{command}[/cyan]")
            try:
                result = subprocess.run(command, shell=True, check=True, capture_output=True, text=True)
                return result.stdout  # Return the output as-is, preserving newlines
            except subprocess.CalledProcessError as e:
                console.print(f"[bold red]Error:[/bold red] Shell command failed: {e}")
                return f"Error: {e}"
        else:
            return full_match  # Return the original match for any other tags

    # Process only specific tags, without assuming or adding closing tags
    pattern = r'<(include|pdd|shell)(?:\s+[^>]*)?(?:>(.*?)</\1>|/>|>)'
    return re.sub(pattern, process_tag, text, flags=re.DOTALL)

def get_file_path(file_name: str) -> str:
    """
    Get the full file path based on PDD_PATH environment variable.

    :param file_name: The name of the file to locate.
    :return: The full path to the file.
    """
    pdd_path = os.getenv('PDD_PATH', '')
    return os.path.join(pdd_path, file_name)

def double_curly(text: str, exclude_keys: List[str] = None) -> str:
    """
    Double the curly brackets in the text, excluding specified keys.

    :param text: The input text with single curly brackets.
    :param exclude_keys: List of keys to exclude from doubling.
    :return: The text with doubled curly brackets.
    """
    console.print("Doubling curly brackets")
    if exclude_keys is None:
        exclude_keys = []
    
    def replace_curly(match):
        key = match.group(1)
        if key in exclude_keys:
            return f"{{{key}}}"
        return f"{{{{{key}}}}}"
    
    return re.sub(r'\{([^{}]+)\}', replace_curly, text)
