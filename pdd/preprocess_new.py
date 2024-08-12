import os
import re
import subprocess
from bs4 import BeautifulSoup
from rich import print
from rich.console import Console
from rich.panel import Panel

console = Console()

def preprocess(prompt: str, recursive: bool = False, double_curly_brackets: bool = True) -> str:
    """
    Preprocess the given prompt by handling includes, XML-like tags, and doubling curly brackets.

    :param prompt: The input text to preprocess.
    :param recursive: Whether to recursively preprocess included content.
    :param double_curly_brackets: Whether to double curly brackets in the text.
    :return: The preprocessed text.
    """
    console.print(Panel("Starting preprocessing", style="bold green"))

    # Process includes in triple backticks
    prompt = process_backtick_includes(prompt, recursive)

    # Process XML-like tags
    soup = BeautifulSoup(prompt, 'html.parser')
    prompt = process_xml_tags(soup, recursive)

    # Double curly brackets if needed
    if double_curly_brackets:
        prompt = double_curly(prompt)

    console.print(Panel("Preprocessing complete", style="bold green"))
    return prompt

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
        try:
            with open(match, 'r') as file:
                content = file.read()
                if recursive:
                    content = preprocess(content, recursive, False)
                text = text.replace(f"```<{match}>```", f"```{content}```")
        except FileNotFoundError:
            console.print(f"[bold red]Warning:[/bold red] File not found: {match}")
    
    return text

def process_xml_tags(soup: BeautifulSoup, recursive: bool) -> str:
    """
    Process only specific XML-like tags in the BeautifulSoup object.

    :param soup: The BeautifulSoup object containing XML-like tags.
    :param recursive: Whether to recursively preprocess included content.
    :return: The text with specific XML-like tags processed.
    """
    # Process include tags
    for include in soup.find_all('include'):
        file_path = include.string.strip()
        console.print(f"Processing XML include: [cyan]{file_path}[/cyan]")
        try:
            with open(file_path, 'r') as file:
                content = file.read()
                if recursive:
                    content = preprocess(content, recursive, False)
                new_tag = soup.new_tag("div")
                new_tag.string = content
                include.replace_with(new_tag)
        except FileNotFoundError:
            console.print(f"[bold red]Warning:[/bold red] File not found: {file_path}")

    # Remove comment tags
    for comment in soup.find_all('pdd'):
        comment.extract()

    # Process shell tags
    for shell in soup.find_all('shell'):
        command = shell.string.strip()
        console.print(f"Executing shell command: [cyan]{command}[/cyan]")
        try:
            result = subprocess.run(command, shell=True, check=True, capture_output=True, text=True)
            new_tag = soup.new_tag("div")
            new_tag.string = result.stdout
            shell.replace_with(new_tag)
        except subprocess.CalledProcessError as e:
            console.print(f"[bold red]Error:[/bold red] Shell command failed: {e}")
            new_tag = soup.new_tag("div")
            new_tag.string = f"Error: {e}"
            shell.replace_with(new_tag)

    # Convert the modified soup back to a string, preserving other tags
    return ''.join(str(child) for child in soup.contents)

def double_curly(text: str) -> str:
    """
    Double the curly brackets in the text.

    :param text: The input text with single curly brackets.
    :return: The text with doubled curly brackets.
    """
    console.print("Doubling curly brackets")
    return re.sub(r'(?<!\{)\{(?!\{)', '{{', re.sub(r'(?<!\})\}(?!\})', '}}', text))

# Example usage:
if __name__ == "__main__":
    sample_prompt = """
    Here's an include: ```<Makefile>```
    <include>TODO.md</include>
    <pdd>This is a comment that will be removed</pdd>
    <shell>echo "Hello, World!"</shell>
    This is a {{variable}} that will be doubled.
    """
    
    result = preprocess(sample_prompt)
    print(Panel(result, title="Preprocessed Prompt", expand=False))
