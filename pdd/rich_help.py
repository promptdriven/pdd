"""
Rich help text formatter for PDD CLI commands.

This module provides utilities for creating comprehensive, well-formatted help
text that includes quick reference information, detailed descriptions, examples,
and related commands.
"""
from typing import List, Optional, Dict, Any
from rich.console import Console
from rich.markdown import Markdown
from rich.panel import Panel
from rich.table import Table
from rich import box
from rich.theme import Theme


# Initialize console with custom theme
help_theme = Theme({
    "header": "bold cyan",
    "section": "bold yellow",
    "emphasis": "bold",
    "command": "bold magenta",
    "option": "green",
    "path": "dim blue",
})

console = Console(theme=help_theme)


class RichHelpFormatter:
    """Formats rich help text for CLI commands."""
    
    def __init__(self, command_name: str):
        """Initialize the formatter for a specific command.
        
        Args:
            command_name: Name of the command being documented
        """
        self.command_name = command_name
        self.sections = []
    
    def add_quick_reference(self, synopsis: str, description: str) -> "RichHelpFormatter":
        """Add quick reference section with command synopsis and brief description.
        
        Args:
            synopsis: Brief one-line command synopsis
            description: Short description of what the command does
            
        Returns:
            Self for method chaining
        """
        quick_ref = f"""## Quick Reference

**{synopsis}**

{description}
"""
        self.sections.append(("quick_reference", quick_ref))
        return self
    
    def add_description(self, text: str) -> "RichHelpFormatter":
        """Add detailed description section.
        
        Args:
            text: Detailed description text (markdown supported)
            
        Returns:
            Self for method chaining
        """
        desc = f"""## Description

{text}
"""
        self.sections.append(("description", desc))
        return self
    
    def add_usage(self, usage_text: str) -> "RichHelpFormatter":
        """Add usage section with command syntax.
        
        Args:
            usage_text: Command usage syntax
            
        Returns:
            Self for method chaining
        """
        usage = f"""## Usage

```bash
{usage_text}
```
"""
        self.sections.append(("usage", usage))
        return self
    
    def add_arguments(self, args: List[Dict[str, str]]) -> "RichHelpFormatter":
        """Add arguments section.
        
        Args:
            args: List of argument dictionaries with 'name' and 'description' keys
            
        Returns:
            Self for method chaining
        """
        if not args:
            return self
        
        args_text = "## Arguments\n\n"
        for arg in args:
            args_text += f"- **{arg['name']}**: {arg['description']}\n"
        
        self.sections.append(("arguments", args_text))
        return self
    
    def add_options(self, opts: List[Dict[str, str]]) -> "RichHelpFormatter":
        """Add options section.
        
        Args:
            opts: List of option dictionaries with 'name' and 'description' keys
            
        Returns:
            Self for method chaining
        """
        if not opts:
            return self
        
        opts_text = "## Options\n\n"
        for opt in opts:
            opts_text += f"- **{opt['name']}**: {opt['description']}\n"
        
        self.sections.append(("options", opts_text))
        return self
    
    def add_examples(self, examples: List[Dict[str, str]]) -> "RichHelpFormatter":
        """Add examples section.
        
        Args:
            examples: List of example dictionaries with 'description' and 'command' keys
            
        Returns:
            Self for method chaining
        """
        if not examples:
            return self
        
        examples_text = "## Examples\n\n"
        for i, example in enumerate(examples, 1):
            examples_text += f"{i}. {example['description']}\n```bash\n{example['command']}\n```\n\n"
        
        self.sections.append(("examples", examples_text))
        return self
    
    def add_notes(self, notes: str) -> "RichHelpFormatter":
        """Add important notes section.
        
        Args:
            notes: Notes text (markdown supported)
            
        Returns:
            Self for method chaining
        """
        notes_section = f"""## Important Notes

{notes}
"""
        self.sections.append(("notes", notes_section))
        return self
    
    def add_see_also(self, related_commands: List[str]) -> "RichHelpFormatter":
        """Add see also section with related commands.
        
        Args:
            related_commands: List of related command names
            
        Returns:
            Self for method chaining
        """
        if not related_commands:
            return self
        
        see_also = "## See Also\n\n"
        for cmd in related_commands:
            see_also += f"- `pdd {cmd} --help`\n"
        
        self.sections.append(("see_also", see_also))
        return self
    
    def add_custom_section(self, title: str, content: str) -> "RichHelpFormatter":
        """Add a custom section.
        
        Args:
            title: Section title
            content: Section content (markdown supported)
            
        Returns:
            Self for method chaining
        """
        section = f"""## {title}

{content}
"""
        self.sections.append(("custom", section))
        return self
    
    def format(self) -> str:
        """Format all sections into a complete help text.
        
        Returns:
            Complete formatted help text as markdown string
        """
        # Combine all sections
        help_text = f"# pdd {self.command_name}\n\n"
        for _, section_content in self.sections:
            help_text += section_content + "\n"
        
        return help_text.rstrip()
    
    def render(self) -> None:
        """Render the help text to the console using Rich."""
        help_text = self.format()
        md = Markdown(help_text)
        console.print(md)


def create_rich_help(command_name: str, **sections) -> str:
    """Quick helper to create rich help text.
    
    Args:
        command_name: Name of the command
        **sections: Keyword arguments for different sections
            - quick_ref: tuple of (synopsis, description)
            - description: str
            - usage: str
            - arguments: list of dicts
            - options: list of dicts
            - examples: list of dicts
            - notes: str
            - see_also: list of str
            
    Returns:
        Formatted help text
    """
    formatter = RichHelpFormatter(command_name)
    
    if "quick_ref" in sections:
        synopsis, desc = sections["quick_ref"]
        formatter.add_quick_reference(synopsis, desc)
    
    if "description" in sections:
        formatter.add_description(sections["description"])
    
    if "usage" in sections:
        formatter.add_usage(sections["usage"])
    
    if "arguments" in sections:
        formatter.add_arguments(sections["arguments"])
    
    if "options" in sections:
        formatter.add_options(sections["options"])
    
    if "examples" in sections:
        formatter.add_examples(sections["examples"])
    
    if "notes" in sections:
        formatter.add_notes(sections["notes"])
    
    if "see_also" in sections:
        formatter.add_see_also(sections["see_also"])
    
    return formatter.format()
