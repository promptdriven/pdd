"""
Tool definitions for PDD MCP Server.

This module defines the tools that will be exposed by the MCP server, corresponding
to commands supported by the PDD CLI. Each tool has a name, description, and a JSON
schema that defines its input parameters.
"""

import mcp.types as types
from typing import Dict, List

# Generate Command Tool
#----------------------
PDD_GENERATE = types.Tool(
    name="pdd-generate",
    description="Generate code from a prompt file",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "The filename of the prompt file used to generate the code"
            },
            "output": {
                "type": "string",
                "description": "Specify where to save the generated code. If not provided, uses default naming based on the prompt file"
            },
            "strength": {
                "type": "number",
                "description": "Set the strength of the AI model (0.0 to 1.0, default is 0.5)"
            },
            "temperature": {
                "type": "number",
                "description": "Set the temperature of the AI model (default is 0.0)"
            },
            "local": {
                "type": "boolean",
                "description": "Run the generation locally instead of in the cloud"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            },
            "verbose": {
                "type": "boolean",
                "description": "Increase output verbosity for more detailed information"
            },
            "quiet": {
                "type": "boolean",
                "description": "Decrease output verbosity for minimal information"
            }
        },
        "required": ["prompt_file"]
    }
)

# Test Command Tool
#------------------
PDD_TEST = types.Tool(
    name="pdd-test",
    description="Generate test files for a source file",
    inputSchema={
        "type": "object",
        "properties": {
            "source_file": {
                "type": "string",
                "description": "The source file to generate tests for"
            },
            "prompt_file": {
                "type": "string",
                "description": "Optional prompt file to guide test generation"
            },
            "output": {
                "type": "string",
                "description": "Specify where to save the generated tests"
            },
            "strength": {
                "type": "number",
                "description": "Set the strength of the AI model (0.0 to 1.0, default is 0.5)"
            },
            "temperature": {
                "type": "number",
                "description": "Set the temperature of the AI model (default is 0.0)"
            },
            "local": {
                "type": "boolean",
                "description": "Run the generation locally instead of in the cloud"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            },
            "verbose": {
                "type": "boolean",
                "description": "Increase output verbosity for more detailed information"
            },
            "quiet": {
                "type": "boolean",
                "description": "Decrease output verbosity for minimal information"
            }
        },
        "required": ["source_file"]
    }
)

# Fix Command Tool
#-----------------
PDD_FIX = types.Tool(
    name="pdd-fix",
    description="Fix issues in a source file using AI",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "The prompt file describing the code to be fixed"
            },
            "source_file": {
                "type": "string",
                "description": "The source file to be fixed"
            },
            "test_file": {
                "type": "string",
                "description": "Optional test file to validate fixes"
            },
            "output_code": {
                "type": "string",
                "description": "Where to save the fixed code"
            },
            "output_test": {
                "type": "string",
                "description": "Where to save the fixed tests"
            },
            "verification_program": {
                "type": "string",
                "description": "Program to verify the fix works correctly"
            },
            "loop": {
                "type": "boolean",
                "description": "Keep generating fixes until successful or max attempts reached"
            },
            "max_attempts": {
                "type": "integer",
                "description": "Maximum number of fix attempts (default: 5)"
            },
            "strength": {
                "type": "number",
                "description": "Set the strength of the AI model (0.0 to 1.0, default is 0.5)"
            },
            "temperature": {
                "type": "number",
                "description": "Set the temperature of the AI model (default is 0.0)"
            },
            "local": {
                "type": "boolean",
                "description": "Run the generation locally instead of in the cloud"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            },
            "verbose": {
                "type": "boolean",
                "description": "Increase output verbosity for more detailed information"
            }
        },
        "required": ["prompt_file", "source_file"]
    }
)

# Example Command Tool
#---------------------
PDD_EXAMPLE = types.Tool(
    name="pdd-example",
    description="Generate example code that demonstrates how to use a module",
    inputSchema={
        "type": "object",
        "properties": {
            "source_file": {
                "type": "string",
                "description": "The source file to generate examples for"
            },
            "output": {
                "type": "string",
                "description": "Specify where to save the generated examples"
            },
            "strength": {
                "type": "number",
                "description": "Set the strength of the AI model (0.0 to 1.0, default is 0.5)"
            },
            "temperature": {
                "type": "number",
                "description": "Set the temperature of the AI model (default is 0.0)"
            },
            "local": {
                "type": "boolean",
                "description": "Run the generation locally instead of in the cloud"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            },
            "verbose": {
                "type": "boolean",
                "description": "Increase output verbosity for more detailed information"
            }
        },
        "required": ["source_file"]
    }
)

# Continue Command Tool
#----------------------
PDD_CONTINUE = types.Tool(
    name="pdd-continue",
    description="Continue generation of partially completed output",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "The original prompt file"
            },
            "output_file": {
                "type": "string",
                "description": "The partially generated output file to continue"
            },
            "result_file": {
                "type": "string",
                "description": "Where to save the continued output"
            },
            "strength": {
                "type": "number",
                "description": "Set the strength of the AI model (0.0 to 1.0, default is 0.5)"
            },
            "temperature": {
                "type": "number",
                "description": "Set the temperature of the AI model (default is 0.0)"
            },
            "local": {
                "type": "boolean",
                "description": "Run the generation locally instead of in the cloud"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            },
            "verbose": {
                "type": "boolean",
                "description": "Increase output verbosity for more detailed information"
            }
        },
        "required": ["prompt_file", "output_file"]
    }
)

# Analyze Command Tool
#---------------------
PDD_ANALYZE = types.Tool(
    name="pdd-analyze",
    description="Analyze code to provide insights and recommendations",
    inputSchema={
        "type": "object",
        "properties": {
            "source_file": {
                "type": "string",
                "description": "The source file to analyze"
            },
            "output": {
                "type": "string",
                "description": "Where to save the analysis results"
            },
            "format": {
                "type": "string",
                "enum": ["text", "json", "html", "markdown"],
                "description": "Output format for the analysis (default: markdown)"
            },
            "strength": {
                "type": "number",
                "description": "Set the strength of the AI model (0.0 to 1.0, default is 0.5)"
            },
            "temperature": {
                "type": "number",
                "description": "Set the temperature of the AI model (default is 0.0)"
            },
            "local": {
                "type": "boolean",
                "description": "Run the analysis locally instead of in the cloud"
            },
            "verbose": {
                "type": "boolean",
                "description": "Increase output verbosity for more detailed information"
            }
        },
        "required": ["source_file"]
    }
)

# Collection of all PDD tools
PDD_TOOLS = [
    PDD_GENERATE,
    PDD_TEST,
    PDD_FIX,
    PDD_EXAMPLE,
    PDD_CONTINUE,
    PDD_ANALYZE
]

# Dictionary mapping tool names to tool objects for easy lookup
PDD_TOOLS_DICT: Dict[str, types.Tool] = {tool.name: tool for tool in PDD_TOOLS}

def get_tool_by_name(name: str) -> types.Tool:
    """
    Get a tool definition by name.
    
    Args:
        name: The name of the tool to retrieve
        
    Returns:
        The tool object matching the given name
        
    Raises:
        KeyError: If no tool with the given name exists
    """
    if name in PDD_TOOLS_DICT:
        return PDD_TOOLS_DICT[name]
    raise KeyError(f"No tool defined with name: {name}")