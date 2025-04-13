"""
Tool definitions for PDD MCP Server.

This module defines the tools that will be exposed by the MCP server, corresponding
to commands supported by the PDD CLI. Each tool has a name, description, and a JSON
schema that defines its input parameters.
"""

import mcp.types as types
from typing import Dict, List

# Common example template for LLMs
LLM_PARAMETER_GUIDANCE = """
IMPORTANT FOR CLAUDE, GPT, AND OTHER LLMs:

CLAUDE CODE SPECIFIC INSTRUCTIONS:
For Claude Code integration, parameters must be wrapped in a "kwargs" JSON string:
✅ CORRECT FORMAT FOR CLAUDE CODE: {"kwargs": "{\\"param1\\": \\"value1\\", \\"param2\\": \\"value2\\"}"}

For direct API calls:
- ALWAYS provide parameters as direct key-value pairs in your tool call
- DO NOT nest parameters under a "kwargs" key
- DO NOT use CLI-style arguments with dashes (like --file=/path/to/file)

✅ CORRECT FORMAT FOR DIRECT API: {"param1": "value1", "param2": "value2"}
❌ INCORRECT FORMAT: {"kwargs": {"param1": "value1"}}
❌ INCORRECT FORMAT: {"kwargs": "--param1 value1 --param2 value2"}
"""

# Generate Command Tool
#----------------------
PDD_GENERATE = types.Tool(
    name="pdd-generate",
    description=f"""Generate code from a prompt file.
{LLM_PARAMETER_GUIDANCE}
Examples:
- ✅ CORRECT FOR CLAUDE CODE: {{"kwargs": "{{\\"prompt_file\\": \\"/path/to/prompt.txt\\", \\"output\\": \\"/path/to/output.py\\"}}"}}
- ✅ CORRECT FOR DIRECT API: {{"prompt_file": "/path/to/prompt.txt", "output": "/path/to/output.py"}}
- ❌ INCORRECT: {{"kwargs": {{"prompt_file": "/path/to/prompt.txt"}}}}
- ❌ INCORRECT: {{"kwargs": "--file=/path/to/prompt.txt"}}

The prompt file should contain instructions for the code you want to generate.""",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "REQUIRED: Full path to the prompt file. Must be provided as a direct parameter, not inside a 'kwargs' object."
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
        "required": ["prompt_file"],
        "additionalProperties": False
    }
)

# Test Command Tool
#------------------
PDD_TEST = types.Tool(
    name="pdd-test",
    description=f"""Generate test files for a source file.
{LLM_PARAMETER_GUIDANCE}    
Examples:
- ✅ CORRECT: {{"source_file": "/path/to/source.py", "prompt_file": "/path/to/prompt.txt"}}
- ❌ INCORRECT: {{"kwargs": {{"source_file": "/path/to/source.py"}}}}
    
This tool generates test files for the provided source file, optionally guided by a prompt file.""",
    inputSchema={
        "type": "object",
        "properties": {
            "source_file": {
                "type": "string",
                "description": "IMPORTANT: Provide just the full path to the source file, without any prefix"
            },
            "prompt_file": {
                "type": "string",
                "description": "Optional: Full path to a prompt file to guide test generation (no prefix)"
            },
            "output": {
                "type": "string",
                "description": "Specify where to save the generated tests"
            },
            "language": {
                "type": "string",
                "description": "Explicitly specify the programming language (normally auto-detected from file extension)"
            },
            "coverage_report": {
                "type": "string",
                "description": "Path to a coverage report file to help focus test generation"
            },
            "existing_tests": {
                "type": "string",
                "description": "Path to existing test files to enhance or extend"
            },
            "target_coverage": {
                "type": "number", 
                "description": "Target coverage percentage to aim for (0-100)"
            },
            "merge": {
                "type": "boolean",
                "description": "Merge new tests with existing tests"
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
        "required": ["source_file"],
        "additionalProperties": False
    }
)

# Fix Command Tool
#-----------------
PDD_FIX = types.Tool(
    name="pdd-fix",
    description="""Fix issues in a source file using AI.
    
Examples:
- ✅ CORRECT: {"prompt_file": "/path/to/prompt.txt", "source_file": "/path/to/source.py", "test_file": "/path/to/test.py"}
- ❌ INCORRECT: Do NOT use CLI-style arguments like "--prompt=/path/to/prompt.txt"
    
This tool attempts to fix issues in source code using AI, guided by a prompt file and validated by tests.""",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "IMPORTANT: Full path to the prompt file describing the code to be fixed (no prefix)"
            },
            "source_file": {
                "type": "string",
                "description": "IMPORTANT: Full path to the source file to be fixed (no prefix)"
            },
            "test_file": {
                "type": "string",
                "description": "Optional: Full path to test file to validate fixes (no prefix)"
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
        "required": ["prompt_file", "source_file"],
        "additionalProperties": False
    }
)

# Example Command Tool
#---------------------
PDD_EXAMPLE = types.Tool(
    name="pdd-example",
    description="""Generate example code that demonstrates how to use a module.
    
Examples:
- ✅ CORRECT: {"source_file": "/path/to/source.py", "output": "/path/to/output.py"}
- ❌ INCORRECT: Do NOT use CLI-style arguments like "--file=/path/to/source.py"
    
This tool creates example code showing how to use the specified module or source file.""",
    inputSchema={
        "type": "object",
        "properties": {
            "source_file": {
                "type": "string",
                "description": "IMPORTANT: Full path to the source file to generate examples for (no prefix)"
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
            },
            "quiet": {
                "type": "boolean",
                "description": "Decrease output verbosity for minimal information"
            }
        },
        "required": ["source_file"],
        "additionalProperties": False
    }
)

# Continue Command Tool
#----------------------
PDD_CONTINUE = types.Tool(
    name="pdd-continue",
    description="""Continue generation of partially completed output.
    
Examples:
- ✅ CORRECT: {"prompt_file": "/path/to/prompt.txt", "output_file": "/path/to/partial.py"}
- ❌ INCORRECT: Do NOT use CLI-style arguments like "--prompt=/path/to/prompt.txt"
    
This tool continues code generation from a partially completed file.""",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "IMPORTANT: Full path to the original prompt file (no prefix)"
            },
            "output_file": {
                "type": "string",
                "description": "IMPORTANT: Full path to the partially generated output file to continue (no prefix)"
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
        "required": ["prompt_file", "output_file"],
        "additionalProperties": False
    }
)

# Preprocess Command Tool
#-----------------------
PDD_PREPROCESS = types.Tool(
    name="pdd-preprocess",
    description="""Preprocess prompt files for code generation.
    
Examples:
- ✅ CORRECT: {"prompt_file": "/path/to/prompt.txt", "output": "/path/to/output.txt"}
- ❌ INCORRECT: Do NOT use CLI-style arguments like "--file=/path/to/prompt.txt"
    
This tool preprocesses prompt files to prepare them for code generation.""",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "IMPORTANT: Full path to the prompt file to preprocess (no prefix)"
            },
            "output": {
                "type": "string", 
                "description": "Specify where to save the preprocessed output"
            },
            "xml": {
                "type": "boolean",
                "description": "Output as XML format"
            },
            "recursive": {
                "type": "boolean",
                "description": "Process directories recursively"
            },
            "double": {
                "type": "boolean",
                "description": "Apply double preprocessing"
            },
            "exclude": {
                "type": "array",
                "items": {"type": "string"},
                "description": "Exclude files matching these patterns"
            }
        },
        "required": ["prompt_file"],
        "additionalProperties": False
    }
)

# Analyze Command Tool
#---------------------
PDD_ANALYZE = types.Tool(
    name="pdd-analyze",
    description="""Analyze code to provide insights and recommendations.
    
Examples:
- ✅ CORRECT: {"source_file": "/path/to/source.py", "output": "/path/to/output.md"}
- ❌ INCORRECT: Do NOT use CLI-style arguments like "--file=/path/to/source.py"
    
This tool analyzes code and generates insights, recommendations, and potential improvements.""",
    inputSchema={
        "type": "object",
        "properties": {
            "source_file": {
                "type": "string",
                "description": "IMPORTANT: Full path to the source file to analyze (no prefix)"
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
        "required": ["source_file"],
        "additionalProperties": False
    }
)

# Split Command Tool
#------------------
PDD_SPLIT = types.Tool(
    name="pdd-split",
    description="Split a prompt into sub-prompts",
    inputSchema={
        "type": "object",
        "properties": {
            "input_prompt": {
                "type": "string",
                "description": "The input prompt file to split"
            },
            "input_code": {
                "type": "string",
                "description": "The input code file"
            },
            "example_code": {
                "type": "string",
                "description": "The example code file"
            },
            "output_sub": {
                "type": "string",
                "description": "Where to save the sub-prompts"
            },
            "output_modified": {
                "type": "string",
                "description": "Where to save the modified code"
            }
        },
        "required": ["input_prompt", "input_code", "example_code"]
    }
)

# Change Command Tool
#------------------
PDD_CHANGE = types.Tool(
    name="pdd-change",
    description="Change code based on a change prompt",
    inputSchema={
        "type": "object",
        "properties": {
            "change_prompt_file": {
                "type": "string",
                "description": "The change prompt file"
            },
            "input_code": {
                "type": "string",
                "description": "The input code file to modify"
            },
            "input_prompt_file": {
                "type": "string",
                "description": "The original prompt file (optional when using --csv)"
            },
            "output": {
                "type": "string",
                "description": "Where to save the changed code"
            },
            "csv": {
                "type": "boolean",
                "description": "Use CSV format for input"
            }
        },
        "required": ["change_prompt_file", "input_code"]
    }
)

# Update Command Tool
#------------------
PDD_UPDATE = types.Tool(
    name="pdd-update",
    description="Update code based on new requirements",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "The original prompt file"
            },
            "code_file": {
                "type": "string",
                "description": "The original code file"
            },
            "new_prompt_file": {
                "type": "string",
                "description": "The new prompt file with updated requirements"
            },
            "output": {
                "type": "string",
                "description": "Where to save the updated code"
            }
        },
        "required": ["prompt_file", "code_file", "new_prompt_file"]
    }
)

# Detect Command Tool
#------------------
PDD_DETECT = types.Tool(
    name="pdd-detect",
    description="Detect code issues and vulnerabilities",
    inputSchema={
        "type": "object",
        "properties": {
            "input_file": {
                "type": "string",
                "description": "The file to check for issues"
            },
            "csv": {
                "type": "boolean",
                "description": "Output in CSV format"
            }
        },
        "required": ["input_file"]
    }
)

# Conflicts Command Tool
#---------------------
PDD_CONFLICTS = types.Tool(
    name="pdd-conflicts",
    description="Detect and resolve conflicts in code",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "The prompt file"
            },
            "base": {
                "type": "string",
                "description": "The base version of the code"
            },
            "ours": {
                "type": "string",
                "description": "Our version of the code"
            },
            "theirs": {
                "type": "string",
                "description": "Their version of the code"
            },
            "output": {
                "type": "string",
                "description": "Where to save the resolved code"
            }
        },
        "required": ["prompt_file", "base", "ours", "theirs"]
    }
)

# Crash Command Tool
#-----------------
PDD_CRASH = types.Tool(
    name="pdd-crash",
    description="Analyze and fix crashing code",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "The prompt file describing the code"
            },
            "code_file": {
                "type": "string",
                "description": "The code file that's crashing"
            },
            "crash_file": {
                "type": "string",
                "description": "File containing the crash information"
            },
            "output": {
                "type": "string",
                "description": "Where to save the fixed code"
            }
        },
        "required": ["prompt_file", "code_file", "crash_file"]
    }
)

# Trace Command Tool
#-----------------
PDD_TRACE = types.Tool(
    name="pdd-trace",
    description="Analyze execution trace data",
    inputSchema={
        "type": "object",
        "properties": {
            "trace_file": {
                "type": "string",
                "description": "The trace file to analyze"
            },
            "output": {
                "type": "string",
                "description": "Where to save the analysis results"
            }
        },
        "required": ["trace_file"]
    }
)

# Bug Command Tool
#---------------
PDD_BUG = types.Tool(
    name="pdd-bug",
    description="Find and fix bugs in code",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "The prompt file describing the code"
            },
            "code_file": {
                "type": "string",
                "description": "The code file with bugs"
            },
            "bug_description": {
                "type": "string",
                "description": "File containing bug description"
            },
            "output": {
                "type": "string",
                "description": "Where to save the fixed code"
            }
        },
        "required": ["prompt_file", "code_file", "bug_description"]
    }
)

# Auto Dependencies Command Tool
#-----------------------------
PDD_AUTO_DEPS = types.Tool(
    name="pdd-auto-deps",
    description="Automatically detect and add dependencies",
    inputSchema={
        "type": "object",
        "properties": {
            "input_file": {
                "type": "string",
                "description": "The file to analyze for dependencies"
            },
            "output": {
                "type": "string",
                "description": "Where to save the dependency information"
            }
        },
        "required": ["input_file"]
    }
)

# Simplest possible tool for testing
PDD_TEST_TOOL = types.Tool(
    name="pdd-test-tool",
    description=f"""A simple test tool that returns a static response.
{LLM_PARAMETER_GUIDANCE}    
Examples:
- ✅ CORRECT FORMAT FOR CLAUDE CODE: {{"kwargs": "{{\\"message\\": \\"Hello from Claude\\"}}"}}
- ✅ CORRECT FORMAT FOR DIRECT API: {{"message": "Hello from Claude"}}
""",
    inputSchema={
        "type": "object",
        "properties": {
            "message": {
                "type": "string",
                "description": "A message to include in the response"
            }
        },
        "required": [],
        "additionalProperties": False
    }
)

# Collection of all PDD tools
PDD_TOOLS = [
    PDD_GENERATE,
    PDD_TEST,
    PDD_FIX,
    PDD_EXAMPLE,
    PDD_CONTINUE,
    PDD_PREPROCESS,
    PDD_ANALYZE,
    PDD_SPLIT,
    PDD_CHANGE,
    PDD_UPDATE,
    PDD_DETECT,
    PDD_CONFLICTS,
    PDD_CRASH,
    PDD_TRACE,
    PDD_BUG,
    PDD_AUTO_DEPS,
    PDD_TEST_TOOL
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