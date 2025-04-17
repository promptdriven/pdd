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
- Parameters can be provided either as direct key-value pairs or as a JSON string in the 'kwargs' field
- DO NOT use CLI-style arguments with dashes (like --file=/path/to/file)

✅ CORRECT FORMAT (direct): {"param1": "value1", "param2": "value2"}
✅ CORRECT FORMAT (JSON string): {"kwargs": "{\\"param1\\": \\"value1\\", \\"param2\\": \\"value2\\"}"}
❌ INCORRECT FORMAT: {"kwargs": "--param1 value1 --param2 value2"}
"""

# Generate Command Tool
#----------------------
PDD_GENERATE = types.Tool(
    name="pdd-generate",
    description=f"""Generate code from a prompt file.
{LLM_PARAMETER_GUIDANCE}

WHEN TO USE: Choose this tool when implementing new functionality from scratch or 
creating a full implementation of code described in a prompt file. This creates 
comprehensive implementation details that other code can use.

Examples:
- ✅ CORRECT (direct): {{"prompt_file": "/path/to/prompt.txt", "output": "/path/to/output.py", "force": true}}
- ✅ CORRECT (JSON string): {{"kwargs": "{{\\"prompt_file\\": \\"/path/to/prompt.txt\\", \\"output\\": \\"/path/to/output.py\\", \\"force\\": true}}"}}
- ❌ INCORRECT: {{"kwargs": "--file=/path/to/prompt.txt"}}

IMPORTANT: ALWAYS include "force": true when there's a possibility the output file already exists.
Without it, the command will hang waiting for user confirmation to overwrite files.

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
    description=f"""Generate or enhance unit tests for a given code file and its corresponding prompt file.
{LLM_PARAMETER_GUIDANCE}    
Examples:
- ✅ CORRECT: {{"prompt_file": "/path/to/prompt.txt", "code_file": "/path/to/source.py", "output": "/path/to/test_output.py", "force": true}}
- ❌ INCORRECT: {{"source_file": "/path/to/source.py"}} (missing prompt_file)
- ❌ INCORRECT: {{"kwargs": {{"prompt_file": "/path/to/prompt.txt"}}}}
    
IMPORTANT: ALWAYS include "force": true when there's a possibility the output file already exists.
Without it, the command will hang waiting for user confirmation to overwrite files.

This tool generates test files for the provided code file, guided by the prompt file that generated the code.""",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "REQUIRED: Full path to the prompt file that generated the code"
            },
            "code_file": {
                "type": "string",
                "description": "REQUIRED: Full path to the code file to be tested"
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
        "required": ["prompt_file", "code_file"],
        "additionalProperties": False
    }
)

# Fix Command Tool
#-----------------
PDD_FIX = types.Tool(
    name="pdd-fix",
    description=f"""Fix errors in code and unit tests based on error messages and the original prompt file.
{LLM_PARAMETER_GUIDANCE}    
Examples:
- ✅ CORRECT WITHOUT LOOP: {{"prompt_file": "/path/to/prompt.txt", "code_file": "/path/to/source.py", "unit_test_file": "/path/to/test.py", "error_file": "/path/to/errors.log", "force": true}}
- ✅ CORRECT WITH LOOP: {{"prompt_file": "/path/to/prompt.txt", "code_file": "/path/to/source.py", "unit_test_file": "/path/to/test.py", "error_file": "/path/to/errors.log", "loop": true, "verification_program": "/path/to/example.py", "force": true}}
- ❌ INCORRECT: {{"source_file": "/path/to/source.py"}} (missing other required parameters)
    
IMPORTANT: 
1. ALWAYS include "force": true when there's a possibility the output file already exists.
   Without it, the command will hang waiting for user confirmation to overwrite files.
2. LOOP MODE vs STANDARD MODE:
   - LOOP MODE: Use "loop": true to enable iterative fixing that automatically runs tests, fixes issues, and retries
   - ERROR_FILE is always required due to CLI constraints, but when using loop=true, it can be a path to a non-existent file
   - When using loop=true, "verification_program" is required to verify if fixes work correctly

This tool attempts to fix errors in code based on error messages and the original prompt file.
When using the loop option, it will run multiple fix attempts until tests pass or max attempts is reached.""",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "REQUIRED: Full path to the prompt file that generated the code under test"
            },
            "code_file": {
                "type": "string",
                "description": "REQUIRED: Full path to the code file to be fixed"
            },
            "unit_test_file": {
                "type": "string",
                "description": "REQUIRED: Full path to the unit test file"
            },
            "error_file": {
                "type": "string",
                "description": "REQUIRED: Full path to the file containing unit test runtime error messages (with loop=true, this can be a path to a non-existent file)"
            },
            "output_code": {
                "type": "string",
                "description": "Where to save the fixed code"
            },
            "output_test": {
                "type": "string",
                "description": "Where to save the fixed tests"
            },
            "output_results": {
                "type": "string",
                "description": "Where to save the results of the error fixing process"
            },
            "verification_program": {
                "type": "string",
                "description": "IMPORTANT: Required when using loop=true. Program that verifies if fixed code runs correctly during iterative fixing. Typically it is the _example.py file which is often in the context directory."
            },
            "loop": {
                "type": "boolean",
                "description": "Enable iterative fixing process that automatically runs tests, fixes issues, and retries until successful or max attempts reached"
            },
            "max_attempts": {
                "type": "integer",
                "description": "Maximum number of fix attempts when using loop=true (default: 3)"
            },
            "budget": {
                "type": "number",
                "description": "Maximum cost allowed for the fixing process when using loop=true (default: $5.0)"
            },
            "auto_submit": {
                "type": "boolean",
                "description": "Automatically submit the example if all unit tests pass during the fix loop. During loop mode it is generally best to use this option so that the subsequent generation can use the example as context."
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
        "required": ["prompt_file", "code_file", "unit_test_file", "error_file"],
        "additionalProperties": False
    }
)

# Example Command Tool
#---------------------
PDD_EXAMPLE = types.Tool(
    name="pdd-example",
    description=f"""Generate example code that demonstrates how to use a module.
{LLM_PARAMETER_GUIDANCE}

WHEN TO USE: Choose this tool when creating compact, reusable references that other 
prompts can efficiently import. Similar to a header file or API documentation, this 
produces minimal, token-efficient code that shows the interface without implementation 
details. This is more token-efficient than including full implementations.

Examples:
- ✅ CORRECT: {{"prompt_file": "/path/to/prompt.txt", "code_file": "/path/to/source.py", "output": "/path/to/output.py", "force": true}}
- ❌ INCORRECT: {{"source_file": "/path/to/source.py"}} (missing prompt_file)
- ❌ INCORRECT: {{"code_file": "/path/to/source.py"}} (missing prompt_file)
- ❌ INCORRECT: Do NOT use CLI-style arguments like "--file=/path/to/source.py"
    
IMPORTANT: 
1. ALWAYS include "force": true when there's a possibility the output file already exists.
   Without it, the command will hang waiting for user confirmation to overwrite files.
2. BOTH prompt_file AND code_file are required parameters.
3. Parameter order matters - they will be passed to PDD CLI in this order: prompt_file, then code_file.

This tool creates example code showing how to use the specified module or source file.""",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "REQUIRED: Full path to the prompt file that originally generated the code"
            },
            "code_file": {
                "type": "string",
                "description": "REQUIRED: Full path to the source file to generate examples for"
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
        "required": ["prompt_file", "code_file"],
        "additionalProperties": False
    }
)

# Preprocess Command Tool
#-----------------------
PDD_PREPROCESS = types.Tool(
    name="pdd-preprocess",
    description="""Preprocess prompt files for code generation.
    
Examples:
- ✅ CORRECT: {"prompt_file": "/path/to/prompt.txt", "output": "/path/to/output.txt", "force": true}
- ❌ INCORRECT: Do NOT use CLI-style arguments like "--file=/path/to/prompt.txt"
    
IMPORTANT: ALWAYS include "force": true when there's a possibility the output file already exists.
Without it, the command will hang waiting for user confirmation to overwrite files.

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

# Split Command Tool
#------------------
PDD_SPLIT = types.Tool(
    name="pdd-split",
    description=f"""Split large complex prompt files into smaller, more manageable prompt files by extracting specific functionality into a separate sub-module.
{LLM_PARAMETER_GUIDANCE}    

WHEN TO USE: Choose this tool when you need to extract specific functionality from a large prompt into a separate sub-prompt that can be independently maintained and imported.

HOW IT WORKS:
1. The tool analyzes your original prompt and its generated code
2. It extracts the functionality specified by your interface file into a new sub-prompt
3. It modifies the original prompt to now import the extracted functionality

Examples:
- ✅ CORRECT: {{"input_prompt": "/path/to/prompt.txt", "input_code": "/path/to/code.py", "example_code": "/path/to/interface.py", "force": true}}
- ❌ INCORRECT: Do NOT use CLI-style arguments with dashes

IMPORTANT: 
1. ALWAYS include "force": true when there's a possibility the output file already exists.
2. The example_code must be an INTERFACE FILE that defines the specific functionality you want to extract, not just any example usage.
3. The interface file should contain function signatures, class definitions, or other code that clearly defines the boundary of what should be extracted.

This tool produces two outputs:
- output_sub: Will contain the EXTRACTED FUNCTIONALITY as a self-contained prompt (the part defined by your interface file)
- output_modified: Will contain the REMAINING PROMPT that imports the extracted functionality""",
    inputSchema={
        "type": "object",
        "properties": {
            "input_prompt": {
                "type": "string",
                "description": "REQUIRED: The filename of the large prompt file to be split"
            },
            "input_code": {
                "type": "string",
                "description": "REQUIRED: The filename of the code generated from the input prompt"
            },
            "example_code": {
                "type": "string",
                "description": "REQUIRED: The filename of an interface file that defines exactly what functionality to extract into the sub-module. This should contain function signatures, class definitions, or other code that clearly defines the boundary of what should be extracted."
            },
            "output_sub": {
                "type": "string",
                "description": "Specify where to save the new sub-prompt file containing the extracted functionality (the part defined in your example_code)"
            },
            "output_modified": {
                "type": "string",
                "description": "Specify where to save the modified version of the original prompt file that now imports the extracted functionality"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            }
        },
        "required": ["input_prompt", "input_code", "example_code"]
    }
)

# Change Command Tool
#------------------
PDD_CHANGE = types.Tool(
    name="pdd-change",
    description=f"""Modify an input prompt file based on a change prompt and the corresponding input code.
{LLM_PARAMETER_GUIDANCE}    
Examples:
- ✅ CORRECT: {{"change_prompt_file": "/path/to/change.txt", "input_code": "/path/to/code.py", "input_prompt_file": "/path/to/prompt.txt", "force": true}}
- ✅ CORRECT with CSV: {{"change_prompt_file": "/path/to/change.txt", "input_code": "/path/to/code_dir", "csv": true, "force": true}}
- ❌ INCORRECT: {{"prompt_file": "/path/to/prompt.txt"}} (using incorrect parameter names)

IMPORTANT: ALWAYS include "force": true when there's a possibility the output file already exists.
Without it, the command will hang waiting for user confirmation to overwrite files.

This tool modifies an input prompt file based on a change prompt and the corresponding input code.""",
    inputSchema={
        "type": "object",
        "properties": {
            "change_prompt_file": {
                "type": "string",
                "description": "REQUIRED: The filename containing the instructions on how to modify the input prompt file"
            },
            "input_code": {
                "type": "string",
                "description": "REQUIRED: The filename of the code that was generated from the input prompt file, or the directory containing the code files when used with the '--csv' option"
            },
            "input_prompt_file": {
                "type": "string",
                "description": "The filename of the prompt file that will be modified (not required when using the '--csv' option)"
            },
            "output": {
                "type": "string",
                "description": "Specify where to save the modified prompt file"
            },
            "csv": {
                "type": "boolean",
                "description": "Use a CSV file for the change prompts instead of a single change prompt file"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            }
        },
        "required": ["change_prompt_file", "input_code"]
    }
)

# Update Command Tool
#------------------
PDD_UPDATE = types.Tool(
    name="pdd-update",
    description=f"""Update the original prompt file based on the modified code and optionally the original code.
{LLM_PARAMETER_GUIDANCE}    
Examples:
- ✅ CORRECT: {{"input_prompt_file": "/path/to/prompt.txt", "modified_code_file": "/path/to/modified.py", "input_code_file": "/path/to/original.py", "force": true}}
- ✅ CORRECT with git: {{"input_prompt_file": "/path/to/prompt.txt", "modified_code_file": "/path/to/modified.py", "git": true, "force": true}}
- ❌ INCORRECT: {{"prompt_file": "/path/to/prompt.txt"}} (using incorrect parameter names)

IMPORTANT: ALWAYS include "force": true when there's a possibility the output file already exists.
Without it, the command will hang waiting for user confirmation to overwrite files.

This tool updates the original prompt file based on the modified code and optionally the original code.""",
    inputSchema={
        "type": "object",
        "properties": {
            "input_prompt_file": {
                "type": "string",
                "description": "REQUIRED: The filename of the prompt file that generated the original code"
            },
            "modified_code_file": {
                "type": "string",
                "description": "REQUIRED: The filename of the code that was modified by the user"
            },
            "input_code_file": {
                "type": "string",
                "description": "The filename of the original code that was generated from the input prompt file (not required when using --git)"
            },
            "output": {
                "type": "string",
                "description": "Specify where to save the modified prompt file"
            },
            "git": {
                "type": "boolean", 
                "description": "Use git history to find the original code file, eliminating the need for the input_code_file argument"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            }
        },
        "required": ["input_prompt_file", "modified_code_file"]
    }
)

# Detect Command Tool
#------------------
PDD_DETECT = types.Tool(
    name="pdd-detect",
    description=f"""Analyze a list of prompt files and a change description to determine which prompts need to be changed.
{LLM_PARAMETER_GUIDANCE}    
Examples:
- ✅ CORRECT: {{"prompt_files": ["/path/to/prompt1.txt", "/path/to/prompt2.txt"], "change_file": "/path/to/changes.txt", "force": true}}
- ❌ INCORRECT: {{"input_file": "/path/to/prompt.txt"}} (using incorrect parameter names)

IMPORTANT: ALWAYS include "force": true when there's a possibility the output file already exists.
Without it, the command will hang waiting for user confirmation to overwrite files.

This tool analyzes a list of prompt files and a change description to determine which prompts need to be changed.""",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_files": {
                "type": "array",
                "items": {"type": "string"},
                "description": "REQUIRED: A list of filenames of prompts that may need to be changed"
            },
            "change_file": {
                "type": "string",
                "description": "REQUIRED: Filename whose content describes the changes that need to be analyzed and potentially applied to the prompts"
            },
            "output": {
                "type": "string",
                "description": "Specify where to save the CSV file containing the analysis results"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            }
        },
        "required": ["prompt_files", "change_file"]
    }
)

# Conflicts Command Tool
#---------------------
PDD_CONFLICTS = types.Tool(
    name="pdd-conflicts",
    description=f"""Analyze two prompt files to find conflicts between them and suggest how to resolve those conflicts.
{LLM_PARAMETER_GUIDANCE}    
Examples:
- ✅ CORRECT: {{"prompt1": "/path/to/prompt1.txt", "prompt2": "/path/to/prompt2.txt", "force": true}}
- ❌ INCORRECT: {{"prompt_file": "/path/to/prompt.txt"}} (using incorrect parameter names)

IMPORTANT: ALWAYS include "force": true when there's a possibility the output file already exists.
Without it, the command will hang waiting for user confirmation to overwrite files.

This tool analyzes two prompt files to find conflicts between them and suggest how to resolve those conflicts.""",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt1": {
                "type": "string",
                "description": "REQUIRED: First prompt in the pair of prompts we are comparing"
            },
            "prompt2": {
                "type": "string",
                "description": "REQUIRED: Second prompt in the pair of prompts we are comparing"
            },
            "output": {
                "type": "string",
                "description": "Specify where to save the CSV file containing the conflict analysis results"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            }
        },
        "required": ["prompt1", "prompt2"]
    }
)

# Crash Command Tool
#-----------------
PDD_CRASH = types.Tool(
    name="pdd-crash",
    description=f"""Fix errors in a code module and its calling program that caused a program to crash.
{LLM_PARAMETER_GUIDANCE}    
Examples:
- ✅ CORRECT: {{"prompt_file": "/path/to/prompt.txt", "code_file": "/path/to/code.py", "program_file": "/path/to/program.py", "error_file": "/path/to/errors.log", "force": true}}
- ❌ INCORRECT: {{"prompt_file": "/path/to/prompt.txt", "code_file": "/path/to/code.py"}} (missing required parameters)

IMPORTANT: ALWAYS include "force": true when there's a possibility the output file already exists.
Without it, the command will hang waiting for user confirmation to overwrite files.

This tool fixes errors in a code module and its calling program that caused a program to crash.""",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "REQUIRED: Filename of the prompt file that generated the code module"
            },
            "code_file": {
                "type": "string",
                "description": "REQUIRED: Filename of the code module that caused the crash and will be modified"
            },
            "program_file": {
                "type": "string",
                "description": "REQUIRED: Filename of the program that was running the code module"
            },
            "error_file": {
                "type": "string",
                "description": "REQUIRED: Filename of the file containing the errors from the program run"
            },
            "output": {
                "type": "string",
                "description": "Where to save the fixed code file"
            },
            "output_program": {
                "type": "string",
                "description": "Where to save the fixed program file"
            },
            "loop": {
                "type": "boolean",
                "description": "Enable iterative fixing process"
            },
            "max_attempts": {
                "type": "integer",
                "description": "Maximum number of fix attempts (default: 3)"
            },
            "budget": {
                "type": "number",
                "description": "Maximum cost allowed for the fixing process (default: $5.0)"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            }
        },
        "required": ["prompt_file", "code_file", "program_file", "error_file"]
    }
)

# Bug Command Tool
#---------------
PDD_BUG = types.Tool(
    name="pdd-bug",
    description=f"""Generate a unit test based on observed and desired outputs.
{LLM_PARAMETER_GUIDANCE}    
Examples:
- ✅ CORRECT: {{"prompt_file": "/path/to/prompt.txt", "code_file": "/path/to/code.py", "program_file": "/path/to/program.py", "current_output_file": "/path/to/current.txt", "desired_output_file": "/path/to/desired.txt", "force": true}}
- ❌ INCORRECT: {{"prompt_file": "/path/to/prompt.txt"}} (missing required parameters)

IMPORTANT: ALWAYS include "force": true when there's a possibility the output file already exists.
Without it, the command will hang waiting for user confirmation to overwrite files.

This tool generates a unit test based on observed and desired outputs, given the original prompt and code.""",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "REQUIRED: Filename of the prompt file that generated the code"
            },
            "code_file": {
                "type": "string",
                "description": "REQUIRED: Filename of the code file being tested"
            },
            "program_file": {
                "type": "string",
                "description": "REQUIRED: Filename of the program used to run the code under test"
            },
            "current_output_file": {
                "type": "string",
                "description": "REQUIRED: File containing the current (incorrect) output of the program"
            },
            "desired_output_file": {
                "type": "string",
                "description": "REQUIRED: File containing the desired (correct) output of the program"
            },
            "output": {
                "type": "string",
                "description": "Where to save the generated unit test"
            },
            "language": {
                "type": "string",
                "description": "Specify the programming language for the unit test (default is 'Python')"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            }
        },
        "required": ["prompt_file", "code_file", "program_file", "current_output_file", "desired_output_file"]
    }
)

# Auto Dependencies Command Tool
#-----------------------------
PDD_AUTO_DEPS = types.Tool(
    name="pdd-auto-deps",
    description=f"""Analyze a prompt file and a directory of potential dependencies.
{LLM_PARAMETER_GUIDANCE}    
Examples:
- ✅ CORRECT: {{"prompt_file": "/path/to/prompt.txt", "directory_path": "context/*.py", "force": true}}
- ❌ INCORRECT: {{"input_file": "/path/to/prompt.txt"}} (using incorrect parameter name)

IMPORTANT: ALWAYS include "force": true when there's a possibility the output file already exists.
Without it, the command will hang waiting for user confirmation to overwrite files.

This tool analyzes a prompt file and a directory of potential dependencies to determine and insert needed dependencies into the prompt.""",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "REQUIRED: Filename of the prompt file that needs dependencies analyzed and inserted"
            },
            "directory_path": {
                "type": "string",
                "description": "REQUIRED: Path to the directory containing potential dependency files (should include glob patterns)"
            },
            "output": {
                "type": "string",
                "description": "Where to save the modified prompt file with dependencies inserted"
            },
            "csv": {
                "type": "string",
                "description": "Specify the CSV file that contains or will contain dependency information"
            },
            "force_scan": {
                "type": "boolean",
                "description": "Force rescanning of all potential dependency files even if they exist in the CSV file"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            }
        },
        "required": ["prompt_file", "directory_path"]
    }
)

# Trace Command Tool
#-----------------
PDD_TRACE = types.Tool(
    name="pdd-trace",
    description=f"""Find the associated line number between a prompt file and the generated code.
{LLM_PARAMETER_GUIDANCE}    
Examples:
- ✅ CORRECT: {{"prompt_file": "/path/to/prompt.txt", "code_file": "/path/to/code.py", "code_line": 42, "force": true}}
- ❌ INCORRECT: {{"trace_file": "/path/to/trace.txt"}} (using incorrect parameter name)

IMPORTANT: ALWAYS include "force": true when there's a possibility the output file already exists.
Without it, the command will hang waiting for user confirmation to overwrite files.

This tool traces code lines back to prompt lines.""",
    inputSchema={
        "type": "object",
        "properties": {
            "prompt_file": {
                "type": "string",
                "description": "REQUIRED: Filename of the prompt file that generated the code"
            },
            "code_file": {
                "type": "string",
                "description": "REQUIRED: Filename of the code file to be analyzed"
            },
            "code_line": {
                "type": "integer",
                "description": "REQUIRED: Line number in the code file that the debugger trace line is on"
            },
            "output": {
                "type": "string",
                "description": "Where to save the trace analysis results"
            },
            "force": {
                "type": "boolean",
                "description": "Overwrite existing files without asking for confirmation"
            }
        },
        "required": ["prompt_file", "code_file", "code_line"]
    }
)

# Collection of all PDD tools
PDD_TOOLS = [
    PDD_GENERATE,
    PDD_TEST,
    PDD_FIX,
    PDD_EXAMPLE,
    PDD_PREPROCESS,
    PDD_SPLIT,
    PDD_CHANGE,
    PDD_UPDATE,
    PDD_DETECT,
    PDD_CONFLICTS,
    PDD_CRASH,
    PDD_TRACE,
    PDD_BUG,
    PDD_AUTO_DEPS
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