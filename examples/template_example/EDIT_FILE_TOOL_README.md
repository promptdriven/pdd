# Edit File Tool

A utility for editing files using Claude with the text_editor_20250124 tool and think tool capabilities, featuring intelligent prompt caching to reduce API costs by up to 53%.

## Features

- Edit files using natural language instructions
- Intelligent parsing of edit requests
- Detects and handles multiple edits in a single instruction
- Supports various types of edits (line replacements, text replacements, insertions, etc.)
- Uses Claude's think tool capability for complex editing planning (reduces token usage by up to 43%)
- Direct command-line interface
- Can be used as a Python library
- Tracks and reports LLM costs for API usage
- Uses Anthropic's native prompt caching to reduce API costs

## Installation

### From PyPI (once published)

```bash
pip install edit-file-tool
```

### From Source

```bash
git clone https://github.com/anthropics/edit-file-tool.git
cd edit-file-tool
pip install -e .
```

## Usage

### Command Line Interface

```bash
# Set your API key
export ANTHROPIC_API_KEY=your_api_key_here

# Edit a file with natural language instructions
edit-file path/to/file.py "Fix the syntax error in the for loop on line 10"
# Output includes LLM cost:
# LLM cost: $0.0345
# File edited successfully!

# More verbose output
edit-file --verbose path/to/file.py "Change the greeting to 'Hello, world!'"

# Choose a different model
edit-file --model claude-3-7-sonnet-20250219 path/to/file.py "Add docstrings to all functions"

# Control caching behavior
edit-file --cache auto path/to/file.py "Rename the function to be more descriptive"  # Auto-detect (default)
edit-file --cache always path/to/file.py "Add error handling"  # Always use caching
edit-file --cache never path/to/file.py "Simplify this logic"  # Never use caching
```

### Python API

#### Using Natural Language Editing

```python
import asyncio
from edit_file_tool import edit_file

async def main():
    # Edit using natural language instructions
    success, error, llm_cost = await edit_file(
        file_path="path/to/file.py",
        edit_instructions="Change all occurrences of 'foo' to 'bar'",
        model="claude-3-7-sonnet-20250219",
        verbose=True,
        use_cache="auto",  # Options: "auto" (default), True (always use), False (disable)
        max_iterations=10  # Maximum number of conversation iterations to attempt (default: 10)
    )
    
    # Display the cost
    print(f"LLM cost: ${llm_cost:.4f}")
    
    if success:
        print("File edited successfully!")
    else:
        print(f"Error: {error}")

# Run the async function
asyncio.run(main())
```

#### Using the Editor Tool Directly

You can also use the editor tool directly for programmatic control:

```python
import asyncio
from edit_file_tool import EditTool20250124

async def main():
    # Initialize the editor tool
    editor = EditTool20250124()
    
    # View a file
    result = await editor(
        command="view",
        path="/path/to/file.py"
    )
    print(result.output)
    
    # Insert content after line 5 (remember: insert_line is 0-indexed)
    result = await editor(
        command="insert",
        path="/path/to/file.py",
        insert_line=5,  # After line 6 (1-indexed)
        new_str="# New content inserted here"
    )
    print(result.output)
    
    # Replace specific text
    result = await editor(
        command="str_replace",
        path="/path/to/file.py",
        old_str="function_name",
        new_str="improved_function_name"
    )
    print(result.output)

# Run the async function
asyncio.run(main())
```

## Supported Edit Types

The tool understands various types of edit instructions:

- **Text Replacement**: "Replace 'foo' with 'bar'"
- **Line Editing**: "Change line 5 to 'hello world'"
- **Insertion**: "Insert 'new code' after line 10" or "Insert 'new code' before line 7"
- **Appending**: "Add a new line at the end of the file"
- **Multiple Edits**: "Fix the typo on line 3 and remove the duplicate function on line 15"
- **Code Fixes**: "Fix the syntax error in the function"
- **Formatting**: "Properly indent the code block"
- **Commenting/Uncommenting**: "Comment out the debugging code"

## Advanced Features

### Think Tool Integration

The tool leverages Claude's think tool capability to improve reasoning and token efficiency:

#### How the Think Tool Works

- Provides Claude with a private space for planning and reasoning
- Thoughts are processed without adding to context window or token count
- Helps Claude break down complex edits into logical steps
- Improves token efficiency by externalizing planning steps

#### Benefits

- **Reduced Token Usage**: Testing shows 13-43% reduction in token usage during file editing operations
- **Better Planning**: Helps Claude approach complex edits more systematically
- **Prevent Token Overflows**: Helps avoid "prompt too long" errors in multi-step edits
- **Higher-Quality Edits**: More thorough planning leads to cleaner, more accurate results

#### Automatic Usage

The think tool is automatically integrated with no additional configuration needed. Claude decides when to use the tool based on edit complexity. The implementation enhances performance particularly for:

- Multi-step edits requiring planning
- Complex code reorganization
- Edits requiring careful reasoning about code structure
- Long-running editing sessions that would otherwise hit token limits

#### Performance Benchmarks

Our think tool benchmark tests show consistent token reduction across various edit tasks:

**Complex Edit Test (Multiple Function Updates)**:
```
                       With Think Tool    Without Think Tool    Savings
Token Usage:           $0.2022            $0.2204               8.27%
Iterations Required:   9                  10                    10.00%
```

**Large Code Fix Test (Real-world Project)**:
```
                       With Think Tool     Without Think Tool   Savings
Unit Test Fixing:      $2.6118             $3.0178              13.45%
Code Implementation:   $0.3622             $0.6339              42.86%
Total Editing Cost:    $2.9740             $3.6517              18.56%
Think Tool Usage:      3 times             0 times              n/a
Iterations Required:   35                  30                   -16.67%*
```
*Note: The with-thinking approach required more iterations but had smaller, more focused steps per iteration

**What Happens Without Think Tool During Editing:**
The most significant impact occurs during complex code implementation when Claude needs to reason through multiple interdependent changes. Without the think tool:

- **Higher Token Usage**: Without externalized thinking, all reasoning appears in the main context window, consuming approximately 43% more tokens during implementation
- **More Context Consumption**: Reasoning steps that could be externalized remain in the main context
- **Risk of Token Overflow**: Large files with complex edits can exceed context limits (200K tokens)
- **Less Structured Planning**: Planning steps are interspersed with implementation rather than separated

The benefits become even more significant with:
- Larger files (>5KB)
- More complex editing tasks
- Edits requiring sequential reasoning

Run the benchmark test yourself with:
```bash
python tests/simple_think_test.py
```

### LLM Cost Tracking

The tool automatically tracks and reports the cost of LLM API calls:

- Accurately calculates costs based on input and output tokens
- Supports pricing for all Claude models (3.7, 3.5, 3 Opus/Sonnet/Haiku, etc.)
- Returns cost as a floating point value in USD
- CLI displays cost after each edit operation
- Helps monitor and manage API usage costs

### Prompt Caching

The tool uses Anthropic's native prompt caching to reduce API costs when working with large files and repetitive edits:

#### How Caching Works

- Separates content (file data) from instructions (edit commands) in API requests
- Applies cache control to the file content portion, making it reusable
- Uses Anthropic's ephemeral cache type (5-minute minimum lifetime)
- Correctly calculates costs for cache operations with appropriate pricing:
  - Cache writes: 25% premium over standard input tokens
  - Cache reads: 90% discount compared to standard input tokens

#### Smart Cache Management

- **Auto-Detection**: Intelligently determines when caching is beneficial based on:
  - **File size**: Primary threshold at 1KB and 4KB
  - **Complexity**: Considers line count, non-empty lines, and content density
  - **Very small files (<1KB)**: Caching disabled to avoid overhead
  - **Large files (>4KB)**: Caching always enabled for maximum savings
  - **Medium files (1-4KB)**: Decision based on complexity metrics

- **Control Modes**:
  - `auto` (default): Let the tool decide based on file characteristics
  - `always`: Force caching regardless of file size (useful for benchmarking)
  - `never`: Disable caching entirely (useful for comparison)

- **CLI and API Control**:
  - CLI: `--cache [auto|always|never]` option
  - API: `use_cache` parameter accepting "auto", True, or False

#### Performance Benchmarks

Our testing demonstrates significant cost savings with caching for large files:

**Large File Test (16KB)**:
```
                     With Caching    Without Caching    Savings
First Request:       $0.091          $0.219            58.4%
Second Request:      $0.053          $0.091            41.6%
Total:               $0.144          $0.310            53.4%
```

**Medium File Test (6KB)**:
```
                     With Caching    Without Caching    Savings
First Request:       $0.254          $0.085            -199.5%*
Second Request:      $0.052          $0.088            40.9%
```
*Note: For medium files, the first request with caching can be more expensive due to cache setup costs, but subsequent requests see savings.

**Caching is most beneficial when**:
- Working with larger files (>4KB)
- Making multiple sequential edits to the same file
- Performing similar edits across multiple sessions

The verbose output (`--verbose`) displays detailed token and cost breakdowns for cache operations.

### Enhanced Insert Support

The tool now has first-class support for the `insert` command, enabling more precise insertions:

- **Insert after a line**: "Insert 'new content' after line 3"
- **Insert before a line**: "Insert 'new content' before line 5"
- **Insert at a specific line**: "Insert 'new content' at line 7"

The parser automatically determines the correct insert position and configures the Claude tool to use the `insert` command with the appropriate parameters.

## Requirements

- Python 3.9+
- [Anthropic API Key](https://www.anthropic.com/api)
- Claude model that supports the text_editor_20250124 tool and function-based tools (e.g., claude-3-7-sonnet-20250219)

## Development

### Running Tests

The package includes a comprehensive test suite:

```bash
# Run all tests
cd edit_file_tool
python -m tests.run_tests

# Run only parser tests (no API key needed)
python -m tests.run_tests --parser-only

# Run only tool tests
python -m tests.run_tests --tool-only

# Run with verbose output
python -m tests.run_tests -v

# Skip tests that require API access
python -m tests.run_tests --no-api

# Run think tool benchmark test (requires API key)
python tests/simple_think_test.py
```

### Benchmarking and Performance Testing

You can run the benchmark scripts to evaluate caching performance:

```bash
# Compare caching vs. no caching for different file sizes
python tests/scripts/compare_caching.py --size small
python tests/scripts/compare_caching.py --size medium
python tests/scripts/compare_caching.py --size large

# Test auto-detection for different file sizes
python tests/scripts/test_auto_caching.py --verbose

# See all benchmark options
python tests/scripts/compare_caching.py --help
```

The benchmark scripts require an Anthropic API key and will make real API calls. For accurate results, run each benchmark multiple times and average the results, as network conditions and server load can affect performance.
