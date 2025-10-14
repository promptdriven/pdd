# test_render_mermaid.py

"""
Test Plan for render_mermaid.py

I. Z3 Formal Verification vs. Unit Tests Analysis

The script's core logic is the categorization of modules into 'Frontend', 'Backend', or 'Shared' based on a prioritized set of tags. The rules are:
1.  If a module has a frontend-related tag (e.g., 'frontend', 'ui', 'react'), it is categorized as 'Frontend'.
2.  If a module does *not* have a frontend tag but *does* have a backend-related tag (e.g., 'backend', 'api'), it is categorized as 'Backend'.
3.  Otherwise, it is categorized as 'Shared'.

This is a simple if-elif-else logical structure. While it could be modeled with a formal verification tool like Z3 to prove properties such as mutual exclusivity (a module cannot be both 'Frontend' and 'Backend'), the logic is straightforward and implemented with list comprehensions that inherently enforce this exclusion.

Therefore, a comprehensive suite of unit tests is a more practical and efficient approach. Unit tests can directly verify the generated string output, test file I/O, and simulate command-line interactions, which are outside the scope of formal logic provers. A single test case with a module containing both tag types is sufficient to verify the priority rule.

II. Detailed Unit Test Plan

We will test the two main functions (`generate_mermaid_code`, `generate_html`) and the main execution block (CLI).

1.  **`generate_mermaid_code` Function Tests (Unit Tests)**
    *   **`test_full_architecture`**: Test with a complete architecture containing frontend, backend, and shared modules, along with dependencies between them. Verify the correct generation of subgraphs, nodes (with priorities), links, and class applications.
    *   **`test_empty_architecture`**: Test with an empty list of modules. The output should be a valid, minimal Mermaid diagram containing only the main application node and class definitions.
    *   **`test_frontend_only`**: Test with only frontend modules. Ensure only the 'Frontend' subgraph is created and linked from the main app node.
    *   **`test_backend_only`**: Test with only backend modules. Ensure only the 'Backend' subgraph is created and linked.
    *   **`test_shared_only`**: Test with only shared modules. Ensure the 'Shared' subgraph is created, but there are no direct links from the main app node to the subgraph.
    *   **`test_frontend_priority_rule`**: Test a module that contains both a frontend tag (e.g., 'ui') and a backend tag (e.g., 'api'). It must be categorized as 'Frontend', demonstrating the priority rule.
    *   **`test_missing_optional_fields`**: Test a module dictionary containing only the required 'filename' key. It should default to priority 0, have no dependencies, and be categorized as 'Shared'.
    *   **`test_complex_filenames`**: Test with filenames that include directory paths (`path/to/file.js`) and multiple dots (`api.v1.py`). The node name (ID) should be correctly extracted as the file's stem (`file` and `api.v1` respectively).
    *   **`test_no_dependencies`**: Test an architecture where modules exist but have no dependencies. Ensure no dependency links (`-->|uses|`) are generated.

2.  **`generate_html` Function Tests (Unit Tests)**
    *   **`test_html_generation_with_data`**: Verify that the function correctly embeds the application name, Mermaid code, and module data into the HTML template. Check for the presence of the `<title>`, `<h1>`, the Mermaid code block, and the embedded JSON data for tooltips.
    *   **`test_html_generation_special_chars`**: Test with module data containing special characters (quotes, newlines, etc.) in the description. Verify that the embedded JSON is valid and correctly escaped.
    *   **`test_html_generation_empty_architecture`**: Test with an empty architecture list. The embedded `moduleData` should be an empty JSON object (`{}`).

3.  **CLI and Main Execution Block Tests (Integration Tests)**
    *   **`test_main_success_all_args`**: Simulate running the script with all three command-line arguments (input file, app name, output file). Use mocking for `sys.argv` and `open`. Verify the correct output file is created with the expected content.
    *   **`test_main_success_default_args`**: Simulate running with only the required input file. Verify the default app name ('System Architecture') and default output filename (`<input_stem>_diagram.html`) are used.
    *   **`test_main_no_args`**: Simulate running with no arguments. Verify it calls `sys.exit(1)` and prints a usage message.
    *   **`test_main_file_not_found`**: Simulate running with a non-existent input file. Verify it raises `FileNotFoundError`.
    *   **`test_main_invalid_json`**: Simulate running with a malformed JSON file. Verify it raises `json.JSONDecodeError`.
"""

import json
import sys
import runpy
import pytest
from unittest.mock import patch, mock_open

# Assuming the code under test is in a file named 'render_mermaid.py'
import render_mermaid

# Helper function to normalize multiline strings for comparison
def clean_multiline(s):
    """Removes leading whitespace from each line and strips the whole string."""
    return "\n".join(line.strip() for line in s.strip().split('\n'))

# --- Tests for generate_mermaid_code ---

def test_full_architecture():
    """
    Tests a complete architecture with frontend, backend, shared modules, and dependencies.
    """
    architecture = [
        {"filename": "ui/HomePage.js", "priority": 1, "tags": ["frontend", "react"], "dependencies": ["api/user_service.py"]},
        {"filename": "api/user_service.py", "priority": 1, "tags": ["backend", "fastapi"], "dependencies": ["lib/database.py"]},
        {"filename": "lib/database.py", "priority": 2, "tags": ["shared"]}
    ]
    app_name = "My Full App"
    
    result = render_mermaid.generate_mermaid_code(architecture, app_name)

    expected = """
    flowchart TB
        PRD["My Full App"]

        subgraph Frontend
            HomePage["HomePage (1)"]
        end

        subgraph Backend
            user_service["user_service (1)"]
        end

        subgraph Shared
            database["database (2)"]
        end

        PRD --> Frontend
        PRD --> Backend

        HomePage -->|uses| user_service
        user_service -->|uses| database

        classDef frontend fill:#FFF3E0,stroke:#F57C00,stroke-width:2px
        classDef backend fill:#E3F2FD,stroke:#1976D2,stroke-width:2px
        classDef shared fill:#E8F5E9,stroke:#388E3C,stroke-width:2px
        classDef system fill:#E0E0E0,stroke:#616161,stroke-width:3px

        class HomePage frontend
        class user_service backend
        class database shared
        class PRD system
    """
    assert clean_multiline(result) == clean_multiline(expected)

def test_empty_architecture():
    """
    Tests with an empty list of modules.
    """
    architecture = []
    app_name = "Empty App"
    
    result = render_mermaid.generate_mermaid_code(architecture, app_name)
    
    cleaned_result = clean_multiline(result)
    assert 'flowchart TB' in cleaned_result
    assert 'PRD["Empty App"]' in cleaned_result
    assert 'subgraph' not in cleaned_result
    assert 'class PRD system' in cleaned_result
    assert 'classDef frontend' in cleaned_result

def test_frontend_only():
    """
    Tests an architecture with only frontend modules.
    """
    architecture = [
        {"filename": "Button.jsx", "tags": ["component"]},
        {"filename": "Login.jsx", "tags": ["page"]}
    ]
    result = render_mermaid.generate_mermaid_code(architecture, "UI App")
    
    cleaned_result = clean_multiline(result)
    assert 'subgraph Frontend' in cleaned_result
    assert 'subgraph Backend' not in cleaned_result
    assert 'subgraph Shared' not in cleaned_result
    assert 'PRD --> Frontend' in cleaned_result
    assert 'PRD --> Backend' not in cleaned_result
    assert 'class Button,Login frontend' in cleaned_result

def test_backend_only():
    """
    Tests an architecture with only backend modules.
    """
    architecture = [
        {"filename": "auth.py", "tags": ["api"]},
        {"filename": "models.py", "tags": ["database"]}
    ]
    result = render_mermaid.generate_mermaid_code(architecture, "API App")
    
    cleaned_result = clean_multiline(result)
    assert 'subgraph Frontend' not in cleaned_result
    assert 'subgraph Backend' in cleaned_result
    assert 'subgraph Shared' not in cleaned_result
    assert 'PRD --> Frontend' not in cleaned_result
    assert 'PRD --> Backend' in cleaned_result
    assert 'class auth,models backend' in cleaned_result

def test_shared_only():
    """
    Tests an architecture with only shared modules.
    """
    architecture = [{"filename": "logger.py", "tags": ["logging"]}]
    result = render_mermaid.generate_mermaid_code(architecture, "Shared Lib")
    
    cleaned_result = clean_multiline(result)
    assert 'subgraph Frontend' not in cleaned_result
    assert 'subgraph Backend' not in cleaned_result
    assert 'subgraph Shared' in cleaned_result
    assert 'PRD --> Frontend' not in cleaned_result
    assert 'PRD --> Backend' not in cleaned_result
    assert 'class logger shared' in cleaned_result

def test_frontend_priority_rule():
    """
    Tests that a module with both frontend and backend tags is classified as frontend.
    """
    architecture = [
        {"filename": "bff_service.ts", "tags": ["frontend", "api"]}
    ]
    result = render_mermaid.generate_mermaid_code(architecture, "BFF App")
    
    cleaned_result = clean_multiline(result)
    assert 'subgraph Frontend' in cleaned_result
    assert 'bff_service["bff_service (0)"]' in cleaned_result
    assert 'subgraph Backend' not in cleaned_result
    assert 'class bff_service frontend' in cleaned_result

def test_missing_optional_fields():
    """
    Tests a module with only the required 'filename' field.
    """
    architecture = [{"filename": "config.yml"}]
    result = render_mermaid.generate_mermaid_code(architecture, "Config Only")
    
    cleaned_result = clean_multiline(result)
    assert 'subgraph Shared' in cleaned_result
    assert 'config["config (0)"]' in cleaned_result # Priority defaults to 0
    assert 'class config shared' in cleaned_result

def test_complex_filenames():
    """
    Tests that node names are correctly extracted from complex file paths and multi-dot names.
    """
    architecture = [
        {"filename": "src/components/forms/Input.tsx", "tags": ["component"]},
        {"filename": "api.v1.users.py", "tags": ["api"], "dependencies": ["src/components/forms/Input.tsx"]}
    ]
    result = render_mermaid.generate_mermaid_code(architecture, "Complex Names")
    
    cleaned_result = clean_multiline(result)
    assert 'Input["Input (0)"]' in cleaned_result
    assert 'api.v1.users["api.v1.users (0)"]' in cleaned_result
    assert 'api.v1.users -->|uses| Input' in cleaned_result

def test_no_dependencies():
    """
    Tests an architecture where modules exist but have no dependencies.
    """
    architecture = [
        {"filename": "moduleA.py", "tags": ["backend"]},
        {"filename": "moduleB.py", "tags": ["backend"]}
    ]
    result = render_mermaid.generate_mermaid_code(architecture, "No Deps")
    assert '-->|uses|' not in result

# --- Tests for generate_html ---

def test_html_generation_with_data():
    """
    Verifies correct embedding of app name, mermaid code, and module data.
    """
    mermaid_code = 'flowchart TB\n    A --> B'
    architecture = [
        {"filename": "moduleA.py", "priority": 1, "tags": ["tagA"], "description": "Module A desc", "filepath": "src/a.py"}
    ]
    app_name = "HTML Test App"
    
    html = render_mermaid.generate_html(mermaid_code, architecture, app_name)
    
    assert f'<title>{app_name}</title>' in html
    assert f'<h1>{app_name}</h1>' in html
    assert f'<pre class="mermaid">{mermaid_code}</pre>' in html
    
    expected_json_data = {
        "moduleA": {
            "filename": "moduleA.py",
            "priority": 1,
            "description": "Module A desc",
            "dependencies": [],
            "tags": ["tagA"],
            "filepath": "src/a.py"
        }
    }
    assert f'const moduleData = {json.dumps(expected_json_data)};' in html

def test_html_generation_special_chars():
    """
    Tests that special characters in module data are correctly escaped in the embedded JSON.
    """
    mermaid_code = 'flowchart TB\n    A'
    architecture = [
        {"filename": "moduleA.py", "description": 'This is a "description" with \'quotes\' and a \n newline.'}
    ]
    app_name = "Special Chars"
    
    html = render_mermaid.generate_html(mermaid_code, architecture, app_name)
    
    expected_json_data = {
        "moduleA": {
            "filename": "moduleA.py",
            "priority": "N/A",
            "description": 'This is a "description" with \'quotes\' and a \n newline.',
            "dependencies": [],
            "tags": [],
            "filepath": ""
        }
    }
    assert f'const moduleData = {json.dumps(expected_json_data)};' in html

def test_html_generation_empty_architecture():
    """
    Tests HTML generation with an empty architecture, expecting empty module data.
    """
    html = render_mermaid.generate_html("flowchart TB", [], "Empty Arch")
    assert 'const moduleData = {};' in html

# --- Tests for CLI and Main Execution ---

@patch('sys.argv', ['render_mermaid.py', 'test.json', 'My App', 'output.html'])
@patch('builtins.open', new_callable=mock_open, read_data='[{"filename": "a.py"}]')
@patch('builtins.print')
def test_main_success_all_args(mock_print, mock_file):
    """
    Tests the main execution path with all arguments provided.
    """
    runpy.run_module('render_mermaid', run_name='__main__')

    mock_file.assert_any_call('test.json')
    mock_file.assert_called_with('output.html', 'w')
    handle = mock_file()
    
    written_content = handle.write.call_args[0][0]
    assert '<h1>My App</h1>' in written_content
    assert 'a["a (0)"]' in written_content
    
    mock_print.assert_any_call("✅ Generated: output.html")

@patch('sys.argv', ['render_mermaid.py', 'arch.json'])
@patch('builtins.open', new_callable=mock_open, read_data='[]')
@patch('builtins.print')
def test_main_success_default_args(mock_print, mock_file):
    """
    Tests the main execution path with default arguments for app name and output file.
    """
    runpy.run_module('render_mermaid', run_name='__main__')

    mock_file.assert_called_with('arch_diagram.html', 'w')
    handle = mock_file()
    
    written_content = handle.write.call_args[0][0]
    assert '<h1>System Architecture</h1>' in written_content
    
    mock_print.assert_any_call("✅ Generated: arch_diagram.html")

@patch('sys.argv', ['render_mermaid.py'])
@patch('builtins.print')
def test_main_no_args(mock_print):
    """
    Tests that the script exits and prints usage if no arguments are given.
    """
    with pytest.raises(SystemExit) as e:
        runpy.run_module('render_mermaid', run_name='__main__')
    
    assert e.value.code == 1
    mock_print.assert_called_with("Usage: python render_mermaid.py <architecture.json> [app_name] [output.html]")

@patch('sys.argv', ['render_mermaid.py', 'nonexistent.json'])
def test_main_file_not_found():
    """
    Tests that FileNotFoundError is raised for a missing input file.
    """
    with pytest.raises(FileNotFoundError):
        runpy.run_module('render_mermaid', run_name='__main__')

@patch('sys.argv', ['render_mermaid.py', 'bad.json'])
@patch('builtins.open', new_callable=mock_open, read_data='[{"filename": "a.py",}]') # Invalid JSON
def test_main_invalid_json(mock_file):
    """
    Tests that json.JSONDecodeError is raised for a malformed JSON file.
    """
    with pytest.raises(json.JSONDecodeError):
        runpy.run_module('render_mermaid', run_name='__main__')