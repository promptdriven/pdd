# test_render_mermaid.py

"""
Test Plan for render_mermaid.py

I. Z3 Formal Verification vs. Unit Tests Analysis

The core logic of the script involves categorizing modules based on a set of predefined tags. The rules are:
1. If a module has a 'frontend' tag, it's in the Frontend category.
2. If a module does not have a 'frontend' tag but has a 'backend' tag, it's in the Backend category.
3. Otherwise, it's in the Shared category.

This logic is a simple, prioritized if-elif-else structure. We could model this in Z3 to prove properties like "a module can never be categorized as both Frontend and Backend". However, the implementation is straightforward (using list comprehensions with exclusion), and the logical space is small. A few well-crafted unit tests can exhaustively verify this categorization logic more practically and directly than setting up a Z3 model. For instance, a test case with a module containing both 'frontend' and 'backend' tags is sufficient to prove the priority rule.

Therefore, unit tests are the more suitable and efficient method for ensuring the correctness of this script. They can directly test the string outputs, file I/O, and command-line interactions, which are beyond the scope of Z3.

II. Detailed Unit Test Plan

We will test the two main functions (`generate_mermaid_code`, `generate_html`) and the main execution block.

1.  **`generate_mermaid_code` Function Tests:**
    *   **test_basic_structure:** Test with a full architecture (frontend, backend, shared modules, and dependencies) to ensure all parts of the Mermaid syntax are generated correctly (subgraphs, nodes, links, classes).
    *   **test_empty_architecture:** Test with an empty list of modules. The output should be a valid, minimal Mermaid diagram with only the main app node.
    *   **test_frontend_only:** Test with only frontend modules. Ensure only the Frontend subgraph is created and linked from the main app node.
    *   **test_backend_only:** Test with only backend modules. Ensure only the Backend subgraph is created and linked.
    *   **test_shared_only:** Test with only shared modules. Ensure only the Shared subgraph is created and there are no links from the main app node to subgraphs.
    *   **test_frontend_priority:** Test a module with both frontend and backend tags. It must be categorized as frontend.
    *   **test_missing_optional_fields:** Test a module with only the required 'filename'. It should default to priority 0 and be categorized as 'Shared'.
    *   **test_complex_filenames:** Test with filenames containing paths and multiple dots. The node name should be correctly extracted as the file's stem.

2.  **`generate_html` Function Tests:**
    *   **test_html_generation:** Verify that the function correctly embeds the app name, Mermaid code, and module data into the HTML template. Check for the presence of the title, h1, mermaid code block, and the embedded JSON data for tooltips.

3.  **CLI and Main Execution Block Tests (Integration Tests):**
    *   **test_main_success_all_args:** Simulate running the script with all three command-line arguments (input file, app name, output file). Verify the correct output file is created with the correct content.
    *   **test_main_success_default_args:** Simulate running with only the required input file. Verify the default app name and output filename are used.
    *   **test_main_no_args:** Simulate running with no arguments. Verify it exits with a non-zero status code and prints a usage message.
    *   **test_main_file_not_found:** Simulate running with a non-existent input file. Verify it raises `FileNotFoundError`.
    *   **test_main_invalid_json:** Simulate running with a malformed JSON file. Verify it raises `json.JSONDecodeError`.
"""

import json
import sys
import pytest
from unittest.mock import patch, mock_open

# Assuming the code under test is in a file named 'render_mermaid.py'
# If the file has a different name, adjust the import
import render_mermaid

# Helper function to create a consistent, readable multiline string
def clean_multiline(s):
    return "\n".join(line.strip() for line in s.strip().split('\n'))

# --- Tests for generate_mermaid_code ---

def test_basic_structure():
    """
    Tests a standard architecture with frontend, backend, shared, and dependencies.
    """
    architecture = [
        {"filename": "ui.js", "priority": 1, "tags": ["frontend"], "dependencies": ["api.py"]},
        {"filename": "api.py", "priority": 1, "tags": ["backend"], "dependencies": ["utils.py"]},
        {"filename": "utils.py", "priority": 2, "tags": ["shared"]}
    ]
    app_name = "My Test App"
    
    result = render_mermaid.generate_mermaid_code(architecture, app_name)

    expected = """
    flowchart TB
        PRD["My Test App"]

        subgraph Frontend
            ui["ui (1)"]
        end

        subgraph Backend
            api["api (1)"]
        end

        subgraph Shared
            utils["utils (2)"]
        end

        PRD --> Frontend
        PRD --> Backend

        ui -->|uses| api
        api -->|uses| utils

        classDef frontend fill:#FFF3E0,stroke:#F57C00,stroke-width:2px
        classDef backend fill:#E3F2FD,stroke:#1976D2,stroke-width:2px
        classDef shared fill:#E8F5E9,stroke:#388E3C,stroke-width:2px
        classDef system fill:#E0E0E0,stroke:#616161,stroke-width:3px

        class ui frontend
        class api backend
        class utils shared
        class PRD system
    """
    assert clean_multiline(result) == clean_multiline(expected)

def test_empty_architecture():
    """
    Tests an empty architecture list.
    """
    architecture = []
    app_name = "Empty App"
    
    result = render_mermaid.generate_mermaid_code(architecture, app_name)
    
    expected = """
    flowchart TB
        PRD["Empty App"]


        classDef frontend fill:#FFF3E0,stroke:#F57C00,stroke-width:2px
        classDef backend fill:#E3F2FD,stroke:#1976D2,stroke-width:2px
        classDef shared fill:#E8F5E9,stroke:#388E3C,stroke-width:2px
        classDef system fill:#E0E0E0,stroke:#616161,stroke-width:3px

        class PRD system
    """
    assert clean_multiline(result) == clean_multiline(expected)

def test_frontend_only():
    """
    Tests an architecture with only frontend modules.
    """
    architecture = [
        {"filename": "HomePage.jsx", "tags": ["react", "page"]},
        {"filename": "Button.jsx", "tags": ["react", "component"]}
    ]
    result = render_mermaid.generate_mermaid_code(architecture, "Frontend App")
    
    assert 'subgraph Frontend' in result
    assert 'subgraph Backend' not in result
    assert 'subgraph Shared' not in result
    assert 'PRD --> Frontend' in result
    assert 'PRD --> Backend' not in result
    assert 'class HomePage,Button frontend' in result

def test_backend_only():
    """
    Tests an architecture with only backend modules.
    """
    architecture = [
        {"filename": "users_api.py", "tags": ["fastapi"]},
        {"filename": "db_models.py", "tags": ["sqlalchemy"]}
    ]
    result = render_mermaid.generate_mermaid_code(architecture, "Backend App")
    
    assert 'subgraph Frontend' not in result
    assert 'subgraph Backend' in result
    assert 'subgraph Shared' not in result
    assert 'PRD --> Frontend' not in result
    assert 'PRD --> Backend' in result
    assert 'class users_api,db_models backend' in result

def test_shared_only():
    """
    Tests an architecture with only shared modules.
    """
    architecture = [{"filename": "logger.py", "tags": ["utils"]}]
    result = render_mermaid.generate_mermaid_code(architecture, "Shared App")
    
    assert 'subgraph Frontend' not in result
    assert 'subgraph Backend' not in result
    assert 'subgraph Shared' in result
    assert 'PRD --> Frontend' not in result
    assert 'PRD --> Backend' not in result
    assert 'class logger shared' in result

def test_frontend_priority():
    """
    Tests that a module with both frontend and backend tags is classified as frontend.
    """
    architecture = [
        {"filename": "trpc_router.ts", "tags": ["frontend", "api"]}
    ]
    result = render_mermaid.generate_mermaid_code(architecture, "Fullstack")
    
    assert 'subgraph Frontend' in result
    assert 'trpc_router["trpc_router (0)"]' in result
    assert 'subgraph Backend' not in result
    assert 'class trpc_router frontend' in result

def test_missing_optional_fields():
    """
    Tests a module with only the required 'filename' field.
    """
    architecture = [{"filename": "config.py"}]
    result = render_mermaid.generate_mermaid_code(architecture, "Minimal")
    
    assert 'subgraph Shared' in result
    assert 'config["config (0)"]' in result # Priority defaults to 0
    assert 'class config shared' in result

def test_complex_filenames():
    """
    Tests that node names are correctly extracted from complex file paths.
    """
    architecture = [
        {"filename": "src/components/forms/Input.tsx", "tags": ["component"]},
        {"filename": "api.v1.users.py", "tags": ["api"], "dependencies": ["src/components/forms/Input.tsx"]}
    ]
    result = render_mermaid.generate_mermaid_code(architecture, "Complex Names")
    
    assert 'Input["Input (0)"]' in result
    assert 'api.v1.users["api.v1.users (0)"]' in result
    assert 'api.v1.users -->|uses| Input' in result

# --- Tests for generate_html ---

def test_html_generation():
    """
    Tests that the HTML is generated correctly with embedded data.
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
    
    # Check for correctly embedded JSON data
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

# --- Tests for CLI and Main Execution ---

@patch('sys.argv', ['render_mermaid.py', 'test.json', 'My App', 'output.html'])
@patch('builtins.open', new_callable=mock_open, read_data='[{"filename": "a.py"}]')
@patch('render_mermaid.print')
def test_main_success_all_args(mock_print, mock_file):
    """
    Tests the main execution path with all arguments provided.
    """
    render_mermaid.__main__.__spec__ = "ModuleSpec(name='__main__')" # Mock the __main__ context
    # This is a simple way to execute the script's main block
    with patch.dict('sys.modules', {'__main__': render_mermaid.__main__}):
        # Re-importing or running the code inside the main guard
        from importlib import reload
        reload(render_mermaid)

    # Check that the output file was written to
    mock_file.assert_called_with('output.html', 'w')
    handle = mock_file()
    
    # Check the content written
    written_content = handle.write.call_args[0][0]
    assert '<h1>My App</h1>' in written_content
    assert 'a["a (0)"]' in written_content
    
    # Check success messages
    mock_print.assert_any_call("✅ Generated: output.html")
    mock_print.assert_any_call("📊 Modules: 1")

@patch('sys.argv', ['render_mermaid.py', 'arch.json'])
@patch('builtins.open', new_callable=mock_open, read_data='[]')
@patch('render_mermaid.print')
def test_main_success_default_args(mock_print, mock_file):
    """
    Tests the main execution path with default arguments for app name and output file.
    """
    render_mermaid.__main__.__spec__ = "ModuleSpec(name='__main__')"
    with patch.dict('sys.modules', {'__main__': render_mermaid.__main__}):
        from importlib import reload
        reload(render_mermaid)

    # Check that the default output file was written to
    mock_file.assert_called_with('arch_diagram.html', 'w')
    handle = mock_file()
    
    # Check for default app name
    written_content = handle.write.call_args[0][0]
    assert '<h1>System Architecture</h1>' in written_content
    
    # Check success messages
    mock_print.assert_any_call("✅ Generated: arch_diagram.html")

@patch('sys.argv', ['render_mermaid.py'])
@patch('render_mermaid.print')
def test_main_no_args(mock_print):
    """
    Tests that the script exits and prints usage if no arguments are given.
    """
    with pytest.raises(SystemExit) as e:
        render_mermaid.__main__.__spec__ = "ModuleSpec(name='__main__')"
        with patch.dict('sys.modules', {'__main__': render_mermaid.__main__}):
            from importlib import reload
            reload(render_mermaid)
    
    assert e.value.code == 1
    mock_print.assert_called_with("Usage: python render_mermaid.py <architecture.json> [app_name] [output.html]")

@patch('sys.argv', ['render_mermaid.py', 'nonexistent.json'])
def test_main_file_not_found():
    """
    Tests that FileNotFoundError is raised for a missing input file.
    """
    with pytest.raises(FileNotFoundError):
        render_mermaid.__main__.__spec__ = "ModuleSpec(name='__main__')"
        with patch.dict('sys.modules', {'__main__': render_mermaid.__main__}):
            from importlib import reload
            reload(render_mermaid)

@patch('sys.argv', ['render_mermaid.py', 'bad.json'])
@patch('builtins.open', new_callable=mock_open, read_data='[{"filename": "a.py",}]') # Invalid JSON with trailing comma
def test_main_invalid_json(mock_file):
    """
    Tests that json.JSONDecodeError is raised for a malformed JSON file.
    """
    with pytest.raises(json.JSONDecodeError):
        render_mermaid.__main__.__spec__ = "ModuleSpec(name='__main__')"
        with patch.dict('sys.modules', {'__main__': render_mermaid.__main__}):
            from importlib import reload
            reload(render_mermaid)
