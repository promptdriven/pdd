# test_render_mermaid.py

# ############################################################################
# Test Plan
# ############################################################################
#
# Test Suite: `render_mermaid.py`
#
# Objective: Verify the correct generation of Mermaid code and HTML from various
# `architecture.json` inputs, and ensure the command-line interface works as expected.
#
# Fixtures:
#   - `tmp_path`: Pytest fixture to create temporary files and directories for test isolation.
#   - `create_arch_file`: A helper fixture to create a temporary `architecture.json`
#     file with given content, simplifying test setup.
#
# Test Groups:
#
# 1. `generate_mermaid_code` Function Tests:
#    - `test_basic_structure`: Test with a mix of frontend, backend, and shared modules.
#      Verify the presence of `flowchart TB`, the app name node, all three subgraphs,
#      correct node labels (`name (priority)`), and dependency arrows.
#    - `test_empty_architecture`: Test with an empty JSON array (`[]`). The output should
#      be minimal, containing only the `flowchart TB`, the app name node, and class
#      definitions. No subgraphs or dependencies should be generated.
#    - `test_missing_optional_keys`: Test a module with only the required `filename` key.
#      Verify it's categorized as 'shared' and has a default priority of 0 in the node label.
#    - `test_categorization_priority`: Test a module with both 'frontend' and 'backend' tags.
#      Verify it is placed in the 'Frontend' subgraph only, as per the implementation logic.
#    - `test_uncategorized_as_shared`: Test a module with no tags or with tags not in the
#      predefined lists. Verify it is placed in the 'Shared' subgraph.
#    - `test_single_category_frontend`: Test with only frontend modules. Verify only the
#      'Frontend' subgraph is created and the main app node (`PRD`) connects to it.
#    - `test_single_category_backend`: Test with only backend modules. Verify only the
#      'Backend' subgraph is created and `PRD` connects to it.
#    - `test_single_category_shared`: Test with only shared modules. Verify only the
#      'Shared' subgraph is created and `PRD` does *not* connect to it directly.
#    - `test_filename_parsing`: Test with complex filenames like `path/to/my.component.js`.
#      Verify the node name is correctly extracted as `my.component`.
#
# 2. `generate_html` Function Tests:
#    - `test_html_structure`: Test with a sample architecture. Verify the output is a valid
#      HTML structure containing the app name in `<title>` and `<h1>`, the mermaid code in a
#      `<pre class="mermaid">` block, and a `<table>`.
#    - `test_html_table_content`: Verify the table is correctly populated. Check for correct
#      data, and that missing tags/dependencies are handled gracefully (e.g., show a hyphen).
#    - `test_html_table_sorting`: Test with modules having various priorities, including a
#      missing priority. Verify the table rows are sorted correctly (1, 2, 10, then missing).
#    - `test_html_escaping_vulnerability`: Test with an app name containing HTML characters
#      (e.g., `My <App>`). The test will assert that the characters are *not* escaped,
#      highlighting a potential XSS vulnerability in the current implementation.
#
# 3. Command-Line Interface (CLI) Tests:
#    - `test_cli_no_args`: Use `subprocess` to run the script with no arguments. Verify it
#      prints the usage message and exits with a non-zero status code.
#    - `test_cli_min_args`: Simulate running with just the input file. Verify it creates an
#      output file with the default name (`{stem}_diagram.html`) and default app name.
#    - `test_cli_with_app_name`: Simulate running with input file and app name. Verify the
#      output file has the default name but uses the specified app name.
#    - `test_cli_all_args`: Simulate running with all three arguments. Verify it creates the
#      specified output file with the specified app name.
#    - `test_cli_file_not_found`: Simulate running with a non-existent input file. Verify
#      the script exits with a non-zero status code.
#    - `test_cli_invalid_json`: Simulate running with a malformed JSON file. Verify the
#      script exits with a non-zero status code due to a `json.JSONDecodeError`.
#    - `test_cli_success_message`: For a successful run, capture `stdout` and verify it
#      prints the correct success message with the module count and output filename.
#
# ############################################################################

import pytest
import json
import subprocess
import sys
from pathlib import Path

# Assuming the script is named 'render_mermaid.py' and is in the same directory
# If not, adjust the path accordingly.
SCRIPT_PATH = Path(__file__).parent / "render_mermaid.py"

# Check if the script exists before running tests
if not SCRIPT_PATH.exists():
    pytest.skip("render_mermaid.py not found", allow_module_level=True)

from render_mermaid import generate_mermaid_code, generate_html

@pytest.fixture
def create_arch_file(tmp_path):
    """Fixture to create a temporary architecture.json file for tests."""
    def _create_file(data):
        arch_file = tmp_path / "architecture.json"
        arch_file.write_text(json.dumps(data))
        return arch_file
    return _create_file

# --- 1. `generate_mermaid_code` Function Tests ---

def test_basic_structure():
    """Verify correct Mermaid code for a mixed-module architecture."""
    arch = [
        {"filename": "ui/HomePage.js", "priority": 1, "tags": ["frontend", "page"], "dependencies": ["utils/api.js"]},
        {"filename": "api/main.py", "priority": 1, "tags": ["backend", "api"], "dependencies": ["db/models.py"]},
        {"filename": "utils/api.js", "priority": 2, "tags": ["shared"]},
        {"filename": "db/models.py", "priority": 2, "tags": ["database"]}
    ]
    code = generate_mermaid_code(arch, "My Test App")

    assert 'flowchart TB' in code
    assert 'PRD["My Test App"]' in code
    assert 'subgraph Frontend' in code
    assert 'HomePage["HomePage (1)"]' in code
    assert 'subgraph Backend' in code
    assert 'main["main (1)"]' in code
    assert 'models["models (2)"]' in code
    assert 'subgraph Shared' in code
    assert 'api["api (2)"]' in code
    assert 'HomePage -->|uses| api' in code
    assert 'main -->|uses| models' in code
    assert 'PRD --> Frontend' in code
    assert 'PRD --> Backend' in code
    assert 'class HomePage frontend' in code
    assert 'class main,models backend' in code
    assert 'class api shared' in code
    assert 'class PRD system' in code

def test_empty_architecture():
    """Verify output for an empty architecture list."""
    code = generate_mermaid_code([], "Empty App")
    assert 'flowchart TB' in code
    assert 'PRD["Empty App"]' in code
    assert 'subgraph' not in code
    assert '-->' not in code
    assert 'classDef' in code
    assert 'class PRD system' in code

def test_missing_optional_keys():
    """Verify a module with only a filename is handled correctly."""
    arch = [{"filename": "config.js"}]
    code = generate_mermaid_code(arch, "Config App")
    assert 'subgraph Shared' in code
    # Default priority is 0
    assert 'config["config (0)"]' in code
    assert 'class config shared' in code

def test_categorization_priority():
    """Verify a module with both frontend and backend tags is classified as frontend."""
    arch = [{"filename": "GraphQLBridge.ts", "tags": ["frontend", "api"]}]
    code = generate_mermaid_code(arch, "Bridge App")
    assert 'subgraph Frontend' in code
    assert 'GraphQLBridge["GraphQLBridge (0)"]' in code
    assert 'subgraph Backend' not in code
    assert 'class GraphQLBridge frontend' in code

def test_uncategorized_as_shared():
    """Verify modules with no tags or non-matching tags go to Shared."""
    arch = [
        {"filename": "logger.py"},
        {"filename": "docs_generator.py", "tags": ["docs"]}
    ]
    code = generate_mermaid_code(arch, "Utils App")
    assert 'subgraph Shared' in code
    assert 'logger["logger (0)"]' in code
    assert 'docs_generator["docs_generator (0)"]' in code
    assert 'subgraph Frontend' not in code
    assert 'subgraph Backend' not in code

def test_single_category_frontend():
    """Verify correct output for a frontend-only architecture."""
    arch = [{"filename": "App.jsx", "tags": ["react", "frontend"]}]
    code = generate_mermaid_code(arch, "React App")
    assert 'subgraph Frontend' in code
    assert 'subgraph Backend' not in code
    assert 'subgraph Shared' not in code
    assert 'PRD --> Frontend' in code
    assert 'PRD --> Backend' not in code

def test_single_category_backend():
    """Verify correct output for a backend-only architecture."""
    arch = [{"filename": "server.js", "tags": ["backend"]}]
    code = generate_mermaid_code(arch, "Node App")
    assert 'subgraph Backend' in code
    assert 'subgraph Frontend' not in code
    assert 'subgraph Shared' not in code
    assert 'PRD --> Backend' in code
    assert 'PRD --> Frontend' not in code

def test_single_category_shared():
    """Verify correct output for a shared-only architecture."""
    arch = [{"filename": "common/types.ts", "tags": ["shared"]}]
    code = generate_mermaid_code(arch, "Types App")
    assert 'subgraph Shared' in code
    assert 'subgraph Frontend' not in code
    assert 'subgraph Backend' not in code
    assert 'PRD --> Frontend' not in code
    assert 'PRD --> Backend' not in code

def test_filename_parsing():
    """Verify Path.stem correctly extracts module names from complex paths."""
    arch = [{"filename": "src/components/ui/Button.spec.tsx"}]
    code = generate_mermaid_code(arch, "Test App")
    # Path('...').stem will be 'Button.spec'
    assert 'Button.spec["Button.spec (0)"]' in code

# --- 2. `generate_html` Function Tests ---

def test_html_structure():
    """Verify the basic structure of the generated HTML."""
    arch = [{"filename": "main.py", "priority": 1, "tags": ["backend"]}]
    mermaid_code = "flowchart TB\n..."
    html = generate_html(mermaid_code, arch, "Test HTML App")

    assert '<!DOCTYPE html>' in html
    assert '<title>Test HTML App</title>' in html
    assert '<h1>Test HTML App</h1>' in html
    assert '<pre class="mermaid">flowchart TB\n...</pre>' in html
    assert '<table>' in html
    assert '<th>Priority</th>' in html
    assert '<td><strong>main.py</strong></td>' in html

def test_html_table_sorting():
    """Verify the module table is sorted by priority."""
    arch = [
        {"filename": "c.js", "priority": 10},
        {"filename": "d.js"}, # Missing priority, should be last
        {"filename": "a.js", "priority": 1},
        {"filename": "b.js", "priority": 2},
    ]
    html = generate_html("", arch, "Sort App")
    
    # Find the order of filenames in the generated table rows
    body_content = html.split('<tbody>')[1].split('</tbody>')[0]
    rows = [row for row in body_content.split('<tr>') if '<td>' in row]
    
    assert '<strong>a.js</strong>' in rows[0]
    assert '<strong>b.js</strong>' in rows[1]
    assert '<strong>c.js</strong>' in rows[2]
    assert '<strong>d.js</strong>' in rows[3]
    assert '<td>-</td>' in rows[3] # Check missing priority display

def test_html_table_content_empty_fields():
    """Verify empty/missing optional fields are displayed gracefully."""
    arch = [{"filename": "module.js"}]
    html = generate_html("", arch, "Empty Fields App")
    assert '<td>-</td>' in html # Priority
    assert '<td></td>' in html # Tags
    assert '<td>-</td>' in html # Dependencies

def test_html_escaping_vulnerability():
    """Test that HTML special characters in app_name are not escaped."""
    app_name = 'My App <script>alert("XSS")</script>'
    html = generate_html("", [], app_name)
    # This test confirms the vulnerability. A secure implementation would fail this test.
    assert f'<h1>{app_name}</h1>' in html
    assert f'<title>{app_name}</title>' in html

# --- 3. Command-Line Interface (CLI) Tests ---

def test_cli_no_args():
    """Verify the script exits with a usage message when no args are provided."""
    result = subprocess.run(
        [sys.executable, str(SCRIPT_PATH)],
        capture_output=True, text=True
    )
    assert result.returncode != 0
    assert "Usage:" in result.stdout

def test_cli_file_not_found():
    """Verify the script fails for a non-existent input file."""
    result = subprocess.run(
        [sys.executable, str(SCRIPT_PATH), "nonexistent.json"],
        capture_output=True, text=True
    )
    assert result.returncode != 0
    # The script will raise FileNotFoundError, which prints to stderr
    assert "FileNotFoundError" in result.stderr or "No such file or directory" in result.stderr

def test_cli_invalid_json(create_arch_file):
    """Verify the script fails for a malformed JSON file."""
    arch_file = create_arch_file(None) # create_arch_file expects a list/dict
    arch_file.write_text("{'invalid': 'json'}") # Write invalid JSON
    
    result = subprocess.run(
        [sys.executable, str(SCRIPT_PATH), str(arch_file)],
        capture_output=True, text=True
    )
    assert result.returncode != 0
    assert "json.decoder.JSONDecodeError" in result.stderr

def test_cli_min_args(create_arch_file, tmp_path):
    """Test CLI with only the required input file argument."""
    arch_file = create_arch_file([{"filename": "main.py"}])
    
    result = subprocess.run(
        [sys.executable, str(SCRIPT_PATH), str(arch_file)],
        capture_output=True, text=True, cwd=tmp_path
    )
    
    assert result.returncode == 0
    
    output_file = tmp_path / "architecture_diagram.html"
    assert output_file.exists()
    
    html = output_file.read_text()
    assert "<title>System Architecture</title>" in html
    assert "<h1>System Architecture</h1>" in html
    assert "main.py" in html

def test_cli_with_app_name(create_arch_file, tmp_path):
    """Test CLI with input file and app name."""
    arch_file = create_arch_file([])
    
    result = subprocess.run(
        [sys.executable, str(SCRIPT_PATH), str(arch_file), "My Custom App"],
        capture_output=True, text=True, cwd=tmp_path
    )
    
    assert result.returncode == 0
    
    output_file = tmp_path / "architecture_diagram.html"
    assert output_file.exists()
    
    html = output_file.read_text()
    assert "<title>My Custom App</title>" in html
    assert "<h1>My Custom App</h1>" in html

def test_cli_all_args(create_arch_file, tmp_path):
    """Test CLI with all three arguments."""
    arch_file = create_arch_file([])
    custom_output_path = tmp_path / "custom.html"
    
    result = subprocess.run(
        [sys.executable, str(SCRIPT_PATH), str(arch_file), "Full CLI App", str(custom_output_path)],
        capture_output=True, text=True, cwd=tmp_path
    )
    
    assert result.returncode == 0
    assert custom_output_path.exists()
    
    html = custom_output_path.read_text()
    assert "<title>Full CLI App</title>" in html
    assert "<h1>Full CLI App</h1>" in html

def test_cli_success_message(create_arch_file, tmp_path):
    """Verify the success message is printed to stdout."""
    arch_file = create_arch_file([{"filename": "a.py"}, {"filename": "b.py"}])
    output_file = "arch_diagram.html"
    
    result = subprocess.run(
        [sys.executable, str(SCRIPT_PATH), str(arch_file), "Success App", output_file],
        capture_output=True, text=True, cwd=tmp_path
    )
    
    assert result.returncode == 0
    assert f"✅ Generated: {output_file}" in result.stdout
    assert "📊 Modules: 2" in result.stdout
    assert f"🌐 Open {output_file} in your browser!" in result.stdout