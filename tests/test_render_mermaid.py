# test_render_mermaid.py
import pytest
import json
import html
from pathlib import Path

from pdd.render_mermaid import generate_mermaid_code, generate_html, write_pretty_architecture_json


# Test Plan
#
# 1. Formal Verification (Z3) vs. Unit Tests
#    - The code's primary function is string manipulation and generation based on conditional logic (parsing JSON and formatting into Mermaid/HTML).
#    - The logic for categorization is a series of set-based checks (is tag in list A? if not, is it in list B?). This is straightforward and doesn't involve complex constraints, mathematical properties, or state transitions that would benefit from a Z3 solver.
#    - Unit tests are far more suitable for this task. They allow us to provide specific inputs (JSON data structures) and assert the correctness of the generated string outputs, which is the core requirement.
#    - Therefore, this test suite will exclusively use unit tests (Pytest).
#
# 2. Unit Test Plan
#
#    A. `generate_mermaid_code` Function Tests
#       - `test_empty_architecture`: Ensure it handles an empty list of modules gracefully, generating a diagram with only the main app node.
#       - `test_full_architecture`: Test with a mix of frontend, backend, and shared modules to verify correct subgraph generation, node labeling, dependencies, and styling classes.
#       - `test_categorization_priority`: Verify that a module with both frontend and backend tags is correctly placed in the "Frontend" subgraph.
#       - `test_no_tags_is_shared`: Check that a module with no tags or non-matching tags defaults to the "Shared" category.
#       - `test_single_category_subgraphs`: Test scenarios with only frontend, only backend, or only shared modules to ensure only the necessary subgraphs and connections are created.
#       - `test_missing_optional_fields`: Ensure modules without `priority` or `dependencies` are handled with correct defaults (priority 0, no dependency arrows).
#       - `test_filename_parsing`: Verify that the module name is correctly extracted from a complex file path (e.g., `src/components/Button.js` -> `Button`).
#       - `test_special_chars_in_app_name`: Check if special characters (like quotes) in the app name are properly handled in the Mermaid syntax. The current implementation is expected to fail this, highlighting a bug.
#
#    B. `generate_html` Function Tests
#       - `test_html_structure_and_content`: Verify the overall structure of the generated HTML, ensuring the title, header, and Mermaid code are correctly placed.
#       - `test_module_data_embedding`: Check that the architecture data is correctly serialized into a JSON object within the HTML's script tag for use in tooltips.
#       - `test_html_embedding_with_missing_fields`: Ensure modules with missing optional fields (like `description`, `priority`) are represented with default values in the embedded JSON.
#       - `test_html_escaping`: Test if characters that have special meaning in HTML (e.g., `<`, `>`, `&`) are properly escaped in the output to prevent rendering issues or XSS vulnerabilities. The current implementation is expected to fail this.
#
#    C. CLI / `__main__` block (Not Tested)
#       - Testing the `__main__` block requires mocking `sys.argv`, file system operations (`open`), and `sys.exit`.
#       - Since the core logic is encapsulated in `generate_mermaid_code` and `generate_html`, unit testing these functions provides higher value and better isolation. The CLI tests would be more integration-focused. For this exercise, we will focus on the core functions.


# --- Test Fixtures ---
@pytest.fixture
def full_architecture():
    """A comprehensive architecture with frontend, backend, and shared modules."""
    return [
        {
            "filename": "src/pages/HomePage.jsx",
            "priority": 1,
            "dependencies": ["src/components/Header.jsx", "src/services/apiClient.js"],
            "tags": ["frontend", "page", "react"],
            "description": "The main landing page.",
        },
        {
            "filename": "src/components/Header.jsx",
            "priority": 3,
            "dependencies": [],
            "tags": ["frontend", "component", "ui"],
        },
        {
            "filename": "src/api/main.py",
            "priority": 1,
            "dependencies": ["src/api/database.py"],
            "tags": ["backend", "api", "fastapi"],
        },
        {
            "filename": "src/api/database.py",
            "priority": 2,
            "dependencies": [],
            "tags": ["backend", "database"],
        },
        {
            "filename": "src/services/apiClient.js",
            "priority": 2,
            "dependencies": [],
            "tags": ["shared", "utils"],
            "description": "Shared API client.",
        },
        {
            "filename": "src/auth/user_model.py",
            "priority": 4,
            "dependencies": ["src/api/database.py"],
            "tags": ["backend", "react"],  # Mixed tags to test frontend priority
            "description": "User auth logic.",
        },
    ]


@pytest.fixture
def no_deps_architecture():
    """Architecture with modules but no dependencies."""
    return [
        {"filename": "ui.js", "tags": ["frontend"]},
        {"filename": "api.py", "tags": ["backend"]},
    ]


# --- Tests for generate_mermaid_code ---
class TestGenerateMermaidCode:
    def test_empty_architecture(self):
        """Tests that an empty architecture list produces a valid base diagram."""
        mermaid_code = generate_mermaid_code([], app_name="Empty App")
        assert 'flowchart TB' in mermaid_code
        assert 'PRD["Empty App"]' in mermaid_code
        assert 'subgraph' not in mermaid_code
        assert '-->' not in mermaid_code
        assert 'classDef system' in mermaid_code
        assert 'class PRD system' in mermaid_code

    def test_full_architecture(self, full_architecture):
        """Tests a complete architecture with all module types and dependencies."""
        mermaid_code = generate_mermaid_code(full_architecture, app_name="My App")
        # Check for app name and subgraphs
        assert 'PRD["My App"]' in mermaid_code
        assert 'subgraph Frontend' in mermaid_code
        assert 'subgraph Backend' in mermaid_code
        assert 'subgraph Shared' in mermaid_code
        # Check for PRD connections
        assert "PRD --> Frontend" in mermaid_code
        assert "PRD --> Backend" in mermaid_code
        assert "PRD --> Shared" not in mermaid_code
        # Check node definitions (name and priority)
        assert 'HomePage["HomePage (1)"]' in mermaid_code
        assert 'Header["Header (3)"]' in mermaid_code
        assert 'main["main (1)"]' in mermaid_code
        assert 'database["database (2)"]' in mermaid_code
        assert 'apiClient["apiClient (2)"]' in mermaid_code
        assert 'user_model["user_model (4)"]' in mermaid_code
        # Check dependencies
        assert "HomePage -->|uses| Header" in mermaid_code
        assert "HomePage -->|uses| apiClient" in mermaid_code
        assert "main -->|uses| database" in mermaid_code
        assert "user_model -->|uses| database" in mermaid_code
        # Check class assignments
        assert "class HomePage,Header,user_model frontend" in mermaid_code
        assert "class main,database backend" in mermaid_code
        assert "class apiClient shared" in mermaid_code
        assert "class PRD system" in mermaid_code

    def test_categorization_priority(self, full_architecture):
        """Tests that a module with both frontend and backend tags is classified as frontend."""
        mermaid_code = generate_mermaid_code(full_architecture, app_name="Test App")
        # 'user_model.py' has tags ["backend", "react"], so it should be in Frontend
        assert 'subgraph Frontend' in mermaid_code
        assert 'user_model["user_model (4)"]' in mermaid_code.split('subgraph Frontend')[1].split('end')[0]
        assert 'class HomePage,Header,user_model frontend' in mermaid_code

    def test_no_tags_is_shared(self):
        """Tests that a module with no tags is categorized as Shared."""
        arch = [{"filename": "logger.js"}]  # No 'tags' key
        mermaid_code = generate_mermaid_code(arch, "Test App")
        assert 'subgraph Shared' in mermaid_code
        assert 'logger["logger (0)"]' in mermaid_code
        assert 'class logger shared' in mermaid_code

    def test_only_frontend_modules(self):
        """Tests an architecture with only frontend modules."""
        arch = [{"filename": "ui.js", "tags": ["frontend"]}]
        mermaid_code = generate_mermaid_code(arch, "FE App")
        assert 'subgraph Frontend' in mermaid_code
        assert 'subgraph Backend' not in mermaid_code
        assert 'subgraph Shared' not in mermaid_code
        assert 'PRD --> Frontend' in mermaid_code
        assert 'PRD --> Backend' not in mermaid_code

    def test_only_backend_modules(self):
        """Tests an architecture with only backend modules."""
        arch = [{"filename": "api.py", "tags": ["backend"]}]
        mermaid_code = generate_mermaid_code(arch, "BE App")
        assert 'subgraph Frontend' not in mermaid_code
        assert 'subgraph Backend' in mermaid_code
        assert 'subgraph Shared' not in mermaid_code
        assert 'PRD --> Frontend' not in mermaid_code
        assert 'PRD --> Backend' in mermaid_code

    def test_missing_priority_and_dependencies(self):
        """Tests a module with no priority or dependencies specified."""
        arch = [{"filename": "config.js", "tags": ["shared"]}]
        mermaid_code = generate_mermaid_code(arch, "Config App")
        assert 'config["config (0)"]' in mermaid_code  # Defaults to priority 0
        assert '-->' not in mermaid_code.replace('PRD -->', '')  # No dependency arrows

    def test_filename_parsing(self):
        """Tests that module names are correctly extracted from paths."""
        arch = [{"filename": "src/deep/path/to/MyModule.test.js"}]
        mermaid_code = generate_mermaid_code(arch, "Test")
        # Path('...').stem should be 'MyModule.test'
        assert 'MyModule.test["MyModule.test (0)"]' in mermaid_code

    def test_app_name_with_special_chars(self):
        """Tests if app names with quotes are handled correctly. This test will likely fail."""
        app_name = 'My "Awesome" App'
        # The expected correct output should escape the quotes for the Mermaid label.
        expected_node = f'PRD["{app_name.replace("\"", "&quot;")} "]'  # Mermaid uses HTML entity for quotes
        mermaid_code = generate_mermaid_code([], app_name=app_name)
        # Note: The current implementation f'PRD["{app_name}"]' will produce PRD["My "Awesome" App"],
        # which is invalid. This test correctly identifies that flaw.
        assert expected_node in mermaid_code


# --- Tests for generate_html ---
class TestGenerateHTML:
    def test_html_structure_and_content(self, full_architecture):
        """Tests the basic structure and content of the generated HTML."""
        mermaid_code = "flowchart TB\n  A --> B"
        app_name = "Test HTML App"
        html_doc = generate_html(mermaid_code, full_architecture, app_name)
        assert f"<title>{app_name}</title>" in html_doc
        assert f"<h1>{app_name}</h1>" in html_doc
        assert '<pre class="mermaid">flowchart TB\n  A --> B</pre>' in html_doc
        assert 'https://cdn.jsdelivr.net/npm/mermaid@10/dist/mermaid.esm.min.mjs' in html_doc

    def test_module_data_embedding(self, full_architecture):
        """Tests that module data is correctly embedded as JSON in the script tag."""
        html_doc = generate_html("", full_architecture, "Test App")
        # Extract the JSON string from the HTML
        json_str = extract_module_data_json(html_doc)
        data = json.loads(json_str)
        assert "HomePage" in data
        assert data["HomePage"]["filename"] == "src/pages/HomePage.jsx"
        assert data["HomePage"]["priority"] == 1
        assert "The main landing page." in data["HomePage"]["description"]
        assert "Header" in data
        assert data["Header"]["dependencies"] == []

    def test_html_embedding_with_missing_fields(self):
        """Tests embedding data for a module with missing optional fields."""
        arch = [{"filename": "simple.js"}]
        html_doc = generate_html("", arch, "Test App")
        json_str = extract_module_data_json(html_doc)
        data = json.loads(json_str)
        assert "simple" in data
        assert data["simple"]["priority"] == "N/A"
        assert data["simple"]["description"] == "No description"
        assert data["simple"]["tags"] == []
        assert data["simple"]["dependencies"] == []

    def test_html_escaping(self):
        """Tests if special HTML characters in app_name and description are escaped."""
        app_name = "<App & Test>"
        arch = [{
            "filename": "xss.js",
            "description": "<script>alert('pwned')</script>",
        }]
        
        html_doc = generate_html("", arch, app_name)
        # Test escaping in title and h1
        escaped_app_name = html.escape(app_name)
        assert f"<title>{escaped_app_name}</title>" in html_doc
        assert f"<h1>{escaped_app_name}</h1>" in html_doc
        
        # Test escaping in the embedded JSON data
        json_str = extract_module_data_json(html_doc)
        data = json.loads(json_str)

        # After XSS fix: Unicode escaping in JSON source prevents literal XSS code in HTML
        # When parsed by json.loads(), Unicode escapes become original characters
        # This is safe because render_mermaid.py uses textContent (not innerHTML) for dynamic data

        # Verify the JSON source contains Unicode escapes (not literal < >)
        assert '\\u003cscript\\u003e' in json_str, \
            "JSON source should contain Unicode-escaped HTML to prevent XSS payload in HTML source"

        # After parsing, the data contains original characters (this is expected and safe)
        assert data["xss"]["description"] == "<script>alert('pwned')</script>", \
            "After JSON parsing, data contains original characters (safe with textContent)"


def test_write_pretty_architecture_json(tmp_path):
    """Ensures render_mermaid rewrites architecture.json with consistent indentation."""
    arch_path = tmp_path / "architecture.json"
    data = [
        {
            "filename": "src/api.py",
            "priority": 1,
            "dependencies": [],
            "tags": ["backend"],
        }
    ]
    arch_path.write_text(json.dumps(data), encoding="utf-8")

    write_pretty_architecture_json(arch_path, data)

    content = arch_path.read_text(encoding="utf-8")
    assert content.startswith('[\n  {\n')
    assert content.endswith('\n')
    assert json.loads(content) == data


# --- Tests for XSS Prevention (Issue #411) ---

def extract_module_data_json(html_doc):
    """Extract the moduleData JSON from the generated HTML."""
    start_marker = 'const moduleData = '
    start = html_doc.find(start_marker)
    if start == -1:
        raise ValueError("Could not find 'const moduleData = ' in HTML")

    start += len(start_marker)
    brace_count = 0
    in_string = False
    escape_next = False

    for i in range(start, len(html_doc)):
        char = html_doc[i]

        if escape_next:
            escape_next = False
            continue

        if char == '\\':
            escape_next = True
            continue

        if char == '"' and not escape_next:
            in_string = not in_string

        if not in_string:
            if char == '{':
                brace_count += 1
            elif char == '}':
                brace_count -= 1
                if brace_count == 0:
                    return html_doc[start:i+1]

    raise ValueError("Could not find end of JSON object")


class TestXSSPreventionIssue411:
    """
    Comprehensive XSS vulnerability prevention tests for Issue #411.

    Tests verify that user data from architecture.json is properly escaped
    to prevent XSS attacks in both tooltips and Mermaid diagrams.
    """

    def test_comprehensive_tooltip_xss_prevention(self):
        """
        Comprehensive test: Verify all tooltip fields escape XSS payloads.

        Tests all 6 vulnerable fields (filename, description, tags, dependencies,
        filepath, priority) with various XSS attack vectors.
        """
        arch = [{
            "filename": "test<img src=x onerror=alert('XSS')>.py",
            "description": "Normal text<script>alert('XSS')</script>",
            "tags": ["api", "<img src=x onerror=alert('XSS')>", "backend"],
            "dependencies": ["utils<script>alert(1)</script>"],
            "filepath": "/src/test<svg/onload=alert('XSS')>.py",
            "priority": "<High>",
        }]

        html_doc = generate_html("", arch, "Test App")
        json_str = extract_module_data_json(html_doc)

        # Verify HTML special characters are escaped (as HTML entities or Unicode)
        assert '&lt;img' in json_str or '\\u003c' in json_str, \
            "< character should be escaped"
        assert '&lt;script&gt;' in json_str or '\\u003cscript\\u003e' in json_str, \
            "<script> tags should be escaped"
        assert '&lt;svg' in json_str or '\\u003csvg' in json_str, \
            "<svg tag should be escaped"

        # Verify unescaped XSS payloads are NOT present
        assert '<img src=x onerror=' not in json_str, \
            "Raw XSS payload should not be present"
        assert '<script>alert(' not in json_str, \
            "Unescaped script tags should not be present"

    def test_comprehensive_mermaid_diagram_xss_prevention(self):
        """
        Comprehensive test: Verify all Mermaid diagram locations escape XSS.

        Tests XSS prevention in node definitions, labels, dependencies,
        class assignments, priority field, and app name.
        """
        arch = [
            {
                "filename": "xss1<img src=x onerror=alert(1)>.py",
                "tags": ["frontend"],
                "priority": "high<script>alert('pri')</script>",
                "dependencies": ["xss2<script>alert(2)</script>.py"],
            },
            {
                "filename": "xss2<script>alert(2)</script>.py",
                "tags": ["backend"],
                "priority": 2,
            }
        ]

        mermaid_code = generate_mermaid_code(arch, "XSS<svg onload=alert(3)> Test")

        # Verify NO unescaped XSS payloads in entire Mermaid code
        assert '<img src=x onerror=' not in mermaid_code, "XSS payload 1 should be escaped"
        assert '<script>alert(' not in mermaid_code, "XSS payloads 2 should be escaped"
        assert '<svg onload=' not in mermaid_code, "XSS payload 3 should be escaped"

    def test_regression_priority_values(self):
        """
        Regression test: Numeric, string, and default priority values work correctly.

        Ensures XSS fix doesn't break normal priority field behavior.
        """
        arch = [
            {"filename": "high.py", "priority": 1},
            {"filename": "medium.py", "priority": "medium"},
            {"filename": "default.py"},  # No priority - should default to 0
        ]

        mermaid_code = generate_mermaid_code(arch, "Test App")

        # All priority values should appear correctly
        assert 'high["high (1)"]' in mermaid_code
        assert 'medium["medium (medium)"]' in mermaid_code
        assert 'default["default (0)"]' in mermaid_code

    def test_regression_legitimate_special_characters(self):
        """
        Regression test: Ensure legitimate special characters still work.

        Verifies XSS fix doesn't break quotes, apostrophes, and Unicode.
        """
        arch = [{
            "filename": "user's_file.py",
            "description": 'A "quoted" description with unicode: café',
            "tags": ["it's", "api"],
            "priority": 1,
        }]

        html_doc = generate_html("", arch, "Test App")
        json_str = extract_module_data_json(html_doc)
        data = json.loads(json_str)

        # Data should be preserved correctly
        assert "user's_file" in data or "user\\'s_file" in str(data)
        assert '"quoted"' in data["user's_file"]["description"] or \
               '"quoted"' in str(data["user's_file"]["description"])
        assert data["user's_file"]["priority"] == 1

    def test_edge_case_empty_values(self):
        """
        Edge case test: Empty strings and missing fields handled gracefully.

        Ensures XSS fix works with defaults and empty values.
        """
        arch = [
            {"filename": "minimal.py"},  # Missing optional fields
            {
                "filename": "empty<script>.py",
                "description": "",
                "tags": [],
                "dependencies": [],
                "filepath": "",
            },
        ]

        html_doc = generate_html("", arch, "Test App")
        json_str = extract_module_data_json(html_doc)
        data = json.loads(json_str)

        # Verify defaults are used
        assert data["minimal"]["priority"] == "N/A"
        assert data["minimal"]["description"] == "No description"

        # Verify XSS still escaped with empty fields
        assert '<script>' not in json_str
