"""
Test Plan for agentic_bug_step11_e2e_test_LLM.prompt

This test file verifies that the Step 11 prompt produces cross-endpoint
integration tests when given a multi-endpoint bug scenario. It calls
run_agentic_task (the real agentic CLI) against a fixture repo containing
two endpoints with a leaked-field bug.

Issue: PR #878 — add cross-endpoint integration test type to Step 11 E2E prompt

The bug: When a multi-endpoint bug is reported (e.g., submit_interest writes
waitlist data that get_waitlist_status reads back), the Step 11 prompt listed
"Integration tests" as a type but gave no definition or examples. The LLM fell
back to unit test patterns (hand-crafted dicts, single endpoint) instead of
testing data flow between endpoints.

Test Categories:
1. Unit tests (TestStep11CrossEndpoint*): Verify prompt contains required guidance
2. Integration test (TestStep11AgenticIntegration): Run the real agentic CLI
   against a fixture repo and verify it generates a capture-and-replay test
"""

import os
import re
import subprocess
from pathlib import Path
from typing import Dict

import pytest

from tests.test_agentic_bug_step7_prompt import extract_python_code_blocks


# --- Constants ---

PROMPT_PATH = (
    Path(__file__).parent.parent
    / "pdd"
    / "prompts"
    / "agentic_bug_step11_e2e_test_LLM.prompt"
)


# --- Fixtures ---


@pytest.fixture
def step11_prompt_content() -> str:
    """Load the Step 11 prompt content."""
    assert PROMPT_PATH.exists(), f"Prompt file not found: {PROMPT_PATH}"
    return PROMPT_PATH.read_text()


# --- Fixture Repo: Two-endpoint waitlist app with leaked-field bug ---

SUBMIT_INTEREST_PY = '''\
"""Endpoint: submit_interest — writes waitlist data to Firestore."""
from backend.db import query_collection, set_document


def submit_interest(email: str, plan: str) -> dict:
    """Register user interest. Checks for existing entry, then writes."""
    existing = query_collection("waitlist", [("email", "==", email)])
    if existing:
        # BUG: existing[0] contains a synthetic 'id' field injected by
        # query_collection, and we write it back to Firestore as-is.
        data = existing[0]
        data["plan"] = plan
    else:
        data = {"email": email, "plan": plan, "status": "pending"}

    doc_id = email.replace("@", "_at_").replace(".", "_")
    set_document("waitlist", doc_id, data)
    return {"ok": True, "doc_id": doc_id}
'''

GET_WAITLIST_STATUS_PY = '''\
"""Endpoint: get_waitlist_status — reads waitlist data from Firestore."""
from backend.db import get_document


def get_waitlist_status(email: str) -> dict:
    """Return the waitlist status for a given email."""
    doc_id = email.replace("@", "_at_").replace(".", "_")
    doc = get_document("waitlist", doc_id)
    if doc is None:
        return {"error": "not_found"}
    return doc
'''

DB_PY = '''\
"""Database helpers wrapping Firestore operations."""

_STORE: dict = {}  # In-memory store for testing


def query_collection(collection: str, filters: list) -> list:
    """Query a Firestore collection. Injects synthetic 'id' field."""
    results = []
    for doc_id, doc in _STORE.get(collection, {}).items():
        match = all(doc.get(f[0]) == f[2] for f in filters)
        if match:
            # BUG: inject synthetic 'id' for internal tracking
            result = dict(doc)
            result["id"] = doc_id
            results.append(result)
    return results


def set_document(collection: str, doc_id: str, data: dict) -> None:
    """Write a document to Firestore."""
    if collection not in _STORE:
        _STORE[collection] = {}
    _STORE[collection][doc_id] = dict(data)


def get_document(collection: str, doc_id: str) -> dict | None:
    """Read a document from Firestore."""
    return _STORE.get(collection, {}).get(doc_id)
'''

INIT_PY = ''
CONFTEST_PY = '''\
"""Shared test fixtures for the waitlist app."""
import sys
from pathlib import Path

# Add project root to path so tests can import backend modules
sys.path.insert(0, str(Path(__file__).parent.parent))
'''

UNIT_TEST_SUBMIT_PY = '''\
"""Unit test for submit_interest (generated in Step 9)."""
from unittest.mock import patch


def test_submit_interest_writes_data():
    """Verify submit_interest calls set_document."""
    from backend.endpoints.submit_interest import submit_interest

    with patch("backend.endpoints.submit_interest.set_document") as mock_set:
        with patch("backend.endpoints.submit_interest.query_collection", return_value=[]):
            result = submit_interest("test@example.com", "pro")

    assert result["ok"] is True
    mock_set.assert_called_once()
'''

UNIT_TEST_STATUS_PY = '''\
"""Unit test for get_waitlist_status (generated in Step 9)."""
from unittest.mock import patch


def test_get_waitlist_status_returns_doc():
    """Verify get_waitlist_status returns the document."""
    from backend.endpoints.get_waitlist_status import get_waitlist_status

    mock_doc = {"email": "test@example.com", "plan": "pro", "status": "pending"}
    with patch("backend.endpoints.get_waitlist_status.get_document", return_value=mock_doc):
        result = get_waitlist_status("test@example.com")

    assert result["email"] == "test@example.com"
    assert result["status"] == "pending"
'''


@pytest.fixture
def fixture_repo(tmp_path: Path) -> Path:
    """Create a small git repo with two endpoints that have the leaked-field bug."""
    # Create directory structure
    (tmp_path / "backend").mkdir()
    (tmp_path / "backend" / "__init__.py").write_text(INIT_PY)
    (tmp_path / "backend" / "db.py").write_text(DB_PY)
    (tmp_path / "backend" / "endpoints").mkdir()
    (tmp_path / "backend" / "endpoints" / "__init__.py").write_text(INIT_PY)
    (tmp_path / "backend" / "endpoints" / "submit_interest.py").write_text(SUBMIT_INTEREST_PY)
    (tmp_path / "backend" / "endpoints" / "get_waitlist_status.py").write_text(GET_WAITLIST_STATUS_PY)
    (tmp_path / "tests").mkdir()
    (tmp_path / "tests" / "__init__.py").write_text(INIT_PY)
    (tmp_path / "tests" / "conftest.py").write_text(CONFTEST_PY)
    (tmp_path / "tests" / "test_submit_interest.py").write_text(UNIT_TEST_SUBMIT_PY)
    (tmp_path / "tests" / "test_get_waitlist_status.py").write_text(UNIT_TEST_STATUS_PY)

    # Initialize git repo so the agentic CLI can operate
    subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True, check=True)
    subprocess.run(
        ["git", "config", "user.email", "test@example.com"],
        cwd=tmp_path, capture_output=True, check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Test"],
        cwd=tmp_path, capture_output=True, check=True,
    )
    subprocess.run(["git", "add", "."], cwd=tmp_path, capture_output=True, check=True)
    subprocess.run(
        ["git", "commit", "-m", "Initial commit"],
        cwd=tmp_path, capture_output=True, check=True,
    )

    return tmp_path


# --- Scenario context for Step 11 ---

def make_cross_endpoint_scenario(worktree_path: str) -> Dict[str, str]:
    """Build the context dict that the orchestrator would pass to Step 11."""
    return {
        "issue_url": "https://github.com/example/webapp/issues/594",
        "repo_owner": "example",
        "repo_name": "webapp",
        "issue_number": "594",
        "worktree_path": worktree_path,
        "issue_content": (
            "## Bug Report\n\n"
            "When a user submits interest via the waitlist form and then checks their "
            "status, the status endpoint returns malformed data with an extra `id` field "
            "that breaks the frontend.\n\n"
            "### Steps to Reproduce\n"
            '1. Call submit_interest("test@example.com", "pro")\n'
            '2. Call get_waitlist_status("test@example.com")\n'
            "3. Response contains an unexpected `id` field\n\n"
            "### Root Cause\n"
            "query_collection() injects a synthetic `id` field. submit_interest writes "
            "the raw result (including `id`) back to Firestore. get_waitlist_status "
            "returns it as-is."
        ),
        "step1_output": "Issue is a valid bug report about leaked fields between endpoints.",
        "step2_output": "Confirmed bug: submit_interest and get_waitlist_status have a data flow issue.",
        "step3_output": "Issue has sufficient information to investigate. Two endpoints involved.",
        "step4_output": "No external API dependencies. Uses in-memory store for persistence.",
        "step5_output": (
            "Root cause identified across two endpoints:\n"
            "1. submit_interest (backend/endpoints/submit_interest.py) calls query_collection() "
            "which injects a synthetic `id` field into the returned document.\n"
            "2. submit_interest then calls set_document() to write this data back, including the "
            "leaked `id` field.\n"
            "3. get_waitlist_status (backend/endpoints/get_waitlist_status.py) calls get_document() "
            "and returns the raw document, which now includes the spurious `id` field.\n"
        ),
        "step6_output": (
            "Fix: In submit_interest.py, strip the `id` field from query_collection() results "
            "before writing back via set_document()."
        ),
        "step7_output": (
            "DEFECT_TYPE: code\n"
            "This is a code bug — query_collection's synthetic id leaks through "
            "submit_interest into the data store."
        ),
        "step8_output": (
            "### Test Location\n"
            "**File:** tests/test_submit_interest.py and tests/test_get_waitlist_status.py\n\n"
            "### Test Strategy\n"
            "1. Test submit_interest: mock set_document, call endpoint, verify written data has no `id` field\n"
            "2. Test get_waitlist_status: mock get_document with data containing `id`, verify response excludes it\n"
        ),
        "step9_output": (
            "Generated two unit test files:\n"
            "- tests/test_submit_interest.py — mocks set_document, verifies no `id` in written data\n"
            "- tests/test_get_waitlist_status.py — mocks get_document, verifies response excludes `id`\n\n"
            "Both tests pass in isolation with hand-crafted mock data.\n\n"
            "FILES_CREATED: tests/test_submit_interest.py, tests/test_get_waitlist_status.py"
        ),
        "step10_output": (
            "Unit tests verified:\n"
            "- test_submit_interest correctly catches the leaked `id` field on write\n"
            "- test_get_waitlist_status correctly verifies `id` is excluded from response\n"
            "However, neither test verifies the data flow between the two endpoints."
        ),
        "files_to_stage": "tests/test_submit_interest.py, tests/test_get_waitlist_status.py",
    }


# --- Unit Tests ---


class TestStep11CrossEndpointGuidance:
    """
    Test that the Step 11 prompt contains cross-endpoint integration test guidance.

    When a bug involves data written by one endpoint and read by another,
    the prompt should instruct the LLM to use a capture-and-replay pattern
    rather than testing each endpoint in isolation with hand-crafted data.
    """

    def test_prompt_contains_cross_endpoint_section(
        self, step11_prompt_content: str
    ) -> None:
        """
        Verify the prompt has a dedicated cross-endpoint integration test section.

        Without this section, the LLM falls back to the generic "Integration tests"
        bullet which has no actionable guidance.
        """
        assert "Cross-endpoint integration tests" in step11_prompt_content, (
            "Step 11 prompt should contain a 'Cross-endpoint integration tests' section "
            "with guidance for testing data flow between endpoints."
        )

    def test_prompt_contains_capture_and_replay_pattern(
        self, step11_prompt_content: str
    ) -> None:
        """
        Verify the prompt includes the capture-and-replay code example.

        The key pattern: mock endpoint A's write to capture data, then feed
        that exact data into endpoint B's read mock.
        """
        assert "capture_write" in step11_prompt_content, (
            "Step 11 prompt should contain a capture_write example showing how to "
            "capture data written by endpoint A."
        )
        assert "captured['data']" in step11_prompt_content, (
            "Step 11 prompt should show feeding captured data into endpoint B."
        )

    def test_prompt_warns_against_handcrafted_data(
        self, step11_prompt_content: str
    ) -> None:
        """
        Verify the prompt explicitly warns against hand-crafting intermediate data.

        The whole point of capture-and-replay is that the intermediate data is
        whatever endpoint A actually produces — hand-crafting it defeats the purpose
        and misses bugs like leaked fields.
        """
        assert "Do NOT hand-craft the intermediate data dict" in step11_prompt_content, (
            "Step 11 prompt should warn: 'Do NOT hand-craft the intermediate data dict' "
            "to prevent the LLM from bypassing the capture-and-replay pattern."
        )

    def test_prompt_explains_what_pattern_catches(
        self, step11_prompt_content: str
    ) -> None:
        """
        Verify the prompt explains what bugs the capture-and-replay pattern catches.

        This helps the LLM understand WHY the pattern matters, making it more likely
        to use it correctly.
        """
        assert "serialization mismatches" in step11_prompt_content, (
            "Prompt should list 'serialization mismatches' as a bug type caught by "
            "capture-and-replay testing."
        )
        assert "leaked internal fields" in step11_prompt_content, (
            "Prompt should list 'leaked internal fields' as a bug type caught by "
            "capture-and-replay testing."
        )


# --- Analysis Helper ---


def analyze_test_code_for_cross_endpoint_patterns(code: str) -> dict:
    """
    Analyze generated test code for cross-endpoint integration test patterns.

    Returns a dict with boolean flags. Accepts TWO valid approaches:

    1. Mock capture-and-replay: mock endpoint A's write to capture data,
       feed captured data into endpoint B's read mock.
    2. True integration: call both endpoints directly (no mocking the buggy
       components), letting real data flow through and asserting on the result.

    The anti-pattern is testing each endpoint in ISOLATION with hand-crafted
    mock data — that's what missed the leaked `id` field in issue #594.
    """
    code_lower = code.lower()

    # --- Detect mock-based capture-and-replay ---
    uses_mock_capture = any([
        "captured" in code_lower and "side_effect" in code_lower,
        "capture_write" in code_lower,
        "captured_data" in code_lower,
        "captured[" in code and "side_effect" in code_lower,
        re.search(r'def\s+\w*capture\w*.*?side_effect', code_lower, re.DOTALL) is not None,
        re.search(r'side_effect.*?captured', code_lower, re.DOTALL) is not None,
    ])

    feeds_captured_to_endpoint_b = any([
        re.search(r'captured.*?(return_value|side_effect)', code_lower, re.DOTALL) is not None,
        re.search(r'(return_value|side_effect).*?captured', code_lower, re.DOTALL) is not None,
    ])

    # --- Detect true integration (no mocking, direct endpoint calls) ---
    # The agent may call both endpoints directly and let real data flow through.
    # This is valid as long as BOTH endpoints are called in the SAME test function
    # and the test asserts on the output of endpoint B.
    calls_both_endpoints = (
        "submit_interest" in code_lower and "get_waitlist_status" in code_lower
    )
    uses_real_data_flow = calls_both_endpoints and any([
        # Both endpoints called without mocking the buggy components
        "submit_interest(" in code and "get_waitlist_status(" in code,
        "endpoint_a(" in code_lower and "endpoint_b(" in code_lower,
    ])
    # True integration: calls both endpoints AND does NOT mock the data layer
    # between them (no patch on set_document/get_document/query_collection
    # that would isolate the endpoints)
    mocks_data_layer = any([
        "set_document" in code_lower and "patch" in code_lower,
        "get_document" in code_lower and "patch" in code_lower,
        "query_collection" in code_lower and "patch" in code_lower,
    ])
    is_true_integration = uses_real_data_flow and not mocks_data_layer

    # --- Combined: cross-endpoint data flow tested ---
    tests_cross_endpoint_flow = (
        uses_mock_capture or is_true_integration
    )

    # --- Detect testing both endpoints (any approach) ---
    tests_both_endpoints = any([
        calls_both_endpoints,
        "endpoint_a" in code_lower and "endpoint_b" in code_lower,
        code_lower.count("with patch") >= 2 or code_lower.count("@patch") >= 2,
    ])

    # --- Anti-pattern: hand-crafted dict in isolated single-endpoint tests ---
    has_handcrafted_dict = bool(
        re.search(r'return_value\s*=\s*\{["\']', code)
        or re.search(r'side_effect\s*=\s*\[\s*None\s*,\s*\{["\']', code)
    )
    anti_pattern_handcrafted_data = (
        has_handcrafted_dict and not uses_mock_capture and not is_true_integration
    )

    # --- Basic mock usage ---
    uses_mock = any([
        "from unittest.mock import" in code,
        "from unittest import mock" in code,
        "import mock" in code,
        "@patch" in code,
        "with patch" in code_lower,
        "mock." in code_lower,
    ])

    return {
        "uses_capture_pattern": uses_mock_capture,
        "feeds_captured_to_endpoint_b": feeds_captured_to_endpoint_b,
        "is_true_integration": is_true_integration,
        "tests_cross_endpoint_flow": tests_cross_endpoint_flow,
        "anti_pattern_handcrafted_data": anti_pattern_handcrafted_data,
        "tests_both_endpoints": tests_both_endpoints,
        "uses_mock": uses_mock,
    }


# --- Analysis Helper Unit Tests ---


class TestAnalyzeCrossEndpointPatterns:
    """Unit tests for analyze_test_code_for_cross_endpoint_patterns."""

    def test_detects_capture_and_replay_pattern(self) -> None:
        """Verify detection of the mock-based capture-and-replay pattern."""
        code = """
from unittest.mock import patch

def test_cross_endpoint():
    captured = {}
    def capture_write(collection, doc_id, data):
        captured['data'] = data
    with patch('module_a.set_document', side_effect=capture_write):
        response_a, status_a = submit_interest(request, user, token)
    assert status_a == 200

    with patch('module_b.get_document', return_value=captured['data']):
        response_b, status_b = get_waitlist_status(request, user, token)
    assert status_b == 200
"""
        analysis = analyze_test_code_for_cross_endpoint_patterns(code)
        assert analysis["uses_capture_pattern"]
        assert analysis["feeds_captured_to_endpoint_b"]
        assert analysis["tests_cross_endpoint_flow"]
        assert not analysis["anti_pattern_handcrafted_data"]
        assert analysis["tests_both_endpoints"]
        assert analysis["uses_mock"]

    def test_detects_true_integration_pattern(self) -> None:
        """Verify detection of true integration (no mocking, direct calls)."""
        code = """
from backend.endpoints.submit_interest import submit_interest
from backend.endpoints.get_waitlist_status import get_waitlist_status

def test_submit_then_read_no_leaked_id():
    submit_interest("test@example.com", "pro")
    submit_interest("test@example.com", "enterprise")
    result = get_waitlist_status("test@example.com")
    assert "id" not in result
"""
        analysis = analyze_test_code_for_cross_endpoint_patterns(code)
        assert analysis["is_true_integration"]
        assert analysis["tests_cross_endpoint_flow"]
        assert analysis["tests_both_endpoints"]
        assert not analysis["anti_pattern_handcrafted_data"]
        assert not analysis["uses_capture_pattern"]  # No mock capture needed

    def test_detects_handcrafted_anti_pattern(self) -> None:
        """Verify detection of the hand-crafted data anti-pattern."""
        code = """
from unittest.mock import patch

def test_submit_interest_only():
    with patch('module.set_document') as mock_set:
        submit_interest(request, user, token)
        mock_set.assert_called_once()

def test_get_waitlist_status_only():
    with patch('module.get_document', return_value={"email": "test@example.com", "status": "pending"}):
        response, status = get_waitlist_status(request, user, token)
    assert status == 200
"""
        analysis = analyze_test_code_for_cross_endpoint_patterns(code)
        assert not analysis["uses_capture_pattern"]
        assert not analysis["is_true_integration"]
        assert not analysis["tests_cross_endpoint_flow"]
        assert analysis["anti_pattern_handcrafted_data"]

    def test_no_false_positive_on_capture_with_dict(self) -> None:
        """Ensure capture pattern with dict literal isn't flagged as anti-pattern."""
        code = """
from unittest.mock import patch

def test_cross_endpoint():
    captured = {}
    def capture_write(collection, doc_id, data):
        captured['data'] = data
    with patch('module_a.set_document', side_effect=capture_write):
        submit_interest(request, user, token)
    with patch('module_b.get_document', return_value=captured['data']):
        get_waitlist_status(request, user, token)
"""
        analysis = analyze_test_code_for_cross_endpoint_patterns(code)
        assert not analysis["anti_pattern_handcrafted_data"]


# --- Integration Test: Real Agentic CLI ---


def _format_step11_prompt(prompt_template: str, context: Dict[str, str]) -> str:
    """
    Format the Step 11 prompt the same way the orchestrator does.

    Replicates the orchestrator's 3-step process:
    1. Preprocess (expand includes, escape braces except context keys)
    2. Un-double template braces
    3. Substitute context variables via str.replace()
    """
    from pdd.preprocess import preprocess

    exclude_keys = list(context.keys())
    processed = preprocess(
        prompt_template,
        recursive=True,
        double_curly_brackets=True,
        exclude_keys=exclude_keys,
    )

    processed = processed.replace("{{", "{").replace("}}", "}")
    formatted = processed
    for key, value in context.items():
        formatted = formatted.replace(f"{{{key}}}", str(value))

    return formatted


class TestStep11AgenticIntegration:
    """
    Integration test that runs the real agentic CLI against a fixture repo.

    Creates a small repo with two endpoints that have the leaked-field bug,
    formats the Step 11 prompt with realistic context, calls run_agentic_task,
    and verifies the agent generates a capture-and-replay integration test.

    Skip criteria: No agentic CLI available (claude or gemini)
    """

    @pytest.mark.integration
    def test_agentic_cli_generates_cross_endpoint_test(
        self, step11_prompt_content: str, fixture_repo: Path, monkeypatch
    ) -> None:
        """
        Run the agentic CLI with the Step 11 prompt against a fixture repo
        containing two endpoints with a leaked-field bug.

        Uses Haiku for speed and cost in the regression suite.

        Verify:
        1. The agent creates a test file (E2E_FILES_CREATED marker in output)
        2. The generated test uses the capture-and-replay pattern
        3. The generated test references both endpoints
        4. The generated test does NOT use hand-crafted mock data
        """
        # This test calls run_agentic_task which shells out to an agentic CLI
        # (claude/gemini/codex). PDD_RUN_REAL_LLM_TESTS is insufficient because
        # the cloud batch image sets it for Vertex API tests but doesn't have
        # agentic CLI auth. Require PDD_RUN_AGENTIC_TESTS explicitly.
        if not os.environ.get("PDD_RUN_AGENTIC_TESTS"):
            pytest.skip(
                "Agentic CLI integration test; set PDD_RUN_AGENTIC_TESTS=1 "
                "(requires authenticated claude/gemini/codex CLI)."
            )

        from pdd.agentic_common import get_available_agents, run_agentic_task

        available = get_available_agents()
        if not available:
            pytest.skip("No agentic CLI available (claude/gemini/codex)")

        # Use Haiku for speed/cost in regression suite (unless already overridden)
        if not os.environ.get("CLAUDE_MODEL"):
            monkeypatch.setenv("CLAUDE_MODEL", "claude-haiku-4-5")

        # Format prompt exactly like the orchestrator does
        context = make_cross_endpoint_scenario(str(fixture_repo))
        formatted_prompt = _format_step11_prompt(step11_prompt_content, context)

        # Run the agentic CLI
        success, output, cost, provider = run_agentic_task(
            instruction=formatted_prompt,
            cwd=fixture_repo,
            verbose=True,
            quiet=False,
            label="step11",
            timeout=240.0,
        )

        assert success, (
            f"run_agentic_task failed (provider={provider}).\n"
            f"Output:\n{output[:1000]}"
        )

        # --- Verify output markers ---

        # The agent should produce E2E_FILES_CREATED (or E2E_SKIP)
        has_files_created = "E2E_FILES_CREATED:" in output
        has_skip = "E2E_SKIP:" in output
        has_fail = "E2E_FAIL:" in output

        assert not has_fail, (
            f"Agent reported E2E_FAIL — test did not catch the bug.\n"
            f"Output:\n{output[:1000]}"
        )

        # --- Collect generated test code ---
        # Strategy: read all .py files the agent created/modified in tests/
        # that weren't part of the original fixture
        original_test_files = {
            "tests/test_submit_interest.py",
            "tests/test_get_waitlist_status.py",
            "tests/conftest.py",
            "tests/__init__.py",
        }

        generated_code_parts = []

        # 1. Parse E2E_FILES_CREATED paths from output
        for line in output.splitlines():
            if line.strip().startswith("E2E_FILES_CREATED:"):
                paths_str = line.split(":", 1)[1].strip()
                for p in paths_str.split(","):
                    p = p.strip()
                    full_path = fixture_repo / p
                    if full_path.exists():
                        generated_code_parts.append(full_path.read_text())

        # 2. Find any new .py files in tests/ that weren't in the original set
        for py_file in fixture_repo.rglob("tests/**/*.py"):
            rel = str(py_file.relative_to(fixture_repo))
            if rel not in original_test_files:
                content = py_file.read_text()
                if content not in generated_code_parts:
                    generated_code_parts.append(content)

        # 3. Also extract code blocks from the output text (agent may have
        #    printed the code in its response)
        code_blocks = extract_python_code_blocks(output)
        generated_code_parts.extend(code_blocks)

        all_generated_code = "\n".join(generated_code_parts)

        assert all_generated_code.strip(), (
            "No generated test code found — neither in files nor in output.\n"
            f"E2E_FILES_CREATED present: {has_files_created}\n"
            f"E2E_SKIP present: {has_skip}\n"
            f"Output:\n{output[:1000]}"
        )

        # --- Analyze the generated test code ---
        analysis = analyze_test_code_for_cross_endpoint_patterns(all_generated_code)

        assert analysis["tests_both_endpoints"], (
            "Generated test should reference both submit_interest and "
            "get_waitlist_status (or two distinct endpoints).\n"
            f"Generated code:\n{all_generated_code[:1000]}"
        )

        assert analysis["tests_cross_endpoint_flow"], (
            "Generated test should verify cross-endpoint data flow — either via "
            "mock capture-and-replay or true integration (calling both endpoints "
            "and asserting on endpoint B's output). Instead it appears to test "
            "each endpoint in isolation.\n"
            f"  uses_capture_pattern: {analysis['uses_capture_pattern']}\n"
            f"  is_true_integration: {analysis['is_true_integration']}\n"
            f"Generated code:\n{all_generated_code[:1000]}"
        )

        assert not analysis["anti_pattern_handcrafted_data"], (
            "Generated test uses ANTI-PATTERN: hand-crafted dict as mock "
            "return value without capturing real endpoint output. This "
            "misses bugs like leaked fields.\n"
            f"Generated code:\n{all_generated_code[:1000]}"
        )
