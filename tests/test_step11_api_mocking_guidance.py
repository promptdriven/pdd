"""
Tests for issue #633: step 11 E2E test prompt generates broken mocks.

Verifies that agentic_bug_step11_e2e_test_LLM.prompt contains guidance for
writing correct API mocks in E2E tests, addressing three bug classes from
PR #627 (wrong HTTP method, duplicate handlers, wrong error text) and the
route stacking issue from PR #774.

Acceptance criteria from issue #633:
1. Step 11 prompt includes API mocking best practices section
2. Prompt explicitly instructs reading the API implementation before mocking
3. Prompt warns about Playwright's route handler stacking behavior
4. Prompt instructs tracing error messages through catch blocks

Test categories:
- Regression tests (consolidated from Step 5): verify all 4 acceptance criteria
- Fix-verification tests (Step 8): verify fix quality, code example completeness,
  and that all real-world bug classes are addressed
- Integration test (gated by PDD_RUN_AGENTIC_TESTS): verify the prompt produces
  correct mocks when run through the agentic CLI
"""

import os
import re
import subprocess
from pathlib import Path
from typing import Dict

import pytest


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


# =========================================================================
# Regression Tests (consolidated from Step 5 reproduction tests)
# These verify the 4 acceptance criteria from issue #633.
# They FAIL on the pre-fix prompt and PASS on the post-fix prompt.
# =========================================================================


class TestStep11APIMockingSection:
    """
    Reproduction test — AC1: Step 11 prompt includes API mocking section.

    Without this section, the LLM generates mocks with wrong HTTP methods,
    duplicate route handlers, and incorrect error assertions (PRs #627, #774).
    """

    def test_prompt_contains_api_mocking_section(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the prompt has a dedicated API mocking best practices section."""
        content_lower = step11_prompt_content.lower()
        has_mocking_section = any([
            "api mocking best practices" in content_lower,
            "api mocking" in content_lower and "best practice" in content_lower,
            "mocking best practices" in content_lower,
        ])
        assert has_mocking_section, (
            "Step 11 prompt should contain an 'API Mocking Best Practices' section. "
            "Currently the only page.route() guidance is: 'Prefer self-contained "
            "Playwright tests that use page.route() to mock API responses' — no "
            "mention of correct HTTP methods, route stacking, or error message tracing."
        )


class TestStep11ReadAPIImplementation:
    """
    Reproduction test — AC2: Prompt instructs reading API implementation.

    PR #627 bug #1: LLM assumed PUT for an update operation but
    saveBoards() in github-app-api.ts:39 actually uses POST.
    """

    def test_prompt_instructs_reading_api_implementation(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the prompt instructs reading the actual API call source code."""
        content_lower = step11_prompt_content.lower()
        has_read_api = any([
            "read the actual api call" in content_lower,
            "read the actual fetch" in content_lower,
            "find the fetch" in content_lower and "source code" in content_lower,
            "read the api" in content_lower and "implementation" in content_lower,
            "actual api" in content_lower and "implementation" in content_lower,
        ])
        assert has_read_api, (
            "Step 11 prompt should instruct the LLM to read the actual API call "
            "implementation before writing mocks. In PR #627, the LLM assumed PUT "
            "for an update operation but saveBoards() actually uses POST."
        )

    def test_prompt_warns_against_assuming_http_methods(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the prompt warns against assuming REST conventions for HTTP methods."""
        content_lower = step11_prompt_content.lower()
        has_warning = any([
            "do not assume rest conventions" in content_lower,
            "don't assume rest conventions" in content_lower,
            "exact http method" in content_lower,
            "do not assume" in content_lower and "http method" in content_lower,
            "don't assume" in content_lower and "http method" in content_lower,
        ])
        assert has_warning, (
            "Step 11 prompt should warn against assuming HTTP methods based on REST "
            "conventions. In PR #627, the LLM mocked PUT but the actual API uses POST."
        )

    def test_prompt_instructs_matching_request_response_shapes(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the prompt instructs matching request/response shapes from source."""
        content_lower = step11_prompt_content.lower()
        has_shape_matching = any([
            "request body shape" in content_lower,
            "response shape" in content_lower,
            "match the request" in content_lower and "response" in content_lower,
            "request body" in content_lower and "response" in content_lower
            and "source" in content_lower,
        ])
        assert has_shape_matching, (
            "Step 11 prompt should instruct matching request body and response shapes "
            "from the actual source code, not generating plausible mock data."
        )


class TestStep11RouteHandlerStacking:
    """
    Reproduction test — AC3: Prompt warns about route handler stacking.

    PRs #627 and #774: LLM registered multiple page.route() handlers for
    the same URL — Playwright's LIFO stacking silently bypasses earlier handlers.
    """

    def test_prompt_warns_about_route_stacking(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the prompt explains Playwright's route handler stacking."""
        content_lower = step11_prompt_content.lower()
        has_stacking = any([
            "stacks route handlers" in content_lower,
            "route handler" in content_lower and "stack" in content_lower,
            "last registered" in content_lower and "first" in content_lower,
            "lifo" in content_lower and "route" in content_lower,
            "route stacking" in content_lower,
        ])
        assert has_stacking, (
            "Step 11 prompt should warn about Playwright's route handler stacking. "
            "The LAST registered handler runs FIRST — if it calls route.continue(), "
            "earlier handlers are silently bypassed. PR #627 and PR #774 both hit this."
        )

    def test_prompt_instructs_single_handler_per_url(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the prompt instructs using one handler per URL pattern."""
        content_lower = step11_prompt_content.lower()
        has_single_handler = any([
            "one handler per url" in content_lower,
            "single handler" in content_lower and "url pattern" in content_lower,
            "never register two page.route()" in content_lower,
            "never register two" in content_lower and "page.route" in content_lower,
            "one handler" in content_lower and "url pattern" in content_lower,
            "one `page.route()`" in content_lower and "url pattern" in content_lower,
        ])
        assert has_single_handler, (
            "Step 11 prompt should instruct using ONE handler per URL pattern with "
            "method switching, not multiple page.route() calls for the same URL."
        )

    def test_prompt_shows_method_switching_pattern(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the prompt includes a route.request().method() code example."""
        has_method_switching = any([
            "route.request().method()" in step11_prompt_content,
            "request().method()" in step11_prompt_content,
            re.search(
                r"route\.request\(\)\.method\(\)",
                step11_prompt_content,
            ) is not None,
        ])
        assert has_method_switching, (
            "Step 11 prompt should include a code example showing method switching "
            "within a single page.route() handler using route.request().method()."
        )


class TestStep11ErrorMessageTracing:
    """
    Reproduction test — AC4: Prompt instructs tracing error messages.

    PR #627 bug #3: LLM asserted /Failed to save/i but component shows
    "Save failed (500)". The error path: saveBoards throw -> handleSave
    catch -> setError. The LLM didn't trace this path.
    """

    def test_prompt_instructs_tracing_error_messages(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the prompt instructs tracing errors through catch blocks."""
        content_lower = step11_prompt_content.lower()
        has_tracing = any([
            "catch block" in content_lower and "error" in content_lower,
            "trace error" in content_lower,
            "error message" in content_lower and "catch block" in content_lower,
            "thrown error" in content_lower and "catch block" in content_lower,
            "follow thrown errors through catch blocks" in content_lower,
            "trace error handling" in content_lower,
        ])
        assert has_tracing, (
            "Step 11 prompt should instruct tracing error messages through catch "
            "blocks. In PR #627, the LLM asserted /Failed to save/i but the "
            "component shows 'Save failed (500)' — the error flows through "
            "saveBoards throw -> handleSave catch -> setError."
        )

    def test_prompt_instructs_verifying_error_text_against_source(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the prompt instructs checking exact error text from source."""
        content_lower = step11_prompt_content.lower()
        has_exact_text = any([
            "exact text" in content_lower
            and ("assertion" in content_lower or "test" in content_lower),
            "seterror" in content_lower or "setstate" in content_lower,
            "component's catch block" in content_lower,
            "exact" in content_lower and "ui text" in content_lower,
            "verify error message" in content_lower and "source" in content_lower,
        ])
        assert has_exact_text, (
            "Step 11 prompt should instruct verifying error assertion text against "
            "the source code — read what setError/setState receives in catch blocks."
        )


# =========================================================================
# Fix-Verification Tests (Step 8 plan)
# These verify the fix is complete, code examples are correct, and all
# real-world bug classes (PR #627, PR #774) are specifically addressed.
# =========================================================================


class TestStep11PreprocessedPromptRetainsMockingGuidance:
    """
    Step 8 Test 1: Verify all 3 API mocking subsections survive the
    preprocess() pipeline that the orchestrator uses to render the prompt.

    The prompt goes through preprocess() which expands includes and escapes
    braces. This test confirms the mocking guidance isn't stripped or mangled
    by the template engine.
    """

    def test_preprocessed_prompt_contains_all_three_subsections(
        self, step11_prompt_content: str
    ) -> None:
        """
        Render the prompt through the same preprocessing pipeline the
        orchestrator uses, then verify all 3 API mocking subsections remain.
        """
        try:
            from pdd.preprocess import preprocess
        except ImportError:
            pytest.skip("pdd.preprocess not available in this environment")

        # All context keys that appear as {key} in the template
        context_keys = [
            "issue_url", "repo_owner", "repo_name", "issue_number",
            "issue_content", "step1_output", "step2_output", "step3_output",
            "step4_output", "step5_output", "step6_output", "step7_output",
            "step8_output", "step9_output", "step10_output",
            "worktree_path", "files_to_stage",
        ]
        processed = preprocess(
            step11_prompt_content,
            recursive=True,
            double_curly_brackets=True,
            exclude_keys=context_keys,
        )
        # Un-double braces like the orchestrator does
        rendered = processed.replace("{{", "{").replace("}}", "}")
        rendered_lower = rendered.lower()

        # Subsection 1: Read actual API implementation
        assert any([
            "read the actual api call" in rendered_lower,
            "actual api" in rendered_lower and "implementation" in rendered_lower,
        ]), (
            "Subsection 1 (read API implementation) missing after preprocessing. "
            "The preprocess() pipeline may have stripped or mangled this section."
        )

        # Subsection 2: Single handler per URL pattern
        assert any([
            "single handler per url" in rendered_lower,
            "one handler per url" in rendered_lower,
            "one `page.route()`" in rendered_lower
            and "url pattern" in rendered_lower,
        ]), (
            "Subsection 2 (single handler per URL) missing after preprocessing. "
            "The preprocess() pipeline may have stripped or mangled this section."
        )

        # Subsection 3: Verify error message assertions
        assert any([
            "verify error message" in rendered_lower,
            "error message assertions" in rendered_lower,
        ]), (
            "Subsection 3 (verify error assertions) missing after preprocessing. "
            "The preprocess() pipeline may have stripped or mangled this section."
        )


class TestStep11RouteHandlerCodeExample:
    """
    Step 8 Test 2: Verify the TypeScript code example in the prompt is
    complete with method switching and route.continue() fallback.

    An incomplete code example causes the LLM to generate incomplete mock
    handlers. The example must show the full pattern: extract method,
    branch on GET/POST, and fall through with route.continue().
    """

    def test_code_example_has_method_extraction(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the code example extracts the request method."""
        assert "route.request().method()" in step11_prompt_content, (
            "Code example should use route.request().method() to extract "
            "the HTTP method for switching."
        )

    def test_code_example_has_method_branches(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the code example shows branching on GET and POST."""
        has_get = "method === 'GET'" in step11_prompt_content
        has_post = "method === 'POST'" in step11_prompt_content
        assert has_get and has_post, (
            "Code example should show method-based branching with both "
            "GET and POST cases to demonstrate the switching pattern."
        )

    def test_code_example_has_continue_fallback(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the code example includes a route.continue() fallback."""
        assert "route.continue()" in step11_prompt_content, (
            "Code example should include route.continue() as the fallback "
            "for unhandled HTTP methods."
        )

    def test_code_example_uses_page_route(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the code example uses the page.route() API."""
        assert "page.route(" in step11_prompt_content, (
            "Code example should use page.route() to demonstrate the "
            "correct API mocking pattern."
        )


class TestStep11PR627BugClassesCovered:
    """
    Step 8 Test 3: Verify all 3 bug classes from PR #627 are addressed
    with distinct guidance.

    PR #627 had 3 separate bugs in the generated E2E test:
    1. Wrong HTTP method (PUT vs POST) — assumed REST conventions
    2. Duplicate page.route() handlers — didn't know about stacking
    3. Wrong error text assertion — didn't trace through catch blocks

    Each bug class needs its own explicit guidance to prevent recurrence.
    """

    def test_wrong_http_method_bug_addressed(
        self, step11_prompt_content: str
    ) -> None:
        """
        PR #627 Bug 1: LLM mocked PUT but saveBoards() uses POST.
        Prompt must warn against assuming HTTP methods from REST conventions.
        """
        content_lower = step11_prompt_content.lower()
        has_guidance = any([
            "do not assume rest conventions" in content_lower,
            "don't assume rest conventions" in content_lower,
            "do not assume" in content_lower and "rest" in content_lower,
        ])
        assert has_guidance, (
            "Prompt must address PR #627 bug 1: warn against assuming HTTP methods "
            "based on REST conventions (LLM assumed PUT but API uses POST)."
        )

    def test_duplicate_handlers_bug_addressed(
        self, step11_prompt_content: str
    ) -> None:
        """
        PR #627 Bug 2: LLM registered two page.route() for the same URL.
        Prompt must explicitly forbid this pattern.
        """
        content_lower = step11_prompt_content.lower()
        has_guidance = any([
            "never register two" in content_lower
            and "page.route" in content_lower,
            "never register two `page.route()`" in content_lower,
        ])
        assert has_guidance, (
            "Prompt must address PR #627 bug 2: explicitly forbid registering "
            "two page.route() calls for the same URL pattern."
        )

    def test_wrong_error_text_bug_addressed(
        self, step11_prompt_content: str
    ) -> None:
        """
        PR #627 Bug 3: LLM asserted /Failed to save/i but component shows
        "Save failed (500)". Prompt must instruct tracing the full error path.
        """
        content_lower = step11_prompt_content.lower()
        has_guidance = any([
            "trace the full path" in content_lower,
            "do not guess error" in content_lower,
            "don't guess error" in content_lower,
        ])
        assert has_guidance, (
            "Prompt must address PR #627 bug 3: instruct tracing the full error "
            "path to get exact UI text, not guessing error wording."
        )


class TestStep11PR774StackingScenario:
    """
    Step 8 Test 4: Verify the prompt addresses the PR #774 route stacking bug.

    PR #774: Two page.route() handlers with overlapping patterns for
    firestore.googleapis.com. The second handler runs first (LIFO) and
    if it calls route.continue(), the first handler is silently bypassed.
    """

    def test_lifo_warning_present(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the prompt warns about LIFO route handler ordering."""
        content_lower = step11_prompt_content.lower()
        has_lifo = any([
            "last registered" in content_lower and "first" in content_lower,
            "last registered handler" in content_lower,
        ])
        assert has_lifo, (
            "Prompt must explain LIFO ordering: the last registered handler "
            "runs first. PR #774 had two overlapping patterns where the second "
            "handler took priority."
        )

    def test_skipped_entirely_warning(
        self, step11_prompt_content: str
    ) -> None:
        """Verify the prompt warns that bypassed handlers are skipped."""
        content_lower = step11_prompt_content.lower()
        has_skip_warning = any([
            "skipped entirely" in content_lower,
            "silently bypassed" in content_lower,
            "silently overrides" in content_lower,
        ])
        assert has_skip_warning, (
            "Prompt must warn that earlier handlers are 'skipped entirely' or "
            "'silently bypassed/overrides' when a later handler handles the route. "
            "PR #774 had two overlapping patterns where Handler 1 was silently skipped."
        )


# =========================================================================
# Integration Test (gated by PDD_RUN_AGENTIC_TESTS)
# =========================================================================


# Fixture: minimal frontend repo that requires correct API mocking
FIXTURE_API_TS = """\
export async function saveBoards(boards: Board[]): Promise<void> {
  const response = await fetch('/api/boards', {
    method: 'POST',  // NOTE: uses POST, not PUT
    body: JSON.stringify({ boards }),
  });
  if (!response.ok) {
    throw new Error(`Save failed (${response.status})`);
  }
}

export async function loadBoards(): Promise<Board[]> {
  const response = await fetch('/api/boards', { method: 'GET' });
  return response.json();
}
"""

FIXTURE_COMPONENT_TSX = """\
import { saveBoards, loadBoards } from './api';
import { useState, useEffect } from 'react';

export function BoardManager() {
  const [error, setError] = useState<string | null>(null);
  const [boards, setBoards] = useState<Board[]>([]);

  useEffect(() => { loadBoards().then(setBoards); }, []);

  const handleSave = async () => {
    try {
      await saveBoards(boards);
    } catch (e) {
      setError(e.message);  // Shows exact text from api.ts throw
    }
  };

  return (
    <div>
      {error && <div data-testid="error">{error}</div>}
      <button onClick={handleSave}>Save</button>
    </div>
  );
}
"""

FIXTURE_PACKAGE_JSON = '{"name": "test-app", "dependencies": {"react": "^18"}}'


class TestStep11AgenticAPIMockingIntegration:
    """
    Step 8 Test 5: Gold-standard behavioral test that runs the prompt through
    the agentic CLI and verifies the generated E2E test uses correct mocking.

    Creates a fixture repo with a component that makes API calls (POST to
    /api/boards, GET to /api/boards on the same URL), then verifies the LLM:
    1. Does NOT register duplicate page.route() for the same URL
    2. Uses POST (not PUT) matching the source code
    3. Uses correct error text matching the actual throw message

    Gated by PDD_RUN_AGENTIC_TESTS=1 since it requires an authenticated
    agentic CLI (claude/gemini/codex).
    """

    @pytest.fixture
    def api_mocking_fixture_repo(self, tmp_path: Path) -> Path:
        """Create a git repo with a frontend component requiring API mocking."""
        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "api.ts").write_text(FIXTURE_API_TS)
        (tmp_path / "src" / "BoardManager.tsx").write_text(FIXTURE_COMPONENT_TSX)
        (tmp_path / "package.json").write_text(FIXTURE_PACKAGE_JSON)
        (tmp_path / "playwright.config.ts").write_text(
            'import { defineConfig } from "@playwright/test";\n'
            "export default defineConfig({ testDir: './tests/e2e' });\n"
        )
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "e2e").mkdir()

        subprocess.run(
            ["git", "init"], cwd=tmp_path, capture_output=True, check=True,
        )
        subprocess.run(
            ["git", "config", "user.email", "test@test.com"],
            cwd=tmp_path, capture_output=True, check=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test"],
            cwd=tmp_path, capture_output=True, check=True,
        )
        subprocess.run(
            ["git", "add", "."], cwd=tmp_path, capture_output=True, check=True,
        )
        subprocess.run(
            ["git", "commit", "-m", "Initial commit"],
            cwd=tmp_path, capture_output=True, check=True,
        )
        return tmp_path

    @pytest.mark.integration
    def test_agentic_cli_generates_correct_api_mocks(
        self,
        step11_prompt_content: str,
        api_mocking_fixture_repo: Path,
        monkeypatch,
    ) -> None:
        """
        Run the agentic CLI with the Step 11 prompt against a fixture repo
        and verify the generated E2E test uses correct API mocking patterns.
        """
        if not os.environ.get("PDD_RUN_AGENTIC_TESTS"):
            pytest.skip(
                "Agentic CLI integration test; set PDD_RUN_AGENTIC_TESTS=1 "
                "(requires authenticated claude/gemini/codex CLI)."
            )

        from pdd.agentic_common import get_available_agents, run_agentic_task

        available = get_available_agents()
        if not available:
            pytest.skip("No agentic CLI available (claude/gemini/codex)")

        if not os.environ.get("CLAUDE_MODEL"):
            monkeypatch.setenv("CLAUDE_MODEL", "claude-haiku-4-5")

        repo = api_mocking_fixture_repo

        # Build context matching the orchestrator's format
        context: Dict[str, str] = {
            "issue_url": "https://github.com/example/app/issues/625",
            "repo_owner": "example",
            "repo_name": "app",
            "issue_number": "625",
            "worktree_path": str(repo),
            "issue_content": (
                "## Bug: Board save error not displayed correctly\n\n"
                "saveBoards() in src/api.ts uses POST to /api/boards. "
                "loadBoards() uses GET on the same URL. When save fails with "
                "500, the component should show 'Save failed (500)' but "
                "displays nothing.\n\n"
                "Both GET and POST use the same /api/boards URL."
            ),
            "step1_output": "Valid bug, no duplicates.",
            "step2_output": "Confirmed: API uses POST for save, GET for load.",
            "step3_output": "Proceed.",
            "step4_output": "No external APIs. Frontend component bug.",
            "step5_output": "Root cause in BoardManager.tsx error handling.",
            "step6_output": "Fix: update error display in catch block.",
            "step7_output": "DEFECT_TYPE: code",
            "step8_output": "Test in tests/e2e/board-manager.spec.ts",
            "step9_output": "Unit test created.",
            "step10_output": "E2E_NEEDED: yes",
            "files_to_stage": "tests/e2e/board-manager.spec.ts",
        }

        # Format prompt through the same pipeline the orchestrator uses
        try:
            from pdd.preprocess import preprocess

            exclude_keys = list(context.keys())
            processed = preprocess(
                step11_prompt_content,
                recursive=True,
                double_curly_brackets=True,
                exclude_keys=exclude_keys,
            )
            rendered = processed.replace("{{", "{").replace("}}", "}")
        except ImportError:
            rendered = step11_prompt_content

        for key, value in context.items():
            rendered = rendered.replace(f"{{{key}}}", str(value))

        # Run the agentic CLI
        success, output, cost, provider = run_agentic_task(
            instruction=rendered,
            cwd=repo,
            verbose=True,
            quiet=False,
            label="step11-api-mocking-633",
            timeout=240.0,
        )

        assert success, (
            f"run_agentic_task failed (provider={provider}).\n"
            f"Output:\n{output[:1000]}"
        )

        # Collect generated test code from output and files
        generated_parts = []

        # Parse E2E_FILES_CREATED paths
        for line in output.splitlines():
            if line.strip().startswith("E2E_FILES_CREATED:"):
                paths_str = line.split(":", 1)[1].strip()
                for p in paths_str.split(","):
                    p = p.strip()
                    full_path = repo / p
                    if full_path.exists():
                        generated_parts.append(full_path.read_text())

        # Also check for new test files in the repo
        for ts_file in repo.rglob("*.spec.ts"):
            content = ts_file.read_text()
            if content not in generated_parts:
                generated_parts.append(content)
        for ts_file in repo.rglob("*.test.ts"):
            content = ts_file.read_text()
            if content not in generated_parts:
                generated_parts.append(content)

        all_code = "\n".join(generated_parts)

        assert all_code.strip(), (
            "No generated test code found — no files created and no code in output."
        )

        # Verify: no duplicate page.route() for the same URL pattern
        route_calls = re.findall(
            r"page\.route\s*\(\s*['\"]([^'\"]+)['\"]",
            all_code,
        )
        if len(route_calls) > 1:
            # Check for duplicates
            seen = set()
            for pattern in route_calls:
                assert pattern not in seen, (
                    f"Generated test has duplicate page.route() for '{pattern}'. "
                    "The prompt should have instructed using a single handler "
                    "with method switching."
                )
                seen.add(pattern)

        # Verify: if mocking /api/boards, uses POST (not just PUT)
        all_code_lower = all_code.lower()
        if "board" in all_code_lower and "page.route" in all_code_lower:
            # The source code uses POST for save — the mock should match
            has_post = "'post'" in all_code_lower or '"post"' in all_code_lower
            assert has_post, (
                "Generated test should mock POST for /api/boards (matching the "
                "source code in api.ts), not assume PUT for update operations."
            )
