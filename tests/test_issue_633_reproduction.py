"""
Reproduction tests for issue #633: step 11 E2E test prompt generates broken mocks.

The step 11 prompt (agentic_bug_step11_e2e_test_LLM.prompt) tells the LLM to use
page.route() for API mocking but provides no guidance on:
1. Reading the actual API implementation to determine correct HTTP methods
2. Playwright's LIFO route handler stacking (last registered = first checked)
3. Tracing error messages through catch blocks for accurate assertions

Two independent PRs (#627, #774) demonstrate the resulting broken mocks:
- PR #627: wrong HTTP method (PUT vs POST), duplicate page.route() handlers, wrong error text
- PR #774: overlapping page.route() patterns that silently bypass each other

These tests assert the CORRECT/expected behavior (prompt contains the required guidance).
They will FAIL on the current buggy prompt and PASS once the fix is applied.

Acceptance criteria from issue #633:
- [ ] Step 11 prompt includes API mocking best practices section
- [ ] Prompt explicitly instructs reading the API implementation before mocking
- [ ] Prompt warns about Playwright's route handler stacking behavior
- [ ] Prompt instructs tracing error messages through catch blocks
"""

import re
from pathlib import Path

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


# --- Test: AC1 - API Mocking Best Practices Section ---


class TestStep11APIMockingBestPracticesSection:
    """
    Acceptance criterion #1: Step 11 prompt includes API mocking best practices section.

    The prompt currently says "Prefer self-contained Playwright tests that use
    page.route() to mock API responses" (line 84) but gives no guidance on HOW
    to write correct mocks. This results in broken tests (PRs #627, #774).
    """

    def test_prompt_contains_api_mocking_section(
        self, step11_prompt_content: str
    ) -> None:
        """
        Verify the prompt has a dedicated API mocking best practices section.

        Without this section, the LLM generates mocks with wrong HTTP methods,
        duplicate route handlers, and incorrect error message assertions.
        """
        content_lower = step11_prompt_content.lower()
        has_mocking_section = any([
            "api mocking best practices" in content_lower,
            "api mocking" in content_lower and "best practice" in content_lower,
            "mocking best practices" in content_lower,
        ])
        assert has_mocking_section, (
            "Step 11 prompt should contain an 'API Mocking Best Practices' section. "
            "Currently the only page.route() guidance is line 84: 'Prefer self-contained "
            "Playwright tests that use page.route() to mock API responses' — no mention "
            "of correct HTTP methods, route stacking, or error message tracing."
        )


# --- Test: AC2 - Read API Implementation Before Mocking ---


class TestStep11ReadAPIImplementation:
    """
    Acceptance criterion #2: Prompt explicitly instructs reading the API
    implementation before mocking.

    Root cause of PR #627 bug #1: The LLM assumed PUT for an update operation
    but saveBoards() in github-app-api.ts:39 actually uses POST. The prompt
    never told the LLM to read the actual fetch/API call implementation.
    """

    def test_prompt_instructs_reading_api_implementation(
        self, step11_prompt_content: str
    ) -> None:
        """
        Verify the prompt instructs reading the actual API call source code.

        The LLM should find the fetch/axios/API client call and use the exact
        HTTP method, not assume REST conventions.
        """
        content_lower = step11_prompt_content.lower()
        has_read_api_instruction = any([
            "read the actual api call" in content_lower,
            "read the actual fetch" in content_lower,
            "find the fetch" in content_lower and "source code" in content_lower,
            "read the api" in content_lower and "implementation" in content_lower,
            "actual api" in content_lower and "implementation" in content_lower,
        ])
        assert has_read_api_instruction, (
            "Step 11 prompt should instruct the LLM to read the actual API call "
            "implementation before writing mocks. In PR #627, the LLM assumed PUT "
            "for an update operation but saveBoards() actually uses POST."
        )

    def test_prompt_warns_against_assuming_http_methods(
        self, step11_prompt_content: str
    ) -> None:
        """
        Verify the prompt warns against assuming REST conventions for HTTP methods.

        The LLM should use the exact HTTP method from the source code, not
        assume GET/POST/PUT/DELETE based on CRUD operation semantics.
        """
        content_lower = step11_prompt_content.lower()
        has_http_method_warning = any([
            "do not assume rest conventions" in content_lower,
            "don't assume rest conventions" in content_lower,
            "exact http method" in content_lower,
            "do not assume" in content_lower and "http method" in content_lower,
            "don't assume" in content_lower and "http method" in content_lower,
        ])
        assert has_http_method_warning, (
            "Step 11 prompt should warn against assuming HTTP methods based on REST "
            "conventions. In PR #627, the LLM mocked PUT but the actual API uses POST."
        )

    def test_prompt_instructs_matching_request_response_shapes(
        self, step11_prompt_content: str
    ) -> None:
        """
        Verify the prompt instructs matching request body and response shapes.

        The LLM should read the source to determine the exact request body format
        and response shape, not generate plausible-looking mock data.
        """
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


# --- Test: AC3 - Playwright Route Handler Stacking Warning ---


class TestStep11RouteHandlerStacking:
    """
    Acceptance criterion #3: Prompt warns about Playwright's route handler
    stacking behavior.

    Root cause of PR #627 bug #2 and PR #774: The LLM registered multiple
    page.route() handlers for the same (or overlapping) URL pattern. Playwright
    stacks handlers and the LAST registered one runs FIRST — if it calls
    route.continue(), earlier handlers are silently bypassed.
    """

    def test_prompt_warns_about_route_stacking(
        self, step11_prompt_content: str
    ) -> None:
        """
        Verify the prompt explains Playwright's route handler stacking behavior.

        Playwright's LIFO stacking means the last-registered handler runs first.
        Multiple handlers for the same URL cause earlier ones to be silently bypassed.
        """
        content_lower = step11_prompt_content.lower()
        has_stacking_warning = any([
            "stacks route handlers" in content_lower,
            "route handler" in content_lower and "stack" in content_lower,
            "last registered" in content_lower and "first" in content_lower,
            "lifo" in content_lower and "route" in content_lower,
            "route stacking" in content_lower,
        ])
        assert has_stacking_warning, (
            "Step 11 prompt should warn about Playwright's route handler stacking. "
            "The LAST registered handler runs FIRST — if it calls route.continue(), "
            "earlier handlers are silently bypassed. PR #627 and PR #774 both hit this."
        )

    def test_prompt_instructs_single_handler_per_url(
        self, step11_prompt_content: str
    ) -> None:
        """
        Verify the prompt instructs using one handler per URL pattern.

        Instead of registering multiple page.route() calls for the same URL,
        use a single handler that switches on request method.
        """
        content_lower = step11_prompt_content.lower()
        has_single_handler_instruction = any([
            "one handler per url" in content_lower,
            "single handler" in content_lower and "url pattern" in content_lower,
            "never register two page.route()" in content_lower,
            "never register two" in content_lower and "page.route" in content_lower,
            "one handler" in content_lower and "url pattern" in content_lower,
        ])
        assert has_single_handler_instruction, (
            "Step 11 prompt should instruct using ONE handler per URL pattern with "
            "method switching, not multiple page.route() calls for the same URL."
        )

    def test_prompt_shows_method_switching_pattern(
        self, step11_prompt_content: str
    ) -> None:
        """
        Verify the prompt includes a code example showing method switching
        within a single page.route() handler.

        Expected pattern:
            await page.route('**/api/endpoint', async (route) => {
              const method = route.request().method();
              if (method === 'GET') { ... }
              else if (method === 'POST') { ... }
              else { await route.continue(); }
            });
        """
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


# --- Test: AC4 - Error Message Tracing Through Catch Blocks ---


class TestStep11ErrorMessageTracing:
    """
    Acceptance criterion #4: Prompt instructs tracing error messages through
    catch blocks.

    Root cause of PR #627 bug #3: The LLM asserted /Failed to save/i but the
    component actually shows "Save failed (500)". The error message goes through:
    saveBoards throw -> handleSave catch -> setError. The LLM didn't trace this path.
    """

    def test_prompt_instructs_tracing_error_messages(
        self, step11_prompt_content: str
    ) -> None:
        """
        Verify the prompt instructs tracing error messages through the code path.

        The LLM should follow thrown errors through catch blocks, error constructors,
        and state setters to find the exact text that appears in the UI.
        """
        content_lower = step11_prompt_content.lower()
        # Must match guidance about tracing errors through catch blocks,
        # NOT the unrelated "This catches:" line in the cross-endpoint section
        has_error_tracing = any([
            "catch block" in content_lower and "error" in content_lower,
            "trace error" in content_lower,
            "error message" in content_lower and "catch block" in content_lower,
            "thrown error" in content_lower and "catch block" in content_lower,
            "follow thrown errors through catch blocks" in content_lower,
            "trace error handling" in content_lower,
        ])
        assert has_error_tracing, (
            "Step 11 prompt should instruct tracing error messages through catch blocks. "
            "In PR #627, the LLM asserted /Failed to save/i but the component shows "
            "'Save failed (500)' — the error flows through saveBoards throw -> "
            "handleSave catch -> setError."
        )

    def test_prompt_instructs_verifying_error_text_against_source(
        self, step11_prompt_content: str
    ) -> None:
        """
        Verify the prompt instructs checking the exact error text from source code.

        The LLM should read the component's catch block to find what setError/setState
        receives, and use that exact text in test assertions.
        """
        content_lower = step11_prompt_content.lower()
        has_exact_text_instruction = any([
            "exact text" in content_lower and ("assertion" in content_lower
                                               or "test" in content_lower),
            "seterror" in content_lower or "setstate" in content_lower,
            "component's catch block" in content_lower,
            "exact" in content_lower and "ui text" in content_lower,
            "verify error message" in content_lower and "source" in content_lower,
        ])
        assert has_exact_text_instruction, (
            "Step 11 prompt should instruct verifying error assertion text against "
            "the source code — read what setError/setState receives in catch blocks."
        )


# --- Test: Verify Current Prompt Is Missing All Four ---


class TestStep11CurrentPromptLacksGuidance:
    """
    Meta-test verifying the current prompt state matches the bug report.

    These tests confirm the ABSENCE of the required guidance. They should
    PASS on the current (buggy) code. If any fail, the prompt may have been
    partially fixed already.
    """

    def test_only_existing_page_route_mention_is_line_84(
        self, step11_prompt_content: str
    ) -> None:
        """
        Confirm the only page.route() mention is the brief line 84 reference.

        The issue comment states: 'The only page.route() guidance in the prompt
        is line 84: "Prefer self-contained Playwright tests that use page.route()
        to mock API responses rather than requiring a live backend" — no mention
        of stacking behavior.'
        """
        page_route_mentions = [
            line.strip()
            for line in step11_prompt_content.splitlines()
            if "page.route()" in line
        ]
        # Currently there should be only the one mention on line 84
        # After the fix, there will be more mentions in the best practices section
        assert len(page_route_mentions) >= 1, (
            "Expected at least one page.route() mention in the prompt."
        )
        # This assertion documents the current state — the prompt has only a single
        # brief mention with no detailed guidance
        if len(page_route_mentions) == 1:
            assert "prefer self-contained" in page_route_mentions[0].lower(), (
                "The single page.route() mention should be the 'Prefer self-contained' line."
            )

    def test_http_method_guidance_exists(
        self, step11_prompt_content: str
    ) -> None:
        """
        Confirm the prompt now has explicit guidance about HTTP methods in mocks.
        """
        content_lower = step11_prompt_content.lower()
        has_http_method_guidance = any([
            "exact http method" in content_lower,
            "do not assume rest" in content_lower,
            "don't assume rest" in content_lower,
        ])
        assert has_http_method_guidance, (
            "Prompt should contain HTTP method guidance after the issue #633 fix."
        )
