"""
E2E Tests for Issue #549: format string double-escaping causes agentic sync
failures when prompts contain JSON curly braces.

Root cause: agentic_bug_orchestrator.py escapes LLM step outputs with
    escaped = output.replace("{", "{{").replace("}", "}}")
before storing them in context, then calls template.format(**context).
Python's str.format() inserts values LITERALLY — it does NOT un-double {{}}
in substituted values (only in the template string itself). So the LLM
receives {{"error": ...}} instead of {"error": ...}.

The same escaping bug exists on the resume path (line 317) and in multiple
other orchestrator files (agentic_change_orchestrator.py, etc.).

Fix: Replace .format(**context) with iterative str.replace() — the existing
safe pattern in template_expander.py:155-156 — and remove the value escaping.
"""

import re
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator


# ---------------------------------------------------------------------------
# Fixtures (mirror test_agentic_bug_orchestrator.py conventions)
# ---------------------------------------------------------------------------


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory.

    Required so that preprocess() can resolve <include> directives when the
    template contains them (harmless for templates without includes).
    """
    import pdd as pdd_pkg
    pdd_package_dir = Path(pdd_pkg.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


@pytest.fixture
def mock_dependencies(tmp_path):
    """Patches external dependencies used by run_agentic_bug_orchestrator."""
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree:

        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (mock_worktree_path, None)

        yield mock_run, mock_load


@pytest.fixture
def default_args(tmp_path):
    """Default keyword arguments for run_agentic_bug_orchestrator."""
    return {
        "issue_url": "http://github.com/owner/repo/issues/1",
        "issue_content": "Bug description",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_author": "user",
        "issue_title": "Bug Title",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
    }


def _make_side_effects(step_outputs_by_label=None, *, captured=None):
    """Return a side-effect function for mock_run.

    Args:
        step_outputs_by_label: dict mapping label -> (output_str). Other steps
            get a generic success response. step7 gets FILES_CREATED if not
            overridden (required to avoid the hard-stop at step 7).
        captured: optional dict; if given, the instruction for each label is
            stored in it.
    """
    step_outputs_by_label = step_outputs_by_label or {}

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", "")
        if captured is not None:
            captured[label] = instruction
        if label in step_outputs_by_label:
            out = step_outputs_by_label[label]
            return (True, out, 0.1, "gpt-4")
        if label == "step7":
            # Avoid the "no FILES_CREATED" hard stop
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    return side_effect


# ---------------------------------------------------------------------------
# Test 1 (PRIMARY): JSON in step output must appear literally in next prompt
# ---------------------------------------------------------------------------


def test_json_in_step_output_not_double_escaped_in_next_prompt(
    mock_dependencies, default_args
):
    """
    Issue #549 PRIMARY: JSON curly braces from a step's LLM output must
    appear as single braces in the subsequent step's formatted prompt.

    Buggy behaviour (current code):
      Step 1 returns: {"error": "Insufficient role", "required": "admin"}
      Code escapes:   {{"error": "Insufficient role", "required": "admin"}}
      After .format(): step 2 instruction contains doubled braces {{...}}

    Expected behaviour (after fix):
      Step 2 instruction contains the original JSON literally with single braces.
    """
    mock_run, mock_load = mock_dependencies

    JSON_OUTPUT = '{"error": "Insufficient role", "required": "admin"}'
    captured = {}

    mock_run.side_effect = _make_side_effects(
        step_outputs_by_label={"step1": JSON_OUTPUT},
        captured=captured,
    )

    # Step 2 template references step 1's output
    def load_side_effect(name):
        if "step2" in name:
            return "Previous finding: {step1_output}"
        return "Prompt for {issue_number}"

    mock_load.side_effect = load_side_effect

    run_agentic_bug_orchestrator(**default_args)

    step2_instruction = captured.get("step2", "")
    assert step2_instruction, "run_agentic_task was not called for step2"

    # BUG: instruction contains {{"error": ...}} (doubled) — corrupts the LLM prompt
    assert "{{" not in step2_instruction, (
        f"Step 2 prompt has doubled curly braces — Issue #549 bug present.\n"
        f"Got: {repr(step2_instruction)}"
    )
    # FIX: original JSON must appear literally
    assert JSON_OUTPUT in step2_instruction, (
        f"Step 2 prompt should contain the original JSON {repr(JSON_OUTPUT)}.\n"
        f"Got: {repr(step2_instruction)}"
    )


# ---------------------------------------------------------------------------
# Test 2: Format-placeholder-like text in step output must survive unchanged
# ---------------------------------------------------------------------------


def test_step_output_with_format_like_placeholder_not_doubled(
    mock_dependencies, default_args
):
    """
    Issue #549: Step output containing {url}-style text must pass through
    unchanged. The current escaping turns {url} into {{url}}, which after
    .format(**context) appears literally as {{url}} in the next step's
    instruction — instead of the expected {url}.

    A further .format() call in llm_invoke.py would then either raise
    KeyError('url') or silently substitute a wrong value.
    """
    mock_run, mock_load = mock_dependencies

    STEP_OUTPUT = "Error: {url} was not found in the request context."
    captured = {}

    mock_run.side_effect = _make_side_effects(
        step_outputs_by_label={"step1": STEP_OUTPUT},
        captured=captured,
    )

    def load_side_effect(name):
        if "step2" in name:
            return "Previous: {step1_output}"
        return "Prompt for {issue_number}"

    mock_load.side_effect = load_side_effect

    run_agentic_bug_orchestrator(**default_args)

    step2_instruction = captured.get("step2", "")
    assert step2_instruction, "run_agentic_task was not called for step2"

    # BUG: {{url}} appears instead of {url}
    assert "{{url}}" not in step2_instruction, (
        f"Step 2 prompt has {{{{url}}}} (doubled) — Issue #549 bug.\n"
        f"Got: {repr(step2_instruction)}"
    )
    # FIX: single-brace {url} must be in the instruction
    assert "{url}" in step2_instruction, (
        f"Step 2 prompt should contain literal {{url}}.\n"
        f"Got: {repr(step2_instruction)}"
    )


# ---------------------------------------------------------------------------
# Test 3: Nested JSON must not accumulate brace doubling
# ---------------------------------------------------------------------------


def test_nested_json_in_step_output_preserved(mock_dependencies, default_args):
    """
    Issue #549 EDGE CASE: Nested JSON objects must not have their inner braces
    doubled multiple times.

    Buggy: {{"response": {{"status": 403, "body": {{"error": "Forbidden"}}}}}}
    Fixed: {"response": {"status": 403, "body": {"error": "Forbidden"}}}
    """
    mock_run, mock_load = mock_dependencies

    NESTED_JSON = '{"response": {"status": 403, "body": {"error": "Forbidden"}}}'
    captured = {}

    mock_run.side_effect = _make_side_effects(
        step_outputs_by_label={"step1": NESTED_JSON},
        captured=captured,
    )

    def load_side_effect(name):
        if "step2" in name:
            return "Finding: {step1_output}"
        return "Prompt for {issue_number}"

    mock_load.side_effect = load_side_effect

    run_agentic_bug_orchestrator(**default_args)

    step2_instruction = captured.get("step2", "")
    assert step2_instruction, "run_agentic_task was not called for step2"

    assert "{{" not in step2_instruction, (
        f"Nested JSON has doubled braces — Issue #549 bug.\n"
        f"Got: {repr(step2_instruction)}"
    )
    assert NESTED_JSON in step2_instruction, (
        f"Nested JSON not preserved. Got: {repr(step2_instruction)}"
    )


# ---------------------------------------------------------------------------
# Test 4: Multiple JSON blocks in a single step output must all be preserved
# ---------------------------------------------------------------------------


def test_multiple_json_blocks_in_step_output_preserved(
    mock_dependencies, default_args
):
    """
    Issue #549 EDGE CASE: Multiple JSON objects in one step output must each
    have their curly braces preserved (not doubled).
    """
    mock_run, mock_load = mock_dependencies

    STEP_OUTPUT = 'First: {"a": 1}. Second: {"b": 2, "c": "three"}.'
    captured = {}

    mock_run.side_effect = _make_side_effects(
        step_outputs_by_label={"step1": STEP_OUTPUT},
        captured=captured,
    )

    def load_side_effect(name):
        if "step2" in name:
            return "Analysis: {step1_output}"
        return "Prompt for {issue_number}"

    mock_load.side_effect = load_side_effect

    run_agentic_bug_orchestrator(**default_args)

    step2_instruction = captured.get("step2", "")
    assert step2_instruction, "run_agentic_task was not called for step2"

    assert "{{" not in step2_instruction, (
        f"Multiple JSON blocks have doubled braces — Issue #549 bug.\n"
        f"Got: {repr(step2_instruction)}"
    )
    assert '{"a": 1}' in step2_instruction, (
        f"First JSON block not preserved. Got: {repr(step2_instruction)}"
    )
    assert '{"b": 2, "c": "three"}' in step2_instruction, (
        f"Second JSON block not preserved. Got: {repr(step2_instruction)}"
    )


# ---------------------------------------------------------------------------
# Test 5 (REGRESSION): Plain text step outputs still substitute correctly
# ---------------------------------------------------------------------------


def test_plain_text_step_output_substituted_correctly(
    mock_dependencies, default_args
):
    """
    REGRESSION: Plain text step outputs (no curly braces) must still be
    substituted into subsequent step prompts correctly after the fix.
    """
    mock_run, mock_load = mock_dependencies

    PLAIN_OUTPUT = "No issues found in the authentication module."
    captured = {}

    mock_run.side_effect = _make_side_effects(
        step_outputs_by_label={"step1": PLAIN_OUTPUT},
        captured=captured,
    )

    def load_side_effect(name):
        if "step2" in name:
            return "Step 1 result: {step1_output}. Please continue."
        return "Prompt for {issue_number}"

    mock_load.side_effect = load_side_effect

    run_agentic_bug_orchestrator(**default_args)

    step2_instruction = captured.get("step2", "")
    assert step2_instruction, "run_agentic_task was not called for step2"

    assert PLAIN_OUTPUT in step2_instruction, (
        f"Plain text output not substituted. Got: {repr(step2_instruction)}"
    )


# ---------------------------------------------------------------------------
# Test 6 (UNIT): The safe str.replace() approach correctly preserves JSON
# ---------------------------------------------------------------------------


def test_safe_str_replace_substitution_preserves_json_braces():
    """
    Unit test showing that the str.replace() pattern (proposed fix, from
    template_expander.py:155-156) preserves JSON curly braces, while the
    buggy .format(**context) + value escaping does NOT.

    This documents the fundamental Python behaviour:
      str.format() does NOT un-double {{ }} in *substituted values* —
      only in the template string itself.
    """
    template = "Analysis: {step1_output}"
    json_value = '{"error": "Insufficient role", "required": "admin"}'
    context = {"step1_output": json_value}

    # --- Buggy approach (current code) ---
    escaped = json_value.replace("{", "{{").replace("}", "}}")
    buggy_result = template.format(**{"step1_output": escaped})
    # buggy_result == 'Analysis: {{"error": "Insufficient role", "required": "admin"}}'

    # --- Safe approach (proposed fix: template_expander.py pattern) ---
    safe_result = template
    for key, value in context.items():
        safe_result = safe_result.replace("{" + key + "}", str(value))
    # safe_result == 'Analysis: {"error": "Insufficient role", "required": "admin"}'

    # The safe result must contain the original JSON literally with no doubling
    assert json_value in safe_result, (
        f"Safe substitution should preserve JSON. Got: {repr(safe_result)}"
    )
    assert "{{" not in safe_result, (
        f"Safe substitution must not produce doubled braces. Got: {repr(safe_result)}"
    )
    # The buggy result contains doubled braces — this documents the corruption
    assert "{{" in buggy_result, (
        f"Buggy result should contain doubled braces (documents the bug). "
        f"Got: {repr(buggy_result)}"
    )
    # The two results must differ — proves the fix changes behaviour
    assert safe_result != buggy_result


# ---------------------------------------------------------------------------
# Test 7 (STRUCTURAL): Buggy value-escaping pattern must not exist in source
# ---------------------------------------------------------------------------


def test_agentic_bug_orchestrator_does_not_escape_context_values():
    """
    Issue #549 STRUCTURAL: agentic_bug_orchestrator.py must NOT escape
    context values with .replace("{", "{{") before prompt substitution.

    Lines 317 and 435 of the current code contain:
        escaped_output = output.replace("{", "{{").replace("}", "}}")
    which is the root cause of Issue #549.

    After the fix, this pattern should be absent.
    """
    import pdd.agentic_bug_orchestrator as mod

    source_path = Path(mod.__file__)
    source = source_path.read_text()

    # The buggy escaping pattern applied to context values
    buggy_pattern = '.replace("{", "{{").replace("}", "}}")'

    assert buggy_pattern not in source, (
        f"Found buggy brace-escaping pattern in {source_path.name} — "
        "this is the root cause of Issue #549.\n"
        "Remove the .replace('{', '{{') calls and use iterative str.replace() "
        "for template substitution instead of .format(**context)."
    )


# ---------------------------------------------------------------------------
# Test 8 (STRUCTURAL): All orchestrators must use safe format pattern
# ---------------------------------------------------------------------------


def test_all_orchestrators_do_not_use_format_with_context_dict():
    """
    Issue #549 STRUCTURAL: No agentic orchestrator file should use
    .format(**context) for prompt substitution. This two-pass .format()
    chain (orchestrator + llm_invoke.py) causes the double-escaping bug.

    After the fix all orchestrators should use iterative str.replace()
    following the template_expander.py:155-156 pattern.
    """
    import pdd as pdd_pkg

    pdd_dir = Path(pdd_pkg.__file__).parent
    orchestrator_files = list(pdd_dir.glob("agentic_*_orchestrator.py"))

    assert orchestrator_files, f"No orchestrator files found in {pdd_dir}"

    violations = []
    for filepath in orchestrator_files:
        source = filepath.read_text()
        if ".format(**context)" in source:
            violations.append(filepath.name)

    assert not violations, (
        f"Orchestrator files still use .format(**context) — Issue #549 pattern: "
        f"{violations}. Replace with iterative str.replace() following "
        "template_expander.py:155-156."
    )


# ---------------------------------------------------------------------------
# E2E Integration Tests (Step 9): Use REAL prompt templates, mock only LLM
# ---------------------------------------------------------------------------
# These tests differ from tests 1–8 above by NOT mocking load_prompt_template.
# The orchestrator loads real templates from pdd/prompts/ which contain the
# real {step1_output} / {step2_output} placeholders.  Only run_agentic_task
# (the LLM call) is mocked so we can control what each "step" returns and
# inspect what instruction the next step actually receives.
# ---------------------------------------------------------------------------


@pytest.fixture
def real_template_deps(tmp_path):
    """
    Patches only the LLM layer and worktree setup; leaves load_prompt_template
    and preprocess() untouched so the real template code path runs.
    """
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree:

        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        mock_worktree.return_value = (mock_worktree_path, None)

        yield mock_run


def test_e2e_json_in_step1_output_double_escaped_in_real_step2_prompt(
    real_template_deps, default_args
):
    """
    E2E Integration: JSON from step 1's LLM output is double-escaped when it
    appears in step 2's prompt instruction.

    This test uses the REAL agentic_bug_step2_docs_LLM.prompt template loaded
    from disk (no mock for load_prompt_template).  Only run_agentic_task is
    mocked so we control what step 1 returns and can inspect step 2's
    instruction.

    Bug (current code, line 435 of agentic_bug_orchestrator.py):
      step 1 returns  : {"error": "Insufficient role"}
      code stores     : {{"error": "Insufficient role"}}  ← incorrect escaping
      step 2 receives : …{{"error": "Insufficient role"}}…  ← doubled braces

    Fix (iterative str.replace):
      step 2 receives : …{"error": "Insufficient role"}…   ← single braces
    """
    mock_run = real_template_deps

    JSON_OUTPUT = '{"error": "Insufficient role", "required": "admin"}'
    captured = {}

    def side_effect(**kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", "")
        captured[label] = instruction
        if label == "step1":
            return (True, JSON_OUTPUT, 0.1, "gpt-4")
        if label == "step7":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    run_agentic_bug_orchestrator(**default_args)

    step2_instruction = captured.get("step2", "")
    assert step2_instruction, "run_agentic_task was not called for step2"

    # BUG: real template formatted with escaped value produces doubled braces
    assert "{{" not in step2_instruction, (
        f"Step 2 prompt (real template) has doubled curly braces — Issue #549 "
        f"bug is present in the full orchestrator code path.\n"
        f"Got instruction snippet: {repr(step2_instruction[:300])}"
    )
    # FIX: the original JSON literal must reach the LLM unchanged
    assert JSON_OUTPUT in step2_instruction, (
        f"Step 2 prompt should contain the original JSON {repr(JSON_OUTPUT)}.\n"
        f"Got instruction snippet: {repr(step2_instruction[:300])}"
    )


def test_e2e_json_in_step2_output_double_escaped_in_real_step3_prompt(
    real_template_deps, default_args
):
    """
    E2E Integration: JSON in step 2's LLM output corrupts step 3's real prompt.

    This exercises the second occurrence of the escaping bug (step 2 → step 3)
    to confirm the issue is not limited to step 1 outputs.
    """
    mock_run = real_template_deps

    JSON_OUTPUT = '{"type": "error", "code": 403, "message": "Forbidden"}'
    captured = {}

    def side_effect(**kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", "")
        captured[label] = instruction
        if label == "step2":
            return (True, JSON_OUTPUT, 0.1, "gpt-4")
        if label == "step7":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    run_agentic_bug_orchestrator(**default_args)

    step3_instruction = captured.get("step3", "")
    assert step3_instruction, "run_agentic_task was not called for step3"

    assert "{{" not in step3_instruction, (
        f"Step 3 prompt (real template) has doubled curly braces — Issue #549 "
        f"affects the step2→step3 boundary.\n"
        f"Got instruction snippet: {repr(step3_instruction[:300])}"
    )
    assert JSON_OUTPUT in step3_instruction, (
        f"Step 3 prompt should contain the original JSON {repr(JSON_OUTPUT)}.\n"
        f"Got instruction snippet: {repr(step3_instruction[:300])}"
    )


def test_e2e_orchestrator_completes_without_keyerror_with_json_step_outputs(
    real_template_deps, default_args
):
    """
    E2E Integration: The full orchestrator run does not raise KeyError when
    every step returns JSON-containing output.

    In the current buggy code, if a JSON key happens to match a Python format
    specifier (e.g. {"error": ...} → {{"error": ...}} after escaping), the
    second .format() pass in llm_invoke.py raises KeyError.  This test
    exercises all steps with JSON outputs to confirm no uncaught KeyError.
    """
    mock_run = real_template_deps

    # These JSON outputs include keys that look like Python format placeholders
    # to maximise the chance of triggering the KeyError failure mode.
    json_outputs_by_step = {
        "step1": '{"status": "new", "duplicate": false}',
        "step2": '{"confirmed": true, "error": "none"}',
        "step3": '{"proceed": true, "type": "bug"}',
        "step4": '{"reproduced": true, "code": 500}',
        "step5": '{"root_cause": "format string", "fix": "str.replace"}',
        "step5_5": 'DEFECT_TYPE: code\n{"classification": "code_bug"}',
        "step6": '{"plan": [{"step": 1}, {"step": 2}]}',
        "step7": 'FILES_CREATED: tests/test_549.py\n{"created": true}',
        "step8": '{"passing": false, "count": 6}',
    }

    def side_effect(**kwargs):
        label = kwargs.get("label", "")
        step_key = re.sub(r"_\d+$", "", label)  # strip retry suffix if any
        return (True, json_outputs_by_step.get(step_key, f"Output for {label}"), 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    # Should not raise KeyError — but may return failure due to missing FILES_CREATED etc.
    try:
        result = run_agentic_bug_orchestrator(**default_args)
    except KeyError as exc:
        pytest.fail(
            f"Issue #549: KeyError raised during orchestrator run with JSON step outputs.\n"
            f"KeyError key: {exc}\n"
            f"This means the second .format() call in the pipeline interpreted a JSON key "
            f"as a Python format placeholder.\n"
            f"Fix: replace .format(**context) with iterative str.replace()."
        )
