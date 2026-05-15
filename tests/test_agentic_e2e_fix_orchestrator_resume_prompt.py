"""Regression tests for issue #1001: post-Step-9 resume routing and ``.gh-wrapper`` filter.

Failure mode being locked in (source incident: ``promptdriven/pdd_cloud#1462`` /
PR ``promptdriven/pdd_cloud#1463``, 2026-05-13):

    1. ``pdd fix`` completes Step 9 with ``ALL_TESTS_PASS`` and pushes the real fix.
    2. The run pauses for insufficient credits while moving into CI validation.
    3. After credits are added, ``pdd fix`` correctly resumes the outer command,
       but the inner e2e-fix orchestrator restarts from Step 1 instead of
       continuing into the post-Step-9 cleanup (Step 11) and CI validation
       (Step 10) phases.
    4. The restarted cycle wastes ~$3 of LLM budget and produces a third commit
       containing only executor wrapper artifacts:

           A .gh-wrapper/gh
           A .gh-wrapper/git

    5. A manual cleanup commit (``8ab8cb25a`` on ``promptdriven/pdd_cloud``) is
       needed to remove the wrapper-artifact diff.

These tests assert that the public prompt body for
``agentic_e2e_fix_orchestrator_python.prompt`` documents the fix that prevents
the regression, scoping each assertion to the specific ``% <Section>`` block
of the prompt so that unrelated text elsewhere in the (very long) prompt body
cannot accidentally satisfy a check:

* Resume routing on Step 9 success lives in the ``% Resume & State`` section
  and ties ``last_completed_step >= 9``, ``ALL_TESTS_PASS`` /
  ``LOCAL_TESTS_PASS``, the loop-control token resolver, and the
  "do NOT start a new cycle" instruction together (criterion A).
* The ``.gh-wrapper/**`` filter and its both-staging-paths discipline live in
  the ``% Commit / Push (push_with_retry)`` section with platform-neutral,
  directory-boundary anchoring (criterion B).
* ``CONTINUE_CYCLE`` still advances ``current_cycle`` and resets per-cycle
  state when Step 9 asks for another cycle, AND the new max-cycles-exhausted
  branch surfaces ``MAX_CYCLES_REACHED`` instead of restarting or falsely
  declaring success (criterion C).
* This module references ``promptdriven/pdd_cloud#1462`` and
  ``promptdriven/pdd_cloud#1463`` in its docstring so the failure mode is
  preserved for future readers (criterion D).
* ``architecture.json`` records the orchestrator as an 11-step workflow and
  the prompt's ``<pdd-interface>`` declares the
  ``force_with_lease_on_non_fast_forward`` parameter so prompt metadata stays
  in sync (criterion E).
"""

import json
import re
from pathlib import Path

import pytest

from pdd.load_prompt_template import load_prompt_template


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Resolve prompt templates from this worktree, not the parent repo checkout."""
    monkeypatch.setenv("PDD_PATH", str(Path(__file__).resolve().parent.parent))


def _strip_pdd_metadata(template: str) -> str:
    """Strip ``<pdd-reason>`` and ``<pdd-interface>`` metadata blocks from a prompt template."""
    template = re.sub(r'<pdd-reason>.*?</pdd-reason>', '', template, flags=re.DOTALL)
    template = re.sub(r'<pdd-interface>.*?</pdd-interface>', '', template, flags=re.DOTALL)
    return template


def _get_section(body: str, title: str) -> str:
    """Return the text of a ``% <title>`` section.

    The prompt uses ``% Section Title`` headers. A section runs from its header
    line up to (but not including) the next ``% `` header line or end-of-file.
    Scoping assertions to a single section proves the prompt's logical
    structure, not just keyword presence somewhere in the very long body.

    The title may end in punctuation (e.g. ``Commit / Push (push_with_retry)``),
    so we anchor on end-of-line after the title rather than ``\\b`` which would
    fail when the title ends with ``)``.
    """
    pattern = rf'^% {re.escape(title)}[ \t]*$.*?(?=^% |\Z)'
    m = re.search(pattern, body, re.DOTALL | re.MULTILINE)
    assert m, f"Section {title!r} not found in prompt body"
    return m.group(0)


def _find_repo_root() -> Path:
    """Find the repository root by walking up from the test file."""
    candidate = Path(__file__).resolve().parent.parent
    # In cloud CI, the source may be at /workspace or a subdirectory
    for root in [candidate, Path("/workspace"), candidate.parent]:
        if (root / "pyproject.toml").exists():
            return root
    return candidate


def _read_repo_text(relative_path: str) -> str:
    """Read a repository file relative to the worktree root."""
    repo_root = _find_repo_root()
    path = repo_root / relative_path
    if not path.exists():
        pytest.skip(f"Repository file not available in this environment: {relative_path}")
    return path.read_text(encoding="utf-8")


def _get_orchestrator_architecture_entry() -> dict:
    """Load the architecture.json entry for the e2e-fix orchestrator prompt."""
    entries = json.loads(_read_repo_text("architecture.json"))
    return next(
        entry
        for entry in entries
        if entry["filename"] == "agentic_e2e_fix_orchestrator_python.prompt"
    )


@pytest.fixture(scope="module")
def orchestrator_prompt_body() -> str:
    """Load and metadata-strip the orchestrator prompt body once per module."""
    template = load_prompt_template("agentic_e2e_fix_orchestrator_python")
    assert template is not None, "agentic_e2e_fix_orchestrator_python.prompt must load"
    return _strip_pdd_metadata(template)


@pytest.fixture(scope="module")
def orchestrator_prompt_raw() -> str:
    """Load the orchestrator prompt template WITHOUT stripping metadata.

    Needed for assertions on the ``<pdd-interface>`` block (which the regular
    fixture strips). Read directly so we cannot accidentally pick up a
    stripped-and-re-included version.
    """
    repo_root = _find_repo_root()
    path = repo_root / "pdd" / "prompts" / "agentic_e2e_fix_orchestrator_python.prompt"
    if not path.exists():
        pytest.skip("Orchestrator prompt file not available in this environment")
    return path.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def resume_section(orchestrator_prompt_body) -> str:
    """The ``% Resume & State`` section of the prompt body."""
    return _get_section(orchestrator_prompt_body, "Resume & State")


@pytest.fixture(scope="module")
def commit_push_section(orchestrator_prompt_body) -> str:
    """The ``% Commit / Push (push_with_retry)`` section of the prompt body."""
    return _get_section(orchestrator_prompt_body, "Commit / Push (push_with_retry)")


class TestResumeRoutingOnStep9Success:
    """Criterion A: resume after Step 9 success enters cleanup/CI, not a new cycle.

    All assertions are scoped to the ``% Resume & State`` section so that
    unrelated prompt text elsewhere cannot accidentally satisfy them.
    """

    def test_resume_section_inspects_last_completed_step(self, resume_section):
        """The resume section MUST tell the orchestrator to inspect cached Step 9 output on resume."""
        # Resume must look at last_completed_step >= 9, not just >= 8 or != 0.
        assert "last_completed_step >= 9" in resume_section

    def test_resume_section_recognizes_step9_success_tokens(self, resume_section):
        """Both ALL_TESTS_PASS and LOCAL_TESTS_PASS must keep the run in the post-Step-9 phase."""
        assert "ALL_TESTS_PASS" in resume_section
        assert "LOCAL_TESTS_PASS" in resume_section

    def test_resume_section_uses_shared_loop_token_resolver(self, resume_section):
        """Resume and inline Step 9 must share the same token resolver for symmetry."""
        assert "_resolve_step9_loop_token" in resume_section

    def test_resume_section_forbids_new_cycle_after_step9_success(self, resume_section):
        """The resume section MUST explicitly forbid restarting a new cycle on Step 9 success."""
        assert "do NOT start a new cycle" in resume_section

    def test_resume_section_routes_into_cleanup_and_ci(self, resume_section):
        """Control after Step 9 success must flow into Step 11 cleanup and Step 10 CI."""
        # The destination phases must be named in this same section.
        assert "Step 11" in resume_section
        assert "Step 10" in resume_section
        # And tied together via the "post-Step-9" phrasing.
        assert "post-Step-9" in resume_section.lower() or "Post-Step-9" in resume_section

    def test_resume_section_references_issue_1001(self, resume_section):
        """The resume branching paragraph must cite Issue #1001 so future readers see the link."""
        assert "Issue #1001" in resume_section

    def test_resume_section_orders_inspection_before_advance(self, resume_section):
        """Within the resume section, ``last_completed_step >= 9`` must appear BEFORE
        ``current_cycle += 1`` — proving the prompt teaches "inspect, then maybe advance"
        rather than "advance unconditionally"."""
        inspect_match = re.search(r"last_completed_step\s*>=\s*9", resume_section)
        advance_match = re.search(r"current_cycle\s*\+=\s*1", resume_section)
        assert inspect_match is not None, "inspection token missing"
        assert advance_match is not None, "advance token missing"
        assert inspect_match.start() < advance_match.start(), (
            "Resume section must inspect last_completed_step >= 9 BEFORE advancing current_cycle += 1"
        )

    def test_resume_section_orders_success_token_before_advance(self, resume_section):
        """``ALL_TESTS_PASS`` (the keep-state branch) must appear BEFORE
        ``current_cycle += 1`` (the advance branch), proving the success
        branch is checked first."""
        success_match = re.search(r"ALL_TESTS_PASS", resume_section)
        advance_match = re.search(r"current_cycle\s*\+=\s*1", resume_section)
        assert success_match is not None
        assert advance_match is not None
        assert success_match.start() < advance_match.start(), (
            "Resume section must check ALL_TESTS_PASS (keep state) BEFORE describing current_cycle += 1 (advance)"
        )

    def test_resume_section_negative_not_only_short_advance_rule(self, resume_section):
        """Guard against regression to the pre-fix wording.

        Before issue #1001 the prompt only said "advance the cycle on resume"
        with no branching. The resume section MUST contain the new branching
        language ("do NOT start a new cycle" plus a ``last_completed_step >= 9``
        inspection) — not just the bare advance rule. If a future edit
        removes the branching language and leaves only the unconditional
        advance, this test fails.
        """
        assert "do NOT start a new cycle" in resume_section, (
            "Resume section must retain the explicit 'do NOT start a new cycle' branch"
        )
        assert "last_completed_step >= 9" in resume_section, (
            "Resume section must retain the last_completed_step >= 9 inspection"
        )


class TestMaxCyclesExhaustionOnResume:
    """Criterion C-extended: resume with no remaining cycles surfaces MAX_CYCLES_REACHED.

    Addresses the gap codex flagged in round 1: when Step 9's cached output is
    ``CONTINUE_CYCLE`` (or unrecognized) AND ``current_cycle >= max_cycles``,
    the resume path must NOT advance and must NOT fall through to cleanup as
    if the run succeeded.
    """

    def test_resume_section_handles_max_cycles_exhaustion(self, resume_section):
        """The resume section MUST describe the ``current_cycle >= max_cycles`` branch."""
        # Token must appear in this section, not elsewhere in the prompt.
        assert "current_cycle >= max_cycles" in resume_section

    def test_resume_section_routes_exhaustion_to_max_cycles_reached(self, resume_section):
        """When the exhaustion branch triggers, the resume section names MAX_CYCLES_REACHED."""
        assert "MAX_CYCLES_REACHED" in resume_section

    def test_resume_section_co_locates_exhaustion_with_max_cycles_reached(self, resume_section):
        """The two tokens must co-occur in the same sentence/paragraph so the
        mapping (exhaustion -> MAX_CYCLES_REACHED) is unambiguous."""
        # Find the offset of each token; they should be close (within the same paragraph).
        exhaust = re.search(r"current_cycle\s*>=\s*max_cycles", resume_section)
        max_token = re.search(r"MAX_CYCLES_REACHED", resume_section)
        assert exhaust is not None and max_token is not None
        # Both should occur in the same paragraph — the post-Step-9 resume branching paragraph.
        # Use a generous co-location window (within ~600 chars) to allow for the
        # surrounding "do NOT advance / do NOT fall through" framing.
        assert abs(exhaust.start() - max_token.start()) < 600, (
            "current_cycle >= max_cycles and MAX_CYCLES_REACHED should be co-located in the resume branching paragraph"
        )


class TestGhWrapperFilterInBothStagingPaths:
    """Criterion B: .gh-wrapper/** filtered in BOTH hash-diff and fallback staging paths.

    All assertions are scoped to the ``% Commit / Push (push_with_retry)``
    section so we prove the language lives in the staging discussion, not
    elsewhere in the prompt body.
    """

    def test_commit_push_section_lists_gh_wrapper_filter(self, commit_push_section):
        """The commit/push section MUST name the .gh-wrapper/** artifact filter."""
        assert ".gh-wrapper/**" in commit_push_section

    def test_commit_push_section_names_hash_diff_staging_path(self, commit_push_section):
        """The hash-diff staging path MUST be named explicitly."""
        assert "hash-diff staging path" in commit_push_section

    def test_commit_push_section_names_fallback_staging_path(self, commit_push_section):
        """The fallback _get_modified_and_untracked staging path MUST also be named."""
        assert "_get_modified_and_untracked" in commit_push_section
        assert "fallback" in commit_push_section.lower()

    def test_commit_push_section_requires_filter_in_both_paths(self, commit_push_section):
        """The instruction must say the filter applies in BOTH paths, not just one."""
        assert "both" in commit_push_section.lower(), (
            "Commit/Push section must say the .gh-wrapper filter applies in BOTH staging paths"
        )

    def test_commit_push_section_requires_platform_neutral_normalization(self, commit_push_section):
        """Path matching MUST be platform-neutral so Windows backslashes are handled."""
        assert "platform-neutral" in commit_push_section

    def test_commit_push_section_requires_directory_boundary_anchoring(self, commit_push_section):
        """The .gh-wrapper match MUST anchor on directory boundary, not bare substring."""
        # So that legit names like gh-wrapper-docs.md or tools/gh_wrapper.py are not over-filtered.
        assert "directory boundary" in commit_push_section
        # And the section should call out an example of an over-filter risk so a future
        # reader can't relax the boundary without thinking about it.
        assert "gh-wrapper-docs.md" in commit_push_section

    def test_commit_push_section_cites_specific_wrapper_files_from_incident(self, commit_push_section):
        """Issue #1001's exact leaked filenames must be cited in this section."""
        assert ".gh-wrapper/gh" in commit_push_section
        assert ".gh-wrapper/git" in commit_push_section

    def test_commit_push_section_references_issue_1001(self, commit_push_section):
        """The .gh-wrapper filter must cite Issue #1001 so the failure mode is traceable."""
        assert "Issue #1001" in commit_push_section

    def test_commit_push_section_orders_gh_wrapper_before_fallback_path(self, commit_push_section):
        """The primary ``.gh-wrapper/**`` filter must be named BEFORE the
        fallback staging path is discussed, proving the prompt teaches the
        primary-path filter and THEN the must-also-apply-to-fallback rule."""
        primary = re.search(r"\.gh-wrapper/\*\*", commit_push_section)
        fallback = re.search(r"_get_modified_and_untracked", commit_push_section)
        assert primary is not None and fallback is not None
        assert primary.start() < fallback.start(), (
            "Commit/Push section must name .gh-wrapper/** BEFORE the _get_modified_and_untracked fallback path"
        )

    def test_commit_push_section_negative_not_just_gitignore_reliance(self, commit_push_section):
        """Guard against regression to "just rely on .gitignore" wording.

        The fix must teach the orchestrator that staging code must NOT rely on
        ``.gitignore`` alone (because ``git add <path>`` bypasses gitignore).
        If a future edit removes the "must not rely on that alone" caveat and
        falls back to gitignore reliance, this test fails.
        """
        # The "not rely on gitignore alone" caveat must be present.
        assert "bypasses gitignore" in commit_push_section, (
            "Commit/Push section must keep the 'git add <path> bypasses gitignore' caveat"
        )


class TestContinueCycleBehaviorPreserved:
    """Criterion C: CONTINUE_CYCLE still advances the cycle when Step 9 asks for it.

    Scoped to the ``% Resume & State`` section.
    """

    def test_resume_section_still_describes_continue_cycle_advance(self, resume_section):
        """Cycle advancement on CONTINUE_CYCLE must still be documented in the resume section."""
        assert "CONTINUE_CYCLE" in resume_section
        assert "current_cycle += 1" in resume_section
        assert "last_completed_step = 0" in resume_section

    def test_resume_section_gates_advance_on_max_cycles(self, resume_section):
        """Advancement must be gated on current_cycle < max_cycles."""
        assert "current_cycle < max_cycles" in resume_section

    def test_resume_section_clears_step_outputs_between_cycles(self, resume_section):
        """The CONTINUE_CYCLE branch MUST clear step_outputs so the next cycle is fresh."""
        assert "step_outputs" in resume_section

    def test_resume_section_handles_unrecognized_token_after_retries(self, resume_section):
        """If Step 9 emits no recognizable terminal token after retries, treat as CONTINUE_CYCLE."""
        # Keep the full phrase including "after retries" so the assertion stays specific.
        assert "no recognizable terminal token after retries" in resume_section.lower()


class TestIncidentReferencePresent:
    """Criterion D: the incident is referenced so the failure mode stays clear."""

    def test_module_docstring_references_source_incident(self):
        """This test module's own docstring must reference the pdd_cloud#1462/#1463 sequence."""
        import tests.test_agentic_e2e_fix_orchestrator_resume_prompt as self_module

        doc = self_module.__doc__ or ""
        assert "promptdriven/pdd_cloud#1462" in doc
        assert "promptdriven/pdd_cloud#1463" in doc
        # And the symptom — the leaked wrapper artifacts — must be named.
        assert ".gh-wrapper/gh" in doc
        assert ".gh-wrapper/git" in doc
        # And the credit-pause / wasted-spend framing the issue describes.
        assert "credit" in doc.lower()


class TestArchitectureMetadataSanityCheck:
    """Criterion E: architecture.json reflects the 11-step workflow and the
    prompt's ``<pdd-interface>`` matches architecture.json's signatures."""

    def test_orchestrator_architecture_reason_mentions_11_step_workflow(self):
        """architecture.json's orchestrator entry must describe the 11-step workflow."""
        entry = _get_orchestrator_architecture_entry()

        # The "reason" field is what was updated in this PR.
        reason = entry.get("reason", "")
        assert "11-step" in reason, (
            "architecture.json orchestrator entry 'reason' must reference the 11-step workflow; "
            f"got: {reason!r}"
        )

    def test_orchestrator_architecture_entry_targets_orchestrator_module(self):
        """Sanity: the architecture entry maps to the orchestrator Python module."""
        entry = _get_orchestrator_architecture_entry()
        assert entry["filepath"] == "pdd/agentic_e2e_fix_orchestrator.py"

    def test_prompt_interface_declares_force_with_lease_param(self, orchestrator_prompt_raw):
        """The prompt's <pdd-interface> push_with_retry signature MUST declare
        ``force_with_lease_on_non_fast_forward`` to stay in sync with
        ``architecture.json``."""
        # Parse the <pdd-interface> JSON block out of the raw template.
        m = re.search(
            r'<pdd-interface>\s*(\{.*?\})\s*</pdd-interface>',
            orchestrator_prompt_raw,
            re.DOTALL,
        )
        assert m, "<pdd-interface> block not found in prompt"
        interface = json.loads(m.group(1))
        functions = interface.get("module", {}).get("functions", [])
        push = next(
            (f for f in functions if f.get("name") == "push_with_retry"),
            None,
        )
        assert push is not None, "push_with_retry must be declared in <pdd-interface>"
        assert "force_with_lease_on_non_fast_forward" in push["signature"], (
            "<pdd-interface> push_with_retry signature must declare "
            "force_with_lease_on_non_fast_forward to match architecture.json"
        )

    def test_prompt_interface_mirrors_architecture_json(self, orchestrator_prompt_raw):
        """The prompt's ``<pdd-interface>`` and ``architecture.json`` MUST
        declare the **exact same set** of function names, and every function
        MUST round-trip-match on ``name``, ``signature``, ``returns``, and
        ``sideEffects`` (when architecture.json declares them).

        This is the strong sync check codex flagged in round 2/3: if either
        side drifts -- a function is added or removed on one side without the
        other, a new ``sideEffects`` entry is added to architecture.json,
        a signature is updated, or the prompt's interface is edited without
        the architecture entry being updated -- this test fails.
        """
        # Parse the <pdd-interface> JSON block out of the raw template.
        m = re.search(
            r'<pdd-interface>\s*(\{.*?\})\s*</pdd-interface>',
            orchestrator_prompt_raw,
            re.DOTALL,
        )
        assert m, "<pdd-interface> block not found in prompt"
        prompt_interface = json.loads(m.group(1))
        prompt_functions = prompt_interface.get("module", {}).get("functions", [])
        assert prompt_functions, "<pdd-interface> must declare at least one function"

        arch_entry = _get_orchestrator_architecture_entry()
        arch_functions = (
            arch_entry.get("interface", {}).get("module", {}).get("functions", [])
        )
        assert arch_functions, (
            "architecture.json orchestrator entry must declare at least one function"
        )
        arch_by_name = {f["name"]: f for f in arch_functions}

        # Exact set equality: the prompt and architecture.json must declare
        # the same function names. This catches drops on either side --
        # e.g. the prompt removing an architecture-declared function, or
        # architecture.json adding a function the prompt never mentions.
        prompt_function_names = {f["name"] for f in prompt_functions}
        arch_function_names = set(arch_by_name.keys())
        only_in_prompt = prompt_function_names - arch_function_names
        only_in_arch = arch_function_names - prompt_function_names
        assert prompt_function_names == arch_function_names, (
            "Function-name set drift between prompt's <pdd-interface> and "
            "architecture.json:\n"
            f"  only in prompt:       {sorted(only_in_prompt)!r}\n"
            f"  only in architecture: {sorted(only_in_arch)!r}\n"
            "Both sides MUST declare exactly the same function names."
        )

        # Every function declared in the prompt must mirror its architecture entry.
        for prompt_fn in prompt_functions:
            name = prompt_fn["name"]
            arch_fn = arch_by_name[name]

            # name / signature / returns must match exactly.
            assert prompt_fn["signature"] == arch_fn["signature"], (
                f"Function {name!r} signature drift between prompt and "
                f"architecture.json:\n  prompt:       {prompt_fn['signature']!r}\n"
                f"  architecture: {arch_fn['signature']!r}"
            )
            assert prompt_fn["returns"] == arch_fn["returns"], (
                f"Function {name!r} returns drift between prompt and "
                f"architecture.json:\n  prompt:       {prompt_fn['returns']!r}\n"
                f"  architecture: {arch_fn['returns']!r}"
            )

            # sideEffects: if architecture.json declares them, the prompt MUST
            # declare the same list (order-preserving equality).
            if "sideEffects" in arch_fn:
                assert "sideEffects" in prompt_fn, (
                    f"architecture.json declares sideEffects for {name!r} but "
                    f"the prompt's <pdd-interface> omits them. Add the "
                    f"sideEffects array verbatim to the prompt interface."
                )
                assert prompt_fn["sideEffects"] == arch_fn["sideEffects"], (
                    f"Function {name!r} sideEffects drift between prompt and "
                    f"architecture.json:\n  prompt:       {prompt_fn['sideEffects']!r}\n"
                    f"  architecture: {arch_fn['sideEffects']!r}"
                )


def _parse_signature_param_names(sig_str: str) -> list:
    """Parse parameter NAMES out of a function signature string.

    Handles ``"(a, b, *, c=1, d: T = False)"`` -- keeps declaration order,
    drops the bare ``*`` marker, and strips type annotations / defaults.

    Compares only NAMES, not defaults: a default like ``Optional[float] = None``
    in the prompt vs. ``= None`` in ``inspect.signature`` would falsely diverge
    even though both describe the same parameter. The reviewer-flagged drift
    (#1001 round 8) is about MISSING parameter names, not formatting.

    Parser is intentionally simple: it tracks bracket depth so commas inside
    ``Dict[str, int]`` or ``Optional[float]`` don't split the parameter list.
    Future drift: a default value that itself contains parens (e.g. ``Path()``)
    would break this parser. Not present in the current signature; reassess
    if/when that changes.
    """
    inner = sig_str[sig_str.index("(") + 1 : sig_str.rindex(")")]
    declared_params: list = []
    depth = 0
    buf = ""
    for ch in inner + ",":
        if ch in "([{":
            depth += 1
            buf += ch
        elif ch in ")]}":
            depth -= 1
            buf += ch
        elif ch == "," and depth == 0:
            tok = buf.strip()
            buf = ""
            if not tok or tok == "*":
                continue
            # tok looks like "name", "name: type", "name=val", "name: type = val".
            name = re.split(r"[:\s=]", tok, maxsplit=1)[0].strip()
            if name:
                declared_params.append(name)
        else:
            buf += ch
    return declared_params


class TestRunOrchestratorSignatureSyncedWithCode:
    """Round 8 reviewer gap: ``run_agentic_e2e_fix_orchestrator`` had two kwargs
    (``skip_cleanup``, ``reasoning_time``) added to the .py module without the
    prompt's ``<pdd-interface>`` or ``architecture.json`` metadata being updated.

    These tests pin BOTH metadata sources independently to
    ``inspect.signature(run_agentic_e2e_fix_orchestrator)`` so the same drift
    cannot recur silently: if a future edit adds a kwarg to the function
    without updating BOTH the prompt and architecture.json, one of these tests
    fails before the change can land.

    Defaults are intentionally not compared (e.g. ``Optional[float] = None``
    formats differently than ``None``); only parameter NAMES and ORDER, which
    is the signal the reviewer flagged.
    """

    def test_prompt_interface_signature_pins_actual_function_params(
        self, orchestrator_prompt_raw
    ):
        """The ``<pdd-interface>`` signature for ``run_agentic_e2e_fix_orchestrator``
        must name the same parameters, in the same order, as ``inspect.signature``.

        Catches the drift the external reviewer flagged: ``skip_cleanup`` and
        ``reasoning_time`` were added to the .py code without prompt metadata
        updates (#1001 round 8).
        """
        import inspect
        from pdd.agentic_e2e_fix_orchestrator import (
            run_agentic_e2e_fix_orchestrator,
        )

        actual_params = list(
            inspect.signature(run_agentic_e2e_fix_orchestrator).parameters.keys()
        )

        m = re.search(
            r'<pdd-interface>\s*(\{.*?\})\s*</pdd-interface>',
            orchestrator_prompt_raw,
            re.DOTALL,
        )
        assert m, "<pdd-interface> block not found in prompt"
        prompt_iface = json.loads(m.group(1))
        sig_str = next(
            f
            for f in prompt_iface["module"]["functions"]
            if f["name"] == "run_agentic_e2e_fix_orchestrator"
        )["signature"]

        declared_params = _parse_signature_param_names(sig_str)

        assert declared_params == actual_params, (
            "<pdd-interface> signature param order/names drifted from "
            "inspect.signature(run_agentic_e2e_fix_orchestrator):\n"
            f"  declared in prompt: {declared_params}\n"
            f"  actual in code:     {actual_params}\n"
            f"  symmetric diff:     "
            f"{sorted(set(declared_params) ^ set(actual_params))}"
        )

    def test_architecture_signature_pins_actual_function_params(self):
        """``architecture.json`` ``run_agentic_e2e_fix_orchestrator`` signature
        must name the same parameters, in the same order, as
        ``inspect.signature``.

        Independent of the prompt-side test above: catches the case where the
        prompt is updated but architecture.json is missed (or vice versa).
        """
        import inspect
        from pdd.agentic_e2e_fix_orchestrator import (
            run_agentic_e2e_fix_orchestrator,
        )

        actual_params = list(
            inspect.signature(run_agentic_e2e_fix_orchestrator).parameters.keys()
        )

        entry = _get_orchestrator_architecture_entry()
        arch_functions = (
            entry.get("interface", {}).get("module", {}).get("functions", [])
        )
        sig_str = next(
            f
            for f in arch_functions
            if f["name"] == "run_agentic_e2e_fix_orchestrator"
        )["signature"]

        declared_params = _parse_signature_param_names(sig_str)

        assert declared_params == actual_params, (
            "architecture.json signature param order/names drifted from "
            "inspect.signature(run_agentic_e2e_fix_orchestrator):\n"
            f"  declared in architecture.json: {declared_params}\n"
            f"  actual in code:                {actual_params}\n"
            f"  symmetric diff:                "
            f"{sorted(set(declared_params) ^ set(actual_params))}"
        )
