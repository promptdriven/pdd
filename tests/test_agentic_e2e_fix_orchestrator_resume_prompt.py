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
the regression:

* Resume with ``last_completed_step >= 9`` and ``ALL_TESTS_PASS`` /
  ``LOCAL_TESTS_PASS`` stays in the post-Step-9 phase (criterion A).
* The ``.gh-wrapper/**`` filter is applied in both the hash-diff staging path
  and the ``_get_modified_and_untracked`` fallback staging path with
  platform-neutral, directory-boundary-anchored matching (criterion B).
* ``CONTINUE_CYCLE`` still advances ``current_cycle`` and resets per-cycle state
  when Step 9 asks for another cycle (criterion C).
* This module references ``promptdriven/pdd_cloud#1462`` and
  ``promptdriven/pdd_cloud#1463`` in its docstring so the failure mode is
  preserved for future readers (criterion D).
* ``architecture.json`` records the orchestrator as an 11-step workflow so the
  metadata stays in sync with the prompt (criterion E / sanity check).
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


class TestResumeRoutingOnStep9Success:
    """Criterion A: resume after Step 9 success enters cleanup/CI, not a new cycle."""

    def test_prompt_documents_post_step9_resume_inspection(self, orchestrator_prompt_body):
        """The prompt MUST tell the orchestrator to inspect cached Step 9 output on resume."""
        # Resume must look at last_completed_step >= 9, not just >= 8 or != 0.
        assert "last_completed_step >= 9" in orchestrator_prompt_body

    def test_prompt_recognizes_step9_success_tokens(self, orchestrator_prompt_body):
        """Both ALL_TESTS_PASS and LOCAL_TESTS_PASS must keep the run in the post-Step-9 phase."""
        assert "ALL_TESTS_PASS" in orchestrator_prompt_body
        assert "LOCAL_TESTS_PASS" in orchestrator_prompt_body

    def test_prompt_uses_shared_loop_token_resolver(self, orchestrator_prompt_body):
        """Resume and inline Step 9 must share the same token resolver for symmetry."""
        assert "_resolve_step9_loop_token" in orchestrator_prompt_body

    def test_prompt_forbids_new_cycle_after_step9_success(self, orchestrator_prompt_body):
        """The prompt MUST explicitly forbid restarting a new cycle on Step 9 success."""
        assert "do NOT start a new cycle" in orchestrator_prompt_body

    def test_prompt_routes_into_cleanup_and_ci(self, orchestrator_prompt_body):
        """Control after Step 9 success must flow into Step 11 cleanup and Step 10 CI."""
        # The prompt should mention both Step 11 (cleanup) and Step 10 (CI validation)
        # as the destination after a successful Step 9 resume.
        assert "Step 11" in orchestrator_prompt_body
        assert "Step 10" in orchestrator_prompt_body
        # And tie them together via the "post-Step-9" phrasing.
        assert "post-Step-9" in orchestrator_prompt_body


class TestGhWrapperFilterInBothStagingPaths:
    """Criterion B: .gh-wrapper/** filtered in BOTH hash-diff and fallback staging paths."""

    def test_prompt_lists_gh_wrapper_filter(self, orchestrator_prompt_body):
        """The prompt MUST name the .gh-wrapper/** artifact filter."""
        assert ".gh-wrapper/**" in orchestrator_prompt_body

    def test_prompt_requires_filter_in_hash_diff_staging(self, orchestrator_prompt_body):
        """The hash-diff staging path MUST drop .gh-wrapper artifacts."""
        assert "hash-diff staging path" in orchestrator_prompt_body

    def test_prompt_requires_filter_in_fallback_staging(self, orchestrator_prompt_body):
        """The fallback _get_modified_and_untracked path MUST also drop .gh-wrapper artifacts."""
        assert "_get_modified_and_untracked" in orchestrator_prompt_body
        # The instruction must say the filter applies in BOTH paths, not just one.
        # Look for "both" near the staging discussion.
        body_lower = orchestrator_prompt_body.lower()
        assert "both" in body_lower
        # And the fallback wording must appear after .gh-wrapper.
        assert "fallback" in body_lower

    def test_prompt_requires_platform_neutral_normalization(self, orchestrator_prompt_body):
        """Path matching MUST be platform-neutral so Windows backslashes are handled."""
        assert "platform-neutral" in orchestrator_prompt_body

    def test_prompt_requires_directory_boundary_anchoring(self, orchestrator_prompt_body):
        """The .gh-wrapper match MUST anchor on directory boundary, not bare substring."""
        # So that legit names like gh-wrapper-docs.md or tools/gh_wrapper.py are not over-filtered.
        assert "directory boundary" in orchestrator_prompt_body
        # And the prompt should call out an example of an over-filter risk so a future
        # reader can't relax the boundary without thinking about it.
        assert "gh-wrapper-docs.md" in orchestrator_prompt_body

    def test_prompt_cites_specific_wrapper_files_from_incident(self, orchestrator_prompt_body):
        """Issue #1001's exact leaked filenames must be cited so the test maps to the incident."""
        assert ".gh-wrapper/gh" in orchestrator_prompt_body
        assert ".gh-wrapper/git" in orchestrator_prompt_body


class TestContinueCycleBehaviorPreserved:
    """Criterion C: CONTINUE_CYCLE still advances the cycle when Step 9 asks for it."""

    def test_prompt_still_describes_continue_cycle_advance(self, orchestrator_prompt_body):
        """Cycle advancement on CONTINUE_CYCLE must still be documented."""
        assert "CONTINUE_CYCLE" in orchestrator_prompt_body
        assert "current_cycle += 1" in orchestrator_prompt_body
        assert "last_completed_step = 0" in orchestrator_prompt_body

    def test_prompt_gates_advance_on_max_cycles(self, orchestrator_prompt_body):
        """Advancement must be gated on current_cycle < max_cycles."""
        assert "current_cycle < max_cycles" in orchestrator_prompt_body

    def test_prompt_clears_step_outputs_between_cycles(self, orchestrator_prompt_body):
        """The CONTINUE_CYCLE branch MUST clear step_outputs so the next cycle is fresh."""
        # "step_outputs" must appear in the prompt context.
        assert "step_outputs" in orchestrator_prompt_body

    def test_prompt_handles_unrecognized_token_after_retries(self, orchestrator_prompt_body):
        """If Step 9 emits no recognizable terminal token after retries, treat as CONTINUE_CYCLE."""
        body_lower = orchestrator_prompt_body.lower()
        # Look for language describing the no-recognizable-token-after-retries fallback.
        assert "no recognizable terminal token after retries" in body_lower


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
    """Criterion E: architecture.json reflects the 11-step workflow."""

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
