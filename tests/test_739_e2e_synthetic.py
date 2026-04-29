"""End-to-end synthetic tests: full orchestrator on a real on-disk mini-repo.

The other test files in this suite either:
  - test the primitives in isolation (test_739_complete unit tests, test_discover_*)
  - test the orchestrator with both _preflight_drift_heal AND discover_*
    mocked away (test_739_complete::TestStep85And105Integration)
  - test discovery + verification on real disk but never invoke the
    orchestrator (test_739_fixtures)

This file closes the remaining coverage gap: build a real on-disk mini-repo
with real prompts, real <include>-ed docs, and real architecture.json — then
run the actual orchestrator with the LLM call as the ONLY mock. That exercises:

  * real ``discover_associated_documents`` reading real prompt files and
    architecture.json,
  * the orchestrator's wiring of discovery → context → Step 10 prompt input,
  * Step 10.5 verifier reacting to realistic Step 10 LLM emissions,
  * the strict-mode abort path through the full state machine.

We still mock ``_preflight_drift_heal`` itself because it requires a fully
populated PDD project (fingerprints, .pddrc, etc.); the real-LLM Layer B
scenarios cover that path on test_repo.
"""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_pdd_repo(tmp_path: Path) -> Path:
    """Create a minimal PDD-shaped worktree: prompts/, docs/, architecture.json."""
    worktree = tmp_path / ".pdd" / "worktrees" / "change-issue-99"
    (worktree / "prompts").mkdir(parents=True, exist_ok=True)
    (worktree / "docs").mkdir(parents=True, exist_ok=True)
    (worktree / "architecture.json").write_text("[]", encoding="utf-8")
    return worktree


def _write_prompt_with_includes(worktree: Path, name: str, doc_paths: list[str]) -> Path:
    """Write a prompt file whose <include> tags reference docs."""
    includes = "\n".join(f"<include>{p}</include>" for p in doc_paths)
    prompt = worktree / "prompts" / name
    prompt.write_text(
        f"% Module {name}\n"
        f"{includes}\n"
        "% Body\n"
        "Build the thing.\n",
        encoding="utf-8",
    )
    return prompt


def _write_doc(worktree: Path, rel_path: str, body: str = "# doc\n") -> Path:
    p = worktree / rel_path
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(body, encoding="utf-8")
    return p


def _orch_kwargs(worktree: Path) -> dict:
    return dict(
        issue_url="http://issue", issue_content="x",
        repo_owner="o", repo_name="r", issue_number=99,
        issue_author="me", issue_title="t",
        cwd=worktree.parent.parent.parent,  # cwd is repo root, worktree is .pdd/worktrees/change-issue-99
        quiet=True,
    )


def _make_orchestrator_patches(worktree: Path):
    """Return a list of patch context managers shared across tests.

    Mocks: run_agentic_task, load/save state, load_prompt_template, subprocess,
    dependency graph helpers, _check_existing_pr, substitute_template_variables,
    _setup_worktree, _preflight_drift_heal. NOT mocked:
    discover_associated_documents, _verify_doc_sync_contract.
    """
    return {
        "run": patch("pdd.agentic_change_orchestrator.run_agentic_task"),
        "load": patch("pdd.agentic_change_orchestrator.load_workflow_state",
                      return_value=(None, None)),
        "save": patch("pdd.agentic_change_orchestrator.save_workflow_state",
                      return_value=42),
        "clear": patch("pdd.agentic_change_orchestrator.clear_workflow_state"),
        "tmpl": patch("pdd.agentic_change_orchestrator.load_prompt_template",
                      return_value=MagicMock()),
        "subproc": patch("pdd.agentic_change_orchestrator.subprocess.run",
                         return_value=MagicMock(stdout=str(worktree), returncode=0)),
        "bg": patch("pdd.agentic_change_orchestrator.build_dependency_graph",
                    return_value={}),
        "ts": patch("pdd.agentic_change_orchestrator.topological_sort",
                    return_value=([], [])),
        "ga": patch("pdd.agentic_change_orchestrator.get_affected_modules",
                    return_value=[]),
        "gen": patch("pdd.agentic_change_orchestrator.generate_sync_order_script"),
        "pr": patch("pdd.agentic_change_orchestrator._check_existing_pr",
                    return_value=None),
        "sub": patch("pdd.agentic_change_orchestrator.substitute_template_variables",
                     side_effect=lambda tmpl, ctx: f"prompt-{sorted(ctx.keys())}"),
        "setup": patch("pdd.agentic_change_orchestrator._setup_worktree",
                       return_value=(worktree, None)),
        "preflight": patch("pdd.agentic_change_orchestrator._preflight_drift_heal",
                           return_value=([], [], [])),
    }


def _enter_all(patches: dict):
    return {k: v.__enter__() for k, v in patches.items()}


def _exit_all(patches: dict):
    for v in patches.values():
        try:
            v.__exit__(None, None, None)
        except Exception:
            pass


# ---------------------------------------------------------------------------
# Test 1: real discovery + real verifier, all docs handled (happy path)
# ---------------------------------------------------------------------------

class TestSyntheticHappyPath:
    """Real on-disk mini-repo. Prompt has 2 <include>-ed docs.

    Step 9 mock reports the prompt as modified. Real discovery walks the
    prompt's <include> tags. Step 10 mock declares all docs handled. Real
    Step 10.5 verifier: clean (no silent drops)."""

    def test_real_discovery_real_verifier_clean_path(self, tmp_path: Path) -> None:
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        worktree = _make_pdd_repo(tmp_path)
        _write_doc(worktree, "docs/api.md", "# API\nGET /users")
        _write_doc(worktree, "README.md", "# Project\nThe thing.")
        prompt = _write_prompt_with_includes(
            worktree, "users_python.prompt",
            ["docs/api.md", "README.md"],
        )

        patches = _make_orchestrator_patches(worktree)
        m = _enter_all(patches)
        try:
            def fake(instruction, **kwargs):
                label = kwargs.get("label", "")
                if "step9" in label:
                    return (True, "FILES_MODIFIED: prompts/users_python.prompt", 0.1, "claude")
                if "step10" in label:
                    return (
                        True,
                        "Arch updated.\n"
                        "ASSOCIATED_DOCS_MODIFIED: docs/api.md\n"
                        "ASSOCIATED_DOCS_UNCHANGED: README.md",
                        0.1, "claude",
                    )
                if "step11" in label:
                    return (True, "No Issues Found", 0.1, "claude")
                if "step13" in label:
                    return (True, "PR Created: https://example/pr/1", 0.1, "claude")
                return (True, f"out-{label}", 0.1, "claude")
            m["run"].side_effect = fake

            success, *_ = run_agentic_change_orchestrator(**_orch_kwargs(worktree))
            assert success is True

            # The verifier must have run on the discovered docs and seen them
            # all handled — no silent-drop warnings should appear in any saved
            # step 10 output.
            step10_outputs = []
            for call in m["save"].call_args_list:
                state_arg = call.args[3]
                so = state_arg.get("step_outputs", {}).get("10")
                if so:
                    step10_outputs.append(so)
            assert step10_outputs, "step 10 output must be persisted"
            for out in step10_outputs:
                assert "DOC_SYNC_SILENT_DROPS" not in out, (
                    f"unexpected silent-drop warning on happy path: {out}"
                )
        finally:
            _exit_all(patches)


# ---------------------------------------------------------------------------
# Test 2: real discovery + real verifier, silent drop caught
# ---------------------------------------------------------------------------

class TestSyntheticSilentDropCaught:
    """Same setup as the happy path, but Step 10 mock OMITS one of the discovered
    docs from its tag emissions. Real Step 10.5 verifier must flag it as a silent
    drop and append the warning to the persisted step 10 output."""

    def test_silent_drop_appended_to_step_output(self, tmp_path: Path) -> None:
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        worktree = _make_pdd_repo(tmp_path)
        _write_doc(worktree, "docs/api.md")
        _write_doc(worktree, "README.md")
        _write_prompt_with_includes(
            worktree, "users_python.prompt",
            ["docs/api.md", "README.md"],
        )

        patches = _make_orchestrator_patches(worktree)
        m = _enter_all(patches)
        try:
            def fake(instruction, **kwargs):
                label = kwargs.get("label", "")
                if "step9" in label:
                    return (True, "FILES_MODIFIED: prompts/users_python.prompt", 0.1, "claude")
                if "step10" in label:
                    # Only handles api.md; README.md is silently dropped
                    return (
                        True,
                        "Arch updated.\nASSOCIATED_DOCS_MODIFIED: docs/api.md",
                        0.1, "claude",
                    )
                if "step11" in label:
                    return (True, "No Issues Found", 0.1, "claude")
                if "step13" in label:
                    return (True, "PR Created: https://example/pr/1", 0.1, "claude")
                return (True, f"out-{label}", 0.1, "claude")
            m["run"].side_effect = fake

            run_agentic_change_orchestrator(**_orch_kwargs(worktree))

            step10_output = None
            for call in m["save"].call_args_list:
                state_arg = call.args[3]
                so = state_arg.get("step_outputs", {}).get("10")
                if so:
                    step10_output = so
            assert step10_output is not None, "step 10 output must be persisted"
            assert "DOC_SYNC_SILENT_DROPS" in step10_output
            assert "README.md" in step10_output, (
                f"silent-dropped doc must appear in warning: {step10_output}"
            )
        finally:
            _exit_all(patches)


# ---------------------------------------------------------------------------
# Test 3: real discovery via architecture.json BFS (transitive)
# ---------------------------------------------------------------------------

class TestSyntheticTransitiveDiscovery:
    """Modify prompt A. Architecture says B depends on A. B's prompt has a doc
    include. Real discover_associated_documents should walk the BFS and find
    B's doc. Real Step 10.5 verifier should flag it if Step 10 omits."""

    def test_transitive_doc_caught_when_step10_omits(self, tmp_path: Path) -> None:
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        worktree = _make_pdd_repo(tmp_path)

        # A: leaf prompt with no doc includes
        _write_prompt_with_includes(worktree, "a_python.prompt", [])
        # B: depends on A in architecture, has a doc include
        _write_doc(worktree, "docs/b_endpoint.md")
        _write_prompt_with_includes(
            worktree, "b_python.prompt",
            ["docs/b_endpoint.md"],
        )
        (worktree / "architecture.json").write_text(json.dumps([
            {"filename": "a_python.prompt", "dependencies": []},
            {"filename": "b_python.prompt", "dependencies": ["a_python.prompt"]},
        ]), encoding="utf-8")

        patches = _make_orchestrator_patches(worktree)
        m = _enter_all(patches)
        try:
            def fake(instruction, **kwargs):
                label = kwargs.get("label", "")
                # Step 9 reports only A as modified; transitive discovery
                # must find B's doc anyway.
                if "step9" in label:
                    return (True, "FILES_MODIFIED: prompts/a_python.prompt", 0.1, "claude")
                if "step10" in label:
                    # Step 10 silently drops the transitively-discovered doc
                    return (True, "Arch updated.", 0.1, "claude")
                if "step11" in label:
                    return (True, "No Issues Found", 0.1, "claude")
                if "step13" in label:
                    return (True, "PR Created: https://example/pr/1", 0.1, "claude")
                return (True, f"out-{label}", 0.1, "claude")
            m["run"].side_effect = fake

            run_agentic_change_orchestrator(**_orch_kwargs(worktree))

            step10_output = None
            for call in m["save"].call_args_list:
                state_arg = call.args[3]
                so = state_arg.get("step_outputs", {}).get("10")
                if so:
                    step10_output = so
            assert step10_output is not None
            # The transitively-discovered b_endpoint.md was dropped by Step 10.
            # Real discovery + real verifier must surface it.
            assert "DOC_SYNC_SILENT_DROPS" in step10_output, step10_output
            assert "docs/b_endpoint.md" in step10_output, step10_output
        finally:
            _exit_all(patches)


# ---------------------------------------------------------------------------
# Test 4: PDD_STRICT_DOC_SYNC=1 aborts the workflow on silent drop
# ---------------------------------------------------------------------------

class TestSyntheticStrictModeAbort:
    """Through the real orchestrator: with PDD_STRICT_DOC_SYNC=1 set and a
    silent drop in Step 10's emission, the workflow must return success=False
    with the silent-drop modules named in the error message."""

    def test_strict_mode_returns_failure_with_drop_names(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        worktree = _make_pdd_repo(tmp_path)
        _write_doc(worktree, "docs/critical.md")
        _write_prompt_with_includes(
            worktree, "x_python.prompt",
            ["docs/critical.md"],
        )

        monkeypatch.setenv("PDD_STRICT_DOC_SYNC", "1")

        patches = _make_orchestrator_patches(worktree)
        m = _enter_all(patches)
        try:
            def fake(instruction, **kwargs):
                label = kwargs.get("label", "")
                if "step9" in label:
                    return (True, "FILES_MODIFIED: prompts/x_python.prompt", 0.1, "claude")
                if "step10" in label:
                    # Drops critical.md silently
                    return (True, "Arch updated.", 0.1, "claude")
                # Steps 11–13 should never run because strict-mode aborts.
                return (True, f"out-{label}", 0.1, "claude")
            m["run"].side_effect = fake

            success, message, *_ = run_agentic_change_orchestrator(**_orch_kwargs(worktree))
            assert success is False, "strict mode must abort on silent drop"
            assert "PDD_STRICT_DOC_SYNC" in message
            assert "docs/critical.md" in message
        finally:
            _exit_all(patches)


# ---------------------------------------------------------------------------
# Test 5: negative space — prompt with no includes, no architecture deps
# ---------------------------------------------------------------------------

class TestSyntheticNegativeSpace:
    """Prompt has no <include> tags; architecture.json is empty.
    Discovery must return [] and Step 10.5 must trivially pass — no warnings
    appended even when Step 10 emits no markers."""

    def test_issue_touching_no_prompt_skips_discovery_entirely(
        self, tmp_path: Path,
    ) -> None:
        """When Step 9's FILES_MODIFIED contains no .prompt entries, discovery
        must not even be invoked — the orchestrator should short-circuit on
        the empty modified_prompts set."""
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        worktree = _make_pdd_repo(tmp_path)
        # Code-only change scenario: a doc and a non-prompt file edited
        _write_doc(worktree, "docs/handwritten.md")
        (worktree / "src").mkdir(exist_ok=True)
        (worktree / "src" / "thing.py").write_text("x = 1\n", encoding="utf-8")

        patches = _make_orchestrator_patches(worktree)
        # Use the real discovery so we can prove it doesn't fire spuriously
        m = _enter_all(patches)
        try:
            def fake(instruction, **kwargs):
                label = kwargs.get("label", "")
                if "step9" in label:
                    return (
                        True,
                        "FILES_MODIFIED: src/thing.py, docs/handwritten.md",
                        0.1, "claude",
                    )
                if "step10" in label:
                    return (True, "Arch updated.", 0.1, "claude")
                if "step11" in label:
                    return (True, "No Issues Found", 0.1, "claude")
                if "step13" in label:
                    return (True, "PR Created: https://example/pr/1", 0.1, "claude")
                return (True, f"out-{label}", 0.1, "claude")
            m["run"].side_effect = fake

            success, *_ = run_agentic_change_orchestrator(**_orch_kwargs(worktree))
            assert success is True

            for call in m["save"].call_args_list:
                state_arg = call.args[3]
                so = state_arg.get("step_outputs", {}).get("10")
                if so:
                    assert "DOC_SYNC_SILENT_DROPS" not in so, (
                        f"non-prompt files must not trigger doc-sync warnings: {so}"
                    )
        finally:
            _exit_all(patches)

    def test_no_includes_no_architecture_no_false_alarms(self, tmp_path: Path) -> None:
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        worktree = _make_pdd_repo(tmp_path)
        _write_prompt_with_includes(worktree, "loner_python.prompt", [])

        patches = _make_orchestrator_patches(worktree)
        m = _enter_all(patches)
        try:
            def fake(instruction, **kwargs):
                label = kwargs.get("label", "")
                if "step9" in label:
                    return (True, "FILES_MODIFIED: prompts/loner_python.prompt", 0.1, "claude")
                if "step10" in label:
                    return (True, "Arch updated.", 0.1, "claude")  # no doc markers
                if "step11" in label:
                    return (True, "No Issues Found", 0.1, "claude")
                if "step13" in label:
                    return (True, "PR Created: https://example/pr/1", 0.1, "claude")
                return (True, f"out-{label}", 0.1, "claude")
            m["run"].side_effect = fake

            success, *_ = run_agentic_change_orchestrator(**_orch_kwargs(worktree))
            assert success is True

            for call in m["save"].call_args_list:
                state_arg = call.args[3]
                so = state_arg.get("step_outputs", {}).get("10")
                if so:
                    assert "DOC_SYNC_SILENT_DROPS" not in so, (
                        f"discovery returned [] but verifier still warned: {so}"
                    )
        finally:
            _exit_all(patches)
