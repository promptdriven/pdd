"""Unit tests for discover_associated_documents and orchestrator wiring."""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from pdd.sync_order import (
    _is_document_include,
    discover_associated_documents,
)
from pdd.agentic_change_orchestrator import (
    _parse_changed_files,
    CHANGE_STEP_TIMEOUTS,
)


def _write(path: Path, content: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return path


class TestIsDocumentInclude:
    @pytest.mark.parametrize(
        "path, expected",
        [
            ("docs/foo.md", True),
            ("docs/foo.rst", True),
            ("docs/foo.txt", True),
            ("README.md", True),
            ("prompts/foo.prompt", False),
            ("prompts/foo_python.prompt", False),
            ("context/foo_example.py", False),
            ("context/foo_example.ts", False),
            ("pdd/foo.py", False),
            ("src/foo.ts", False),
            ("src/foo.js", False),
            ("docs/FOO.MD", True),
        ],
    )
    def test_filter(self, path: str, expected: bool) -> None:
        assert _is_document_include(path) is expected


class TestPhase1DirectIncludes:
    def test_empty_modified_set_returns_empty(self, tmp_path: Path) -> None:
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        assert discover_associated_documents(set(), prompts_dir) == []

    def test_single_md_include_found(self, tmp_path: Path) -> None:
        prompts_dir = tmp_path / "prompts"
        prompt = _write(
            prompts_dir / "foo_python.prompt",
            "<include>docs/spec.md</include>\nsome content",
        )
        docs = discover_associated_documents({prompt}, prompts_dir)
        assert docs == ["docs/spec.md"]

    def test_mixed_include_types_only_docs_kept(self, tmp_path: Path) -> None:
        prompts_dir = tmp_path / "prompts"
        prompt = _write(
            prompts_dir / "foo_python.prompt",
            "<include>docs/a.md</include>\n"
            "<include>docs/b.rst</include>\n"
            "<include>docs/c.txt</include>\n"
            "<include>context/foo_example.py</include>\n"
            "<include>prompts/other_python.prompt</include>\n"
            "<include>pdd/foo.py</include>\n",
        )
        docs = discover_associated_documents({prompt}, prompts_dir)
        assert set(docs) == {"docs/a.md", "docs/b.rst", "docs/c.txt"}

    def test_missing_prompt_file_warns_and_continues(
        self, tmp_path: Path, caplog: pytest.LogCaptureFixture
    ) -> None:
        prompts_dir = tmp_path / "prompts"
        real = _write(prompts_dir / "real_python.prompt", "<include>docs/real.md</include>")
        missing = prompts_dir / "ghost_python.prompt"
        docs = discover_associated_documents({real, missing}, prompts_dir)
        assert docs == ["docs/real.md"]

    def test_deduplicates_across_modified_prompts(self, tmp_path: Path) -> None:
        prompts_dir = tmp_path / "prompts"
        a = _write(prompts_dir / "a_python.prompt", "<include>docs/shared.md</include>")
        b = _write(prompts_dir / "b_python.prompt", "<include>docs/shared.md</include>")
        docs = discover_associated_documents({a, b}, prompts_dir)
        assert docs == ["docs/shared.md"]

    def test_include_many_single_path_found(self, tmp_path: Path) -> None:
        # Regression: Step 5 prompt promises <include-many> traversal but the
        # original regex only matched <include>, so include-many docs silently
        # bypassed the Step 10.5 safety net.
        prompts_dir = tmp_path / "prompts"
        prompt = _write(
            prompts_dir / "foo_python.prompt",
            "<include-many>README.md</include-many>\n",
        )
        docs = discover_associated_documents({prompt}, prompts_dir)
        assert docs == ["README.md"]

    def test_include_many_comma_split_multiple_paths(self, tmp_path: Path) -> None:
        # Regression (reviewer finding): <include-many>a, b, c</include-many>
        # must expand to three separate doc entries.
        prompts_dir = tmp_path / "prompts"
        prompt = _write(
            prompts_dir / "foo_python.prompt",
            "<include-many>README.md, docs/api.md, docs/schema.rst</include-many>\n",
        )
        docs = discover_associated_documents({prompt}, prompts_dir)
        assert set(docs) == {"README.md", "docs/api.md", "docs/schema.rst"}

    def test_mixed_include_and_include_many_both_discovered(self, tmp_path: Path) -> None:
        prompts_dir = tmp_path / "prompts"
        prompt = _write(
            prompts_dir / "foo_python.prompt",
            "<include>docs/spec.md</include>\n"
            "<include-many>README.md, docs/api.md</include-many>\n",
        )
        docs = discover_associated_documents({prompt}, prompts_dir)
        assert set(docs) == {"docs/spec.md", "README.md", "docs/api.md"}

    def test_include_many_filters_non_docs_same_as_include(self, tmp_path: Path) -> None:
        # The document filter runs after extraction, so include-many entries
        # pointing at code/prompts/examples must still be dropped.
        prompts_dir = tmp_path / "prompts"
        prompt = _write(
            prompts_dir / "foo_python.prompt",
            "<include-many>docs/keep.md, pdd/drop.py, "
            "context/drop_example.py, prompts/drop_python.prompt</include-many>\n",
        )
        docs = discover_associated_documents({prompt}, prompts_dir)
        assert docs == ["docs/keep.md"]

    def test_include_many_newline_separated_payload(self, tmp_path: Path) -> None:
        # Regression (second reviewer pass): pdd.preprocess splits the
        # <include-many> payload on newlines OR commas. The extractor here
        # must match that contract; otherwise a multiline declaration is
        # returned as a single garbled entry.
        prompts_dir = tmp_path / "prompts"
        prompt = _write(
            prompts_dir / "foo_python.prompt",
            "<include-many>\nREADME.md\ndocs/api.md\n</include-many>\n",
        )
        docs = discover_associated_documents({prompt}, prompts_dir)
        assert set(docs) == {"README.md", "docs/api.md"}
        # And the raw payload must never leak as one entry.
        assert "README.md\ndocs/api.md" not in docs

    def test_include_many_mixed_comma_and_newline_separators(self, tmp_path: Path) -> None:
        # Mixed form — newlines as outer separator, commas inside a single line
        # — is what real prompts look like when multi-word lists get wrapped.
        prompts_dir = tmp_path / "prompts"
        prompt = _write(
            prompts_dir / "foo_python.prompt",
            "<include-many>\nREADME.md, docs/api.md\ndocs/schema.md\n</include-many>\n",
        )
        docs = discover_associated_documents({prompt}, prompts_dir)
        assert set(docs) == {"README.md", "docs/api.md", "docs/schema.md"}

    def test_discover_associated_documents_returns_sorted_order(self, tmp_path: Path) -> None:
        # Regression: the prompt + architecture contract declares a
        # deterministic sorted return, but the original implementation
        # preserved discovery/set-iteration order. Two prompts each
        # declaring a distinct doc must produce a sorted result regardless
        # of which prompt the caller lists first.
        prompts_dir = tmp_path / "prompts"
        p_b = _write(prompts_dir / "b_python.prompt", "<include>docs/b.md</include>")
        p_a = _write(prompts_dir / "a_python.prompt", "<include>docs/a.md</include>")
        docs = discover_associated_documents({p_b, p_a}, prompts_dir)
        assert docs == sorted(docs)
        assert docs == ["docs/a.md", "docs/b.md"]

    def test_self_closing_include_form_extracted(self, tmp_path: Path) -> None:
        """Reviewer 6th-pass (F3) regression: real preprocessor supports
        ``<include path="..." />`` and PDD prompts use it. The body-form
        regex alone misses this, leaving a real include form outside #739's
        safety net."""
        from pdd.sync_order import extract_includes_from_file
        prompts_dir = tmp_path / "prompts"
        p = _write(
            prompts_dir / "a_python.prompt",
            '<include path="docs/api.md" />\n'
            '<include path="docs/schema.md" />\n'
            '<include>docs/legacy.md</include>\n'
            '<include query="x">docs/with_attr.md</include>\n',
        )
        got = extract_includes_from_file(p)
        assert got == {"docs/api.md", "docs/schema.md", "docs/legacy.md", "docs/with_attr.md"}

    def test_self_closing_then_body_form_neither_swallows_other(self, tmp_path: Path) -> None:
        """The body-form regex must NOT match a self-closing tag's `>`,
        otherwise it absorbs everything to the next `</include>` and
        garbles the inner includes."""
        from pdd.sync_order import extract_includes_from_file
        prompts_dir = tmp_path / "prompts"
        p = _write(
            prompts_dir / "a_python.prompt",
            '<include path="docs/api.md" />\n'
            '<include path="docs/schema.md" />\n'
            '<include>docs/foo.md</include>\n',
        )
        got = extract_includes_from_file(p)
        assert got == {"docs/api.md", "docs/schema.md", "docs/foo.md"}


class TestPhase2ArchitectureBFS:
    @staticmethod
    def _build_arch(entries: list) -> str:
        return json.dumps(entries)

    def test_no_architecture_path_returns_phase1_only(self, tmp_path: Path) -> None:
        prompts_dir = tmp_path / "prompts"
        prompt = _write(prompts_dir / "a_python.prompt", "<include>docs/p1.md</include>")
        docs = discover_associated_documents({prompt}, prompts_dir, architecture_path=None)
        assert docs == ["docs/p1.md"]

    def test_transitive_dependent_doc_found(self, tmp_path: Path) -> None:
        prompts_dir = tmp_path / "prompts"
        # Modify A. B depends on A. B's prompt includes docs/b.md.
        a = _write(prompts_dir / "a_python.prompt", "")
        _write(prompts_dir / "b_python.prompt", "<include>docs/b.md</include>")
        arch = _write(
            tmp_path / "architecture.json",
            self._build_arch([
                {"filename": "a_python.prompt", "dependencies": []},
                {"filename": "b_python.prompt", "dependencies": ["a_python.prompt"]},
            ]),
        )
        docs = discover_associated_documents({a}, prompts_dir, arch, max_depth=3)
        assert docs == ["docs/b.md"]

    def test_nested_prompt_layout_qualified_dep_form(self, tmp_path: Path) -> None:
        """Modified prompt at ``prompts/core/cli_python.prompt`` (nested
        layout); a dependent declares ``dependencies: ["core/cli_python.prompt"]``
        in the qualified form. Without seeding the frontier with both the
        bare basename AND the qualified relative-to-prompts form, the BFS
        misses the dependent and its associated docs vanish.
        """
        prompts_dir = tmp_path / "prompts"
        nested = _write(
            prompts_dir / "core" / "cli_python.prompt", ""
        )
        _write(
            prompts_dir / "consumer_python.prompt",
            "<include>docs/consumer.md</include>",
        )
        arch = _write(
            tmp_path / "architecture.json",
            self._build_arch([
                {"filename": "core/cli_python.prompt", "dependencies": []},
                {
                    "filename": "consumer_python.prompt",
                    "dependencies": ["core/cli_python.prompt"],
                },
            ]),
        )
        docs = discover_associated_documents(
            {nested}, prompts_dir, arch, max_depth=3
        )
        assert docs == ["docs/consumer.md"]

    def test_nested_prompt_collision_does_not_over_discover(self, tmp_path: Path) -> None:
        """Qualified nested deps must stay precise when two entries share a
        basename. Modifying ``core/cli_python.prompt`` must not pull docs from
        dependents of ``other/cli_python.prompt`` just because both share the
        ``cli_python.prompt`` basename.
        """
        prompts_dir = tmp_path / "prompts"
        core = _write(prompts_dir / "core" / "cli_python.prompt", "")
        _write(prompts_dir / "other" / "cli_python.prompt", "")
        _write(
            prompts_dir / "consumer_core_python.prompt",
            "<include>docs/core.md</include>",
        )
        _write(
            prompts_dir / "consumer_other_python.prompt",
            "<include>docs/other.md</include>",
        )
        arch = _write(
            tmp_path / "architecture.json",
            self._build_arch([
                {"filename": "core/cli_python.prompt", "dependencies": []},
                {"filename": "other/cli_python.prompt", "dependencies": []},
                {
                    "filename": "consumer_core_python.prompt",
                    "dependencies": ["core/cli_python.prompt"],
                },
                {
                    "filename": "consumer_other_python.prompt",
                    "dependencies": ["other/cli_python.prompt"],
                },
            ]),
        )

        docs = discover_associated_documents({core}, prompts_dir, arch, max_depth=1)
        assert docs == ["docs/core.md"]

    def test_max_depth_respected(self, tmp_path: Path) -> None:
        """A <- B <- C; modify A, max_depth=1 should only find B's docs, not C's."""
        prompts_dir = tmp_path / "prompts"
        a = _write(prompts_dir / "a_python.prompt", "")
        _write(prompts_dir / "b_python.prompt", "<include>docs/b.md</include>")
        _write(prompts_dir / "c_python.prompt", "<include>docs/c.md</include>")
        arch = _write(
            tmp_path / "architecture.json",
            self._build_arch([
                {"filename": "a_python.prompt", "dependencies": []},
                {"filename": "b_python.prompt", "dependencies": ["a_python.prompt"]},
                {"filename": "c_python.prompt", "dependencies": ["b_python.prompt"]},
            ]),
        )
        docs_d1 = discover_associated_documents({a}, prompts_dir, arch, max_depth=1)
        assert set(docs_d1) == {"docs/b.md"}
        docs_d3 = discover_associated_documents({a}, prompts_dir, arch, max_depth=3)
        assert set(docs_d3) == {"docs/b.md", "docs/c.md"}

    def test_dedup_across_phases(self, tmp_path: Path) -> None:
        """Doc discovered by both phase 1 (direct) and phase 2 (transitive) appears once."""
        prompts_dir = tmp_path / "prompts"
        a = _write(prompts_dir / "a_python.prompt", "<include>docs/shared.md</include>")
        _write(prompts_dir / "b_python.prompt", "<include>docs/shared.md</include>")
        arch = _write(
            tmp_path / "architecture.json",
            self._build_arch([
                {"filename": "a_python.prompt", "dependencies": []},
                {"filename": "b_python.prompt", "dependencies": ["a_python.prompt"]},
            ]),
        )
        docs = discover_associated_documents({a}, prompts_dir, arch, max_depth=3)
        assert docs == ["docs/shared.md"]

    def test_missing_architecture_json_graceful(self, tmp_path: Path) -> None:
        prompts_dir = tmp_path / "prompts"
        a = _write(prompts_dir / "a_python.prompt", "<include>docs/a.md</include>")
        nonexistent = tmp_path / "missing.json"
        docs = discover_associated_documents({a}, prompts_dir, nonexistent)
        assert docs == ["docs/a.md"]

    def test_malformed_architecture_json_graceful(self, tmp_path: Path) -> None:
        prompts_dir = tmp_path / "prompts"
        a = _write(prompts_dir / "a_python.prompt", "<include>docs/a.md</include>")
        bad = _write(tmp_path / "bad.json", "{not valid json")
        docs = discover_associated_documents({a}, prompts_dir, bad)
        assert docs == ["docs/a.md"]

    def test_architecture_not_list_graceful(self, tmp_path: Path) -> None:
        prompts_dir = tmp_path / "prompts"
        a = _write(prompts_dir / "a_python.prompt", "<include>docs/a.md</include>")
        # arch.json is an object, not a list — malformed for PDD's schema.
        bad = _write(tmp_path / "obj.json", json.dumps({"not": "a list"}))
        docs = discover_associated_documents({a}, prompts_dir, bad)
        assert docs == ["docs/a.md"]

    def test_arch_entry_missing_dependencies_field_tolerated(self, tmp_path: Path) -> None:
        prompts_dir = tmp_path / "prompts"
        a = _write(prompts_dir / "a_python.prompt", "")
        arch = _write(
            tmp_path / "arch.json",
            json.dumps([
                {"filename": "a_python.prompt"},  # no "dependencies" key
                {"filename": "b_python.prompt", "dependencies": ["a_python.prompt"]},
            ]),
        )
        # Should not crash; returns empty (b's prompt has no doc includes)
        docs = discover_associated_documents({a}, prompts_dir, arch)
        assert docs == []

    def test_object_format_architecture_json_supported(self, tmp_path: Path) -> None:
        """Reviewer 6th-pass (F4) regression: extract_modules() in
        architecture_registry accepts both bare-array and `{modules: [...]}`
        object format. Discovery's BFS used to reject non-list data,
        silently disabling transitive doc discovery for repos in the
        object format. Both formats must yield the same docs."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        # Modified prompt has no doc; child depends on parent and has README.
        # When parent is modified, BFS should reach child and find README.
        parent = prompts_dir / "parent_python.prompt"
        parent.write_text("% parent has no doc include", encoding="utf-8")
        (prompts_dir / "child_python.prompt").write_text(
            "% child\n<include>./README.md</include>", encoding="utf-8"
        )

        modules = [
            {"filename": "parent_python.prompt", "dependencies": []},
            {"filename": "child_python.prompt", "dependencies": ["parent_python.prompt"]},
        ]

        # Bare-array form (existing behavior)
        arch_array = tmp_path / "architecture_array.json"
        arch_array.write_text(json.dumps(modules), encoding="utf-8")
        docs_array = discover_associated_documents(
            {parent}, prompts_dir, architecture_path=arch_array, max_depth=3,
        )

        # Object form `{modules: [...]}` — the form most of the codebase
        # actually emits via architecture_registry.
        arch_object = tmp_path / "architecture_object.json"
        arch_object.write_text(json.dumps({"modules": modules}), encoding="utf-8")
        docs_object = discover_associated_documents(
            {parent}, prompts_dir, architecture_path=arch_object, max_depth=3,
        )

        assert docs_array == docs_object, (
            "object-format and bare-array architecture must yield identical "
            f"discovery results: array={docs_array}, object={docs_object}"
        )
        assert "./README.md" in docs_object, (
            f"BFS must reach child's README from object-format arch; got {docs_object}"
        )

    def test_basename_collision_logs_warning(
        self, tmp_path: Path, caplog: pytest.LogCaptureFixture,
    ) -> None:
        """Two arch entries sharing a basename (`cli_python.prompt` and
        `core/cli_python.prompt`) cause BFS to over-discover. Surface this
        as a warning so maintainers can disambiguate at the schema level.
        """
        import logging
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        a = prompts_dir / "a_python.prompt"
        a.write_text("% A", encoding="utf-8")
        arch = tmp_path / "architecture.json"
        arch.write_text(json.dumps([
            {"filename": "cli_python.prompt"},
            {"filename": "core/cli_python.prompt"},
            {"filename": "a_python.prompt"},
        ]), encoding="utf-8")

        with caplog.at_level(logging.WARNING, logger="pdd.sync_order"):
            discover_associated_documents({a}, prompts_dir, arch)

        warnings = [r.message for r in caplog.records if r.levelno == logging.WARNING]
        assert any("basename collisions" in w for w in warnings), (
            f"expected basename-collision warning, got: {warnings}"
        )
        assert any("cli_python.prompt" in w for w in warnings)


# ---------------------------------------------------------------------------
# Orchestrator wiring tests — Step 10 tag parsing and the discovery primitive
# being importable into the orchestrator.
# ---------------------------------------------------------------------------

class TestStep10TagParsing:
    """ASSOCIATED_DOCS_MODIFIED appended to changed_files;
    ASSOCIATED_DOCS_CONFLICTS logged as warning, NOT appended."""

    def test_associated_docs_modified_appended(self) -> None:
        output = (
            "FILES_MODIFIED: prompts/foo_python.prompt\n"
            "ARCHITECTURE_FILES_MODIFIED: architecture.json\n"
            "ASSOCIATED_DOCS_MODIFIED: docs/spec.md, docs/api.md\n"
        )
        files = _parse_changed_files(output)
        assert "prompts/foo_python.prompt" in files
        assert "architecture.json" in files
        assert "docs/spec.md" in files
        assert "docs/api.md" in files

    def test_markdown_formatting_stripped_on_assoc_docs(self) -> None:
        output = "ASSOCIATED_DOCS_MODIFIED: **docs/x.md**, docs/y.md"
        files = _parse_changed_files(output)
        assert "docs/x.md" in files
        assert "docs/y.md" in files
        for f in files:
            assert "*" not in f

    def test_no_associated_docs_section_unchanged(self) -> None:
        """Absent ASSOCIATED_DOCS_* lines: parser behaves as before."""
        output = (
            "FILES_MODIFIED: prompts/foo_python.prompt\n"
            "ARCHITECTURE_FILES_MODIFIED: architecture.json\n"
        )
        files = _parse_changed_files(output)
        assert "prompts/foo_python.prompt" in files
        assert "architecture.json" in files

    def test_conflicts_not_added_to_changed_files(self) -> None:
        """req #7b: CONFLICTS is for warnings only, not for staging."""
        output = (
            "FILES_MODIFIED: prompts/foo_python.prompt\n"
            "ASSOCIATED_DOCS_MODIFIED: docs/safe.md\n"
            "ASSOCIATED_DOCS_CONFLICTS: docs/ambiguous.md\n"
        )
        files = _parse_changed_files(output)
        assert "docs/safe.md" in files
        assert "docs/ambiguous.md" not in files

    def test_conflicts_emit_console_warning(self, capsys: pytest.CaptureFixture) -> None:
        output = "ASSOCIATED_DOCS_CONFLICTS: docs/a.md, docs/b.md"
        _parse_changed_files(output)
        out = capsys.readouterr().out
        assert "manual review" in out.lower()
        assert "docs/a.md" in out
        assert "docs/b.md" in out

    def test_empty_conflicts_line_silent(self, capsys: pytest.CaptureFixture) -> None:
        """Regression: a blank CONFLICTS line followed by another marker
        must not be parsed as containing the next line."""
        output = "ASSOCIATED_DOCS_CONFLICTS: \nFILES_MODIFIED: prompts/foo.prompt"
        _parse_changed_files(output)
        out = capsys.readouterr().out
        assert "manual review" not in out.lower()


class TestOrchestratorWiring:
    """req #15: orchestrator must import discover_associated_documents."""

    def test_function_imported(self) -> None:
        import pdd.agentic_change_orchestrator as orch
        assert hasattr(orch, "discover_associated_documents"), (
            "discover_associated_documents must be imported into "
            "agentic_change_orchestrator (req #15) for Step 10 doc context."
        )
        from pdd.sync_order import discover_associated_documents as src
        assert orch.discover_associated_documents is src

    def test_step10_timeout_bumped(self) -> None:
        """Step 10 timeout was bumped 340→600s for the doc-update pass."""
        assert CHANGE_STEP_TIMEOUTS[10] >= 600.0, (
            f"Step 10 timeout dropped to {CHANGE_STEP_TIMEOUTS[10]}s — "
            "doc sync may time out on larger changes."
        )


# ---------------------------------------------------------------------------
# Wiring integration test — proves the orchestrator actually CALLS
# discover_associated_documents before Step 10 and feeds the result into
# Step 10's context (req #15). This is the deterministic production-risk
# test: the tests above prove discover_associated_documents is correct in
# isolation; only this one proves the orchestrator reaches for it.
# ---------------------------------------------------------------------------

from unittest.mock import patch, MagicMock


class TestOrchestratorWiringIntegration:
    """Drive the orchestrator through steps 1-10 with everything mocked and
    prove the discover_associated_documents call happens with the right args
    and its result reaches Step 10's context."""

    @pytest.fixture
    def orchestrator_mocks(self, tmp_path: Path):
        worktree_path = tmp_path / ".pdd" / "worktrees" / "change-issue-99"
        worktree_path.mkdir(parents=True, exist_ok=True)
        (worktree_path / "prompts").mkdir(exist_ok=True)
        (worktree_path / "architecture.json").write_text("[]", encoding="utf-8")

        with patch("pdd.agentic_change_orchestrator.run_agentic_task") as m_run, \
             patch("pdd.agentic_change_orchestrator.load_workflow_state") as m_load, \
             patch("pdd.agentic_change_orchestrator.save_workflow_state") as m_save, \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.load_prompt_template") as m_tmpl, \
             patch("pdd.agentic_change_orchestrator.subprocess.run") as m_subproc, \
             patch("pdd.agentic_change_orchestrator.build_dependency_graph") as m_bg, \
             patch("pdd.agentic_change_orchestrator.topological_sort") as m_ts, \
             patch("pdd.agentic_change_orchestrator.get_affected_modules") as m_ga, \
             patch("pdd.agentic_change_orchestrator.generate_sync_order_script"), \
             patch("pdd.agentic_change_orchestrator._check_existing_pr", return_value=None), \
             patch("pdd.agentic_change_orchestrator.substitute_template_variables") as m_sub, \
             patch("pdd.agentic_change_orchestrator.discover_associated_documents") as m_disc, \
             patch("pdd.agentic_change_orchestrator._setup_worktree") as m_setup:

            m_load.return_value = (None, None)
            m_save.return_value = 42
            m_tmpl.return_value = MagicMock()
            m_subproc.return_value = MagicMock(stdout=str(tmp_path), returncode=0)
            m_bg.return_value = {}
            m_ts.return_value = ([], [])
            m_ga.return_value = []
            m_sub.side_effect = lambda tmpl, ctx: f"prompt-with-ctx-keys={sorted(ctx.keys())}"
            m_setup.return_value = (worktree_path, None)

            yield {
                "run": m_run,
                "discover": m_disc,
                "sub": m_sub,
                "tmp_path": tmp_path,
                "worktree_path": worktree_path,
            }

    def test_discover_called_with_correct_args_before_step10(self, orchestrator_mocks: dict) -> None:
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        m = orchestrator_mocks
        sentinel_docs = ["docs/test_spec.md", "docs/another.md"]
        m["discover"].return_value = sentinel_docs

        def fake_step(instruction, **kwargs):
            label = kwargs.get("label", "")
            if "step9" in label:
                return (
                    True,
                    "FILES_MODIFIED: prompts/foo_python.prompt, "
                    "prompts/bar_python.prompt, src/unrelated.py\n"
                    "FILES_CREATED: prompts/new_python.prompt",
                    0.1, "gpt-4",
                )
            if "step10" in label:
                return (True, "Arch updated\nARCHITECTURE_FILES_MODIFIED:", 0.1, "gpt-4")
            if "step11" in label:
                return (True, "No Issues Found", 0.1, "gpt-4")
            if "step13" in label:
                return (True, "PR Created: https://example/pr/1", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        m["run"].side_effect = fake_step

        success, _msg, _cost, _model, _files = run_agentic_change_orchestrator(
            issue_url="http://issue", issue_content="Fix bug",
            repo_owner="owner", repo_name="repo", issue_number=99,
            issue_author="me", issue_title="Wiring test",
            cwd=m["tmp_path"], quiet=True,
        )
        assert success is True
        assert m["discover"].call_count == 1

        call = m["discover"].call_args
        modified_prompts = call.kwargs.get("modified_prompts") or call.args[0]
        prompts_dir = call.kwargs.get("prompts_dir")
        architecture_path = call.kwargs.get("architecture_path")
        max_depth = call.kwargs.get("max_depth")

        assert isinstance(modified_prompts, set)
        prompt_names = {p.name for p in modified_prompts}
        assert prompt_names == {
            "foo_python.prompt", "bar_python.prompt", "new_python.prompt",
        }, f"got {prompt_names}; unrelated.py must be filtered"
        assert prompts_dir.name == "prompts"
        assert architecture_path.name == "architecture.json"
        assert max_depth == 3

        step10_ctx = None
        for sub_call in m["sub"].call_args_list:
            ctx = sub_call.args[1]
            if "associated_documents" in ctx:
                step10_ctx = ctx
                break
        assert step10_ctx is not None, (
            "Step 10's prompt was never formatted with associated_documents in context."
        )
        assert step10_ctx["associated_documents"] == ", ".join(sentinel_docs)

    def test_discover_uses_step9_fallback_detected_prompt(self, orchestrator_mocks: dict) -> None:
        """Greg review regression: if Step 9 writes files but omits FILES_*
        markers, Step 10 discovery must still use the fallback-detected
        changed prompt from ``changed_files`` / ``files_to_stage``.
        """
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        m = orchestrator_mocks
        sentinel_docs = ["docs/fallback.md"]
        m["discover"].return_value = sentinel_docs

        def fake_step(instruction, **kwargs):
            label = kwargs.get("label", "")
            if "step9" in label:
                return (True, "Implementation complete; files written.", 0.1, "gpt-4")
            if "step10" in label:
                return (True, "Arch updated\nARCHITECTURE_FILES_MODIFIED:", 0.1, "gpt-4")
            if "step11" in label:
                return (True, "No Issues Found", 0.1, "gpt-4")
            if "step13" in label:
                return (True, "PR Created: https://example/pr/4", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        m["run"].side_effect = fake_step

        with patch(
            "pdd.agentic_change_orchestrator._detect_worktree_changes",
            return_value=["prompts/fallback_python.prompt", "README.md"],
        ) as m_detect:
            success, _msg, _cost, _model, files = run_agentic_change_orchestrator(
                issue_url="http://issue", issue_content="Fix fallback path",
                repo_owner="owner", repo_name="repo", issue_number=99,
                issue_author="me", issue_title="Fallback discovery test",
                cwd=m["tmp_path"], quiet=True,
            )

        assert success is True
        m_detect.assert_called_once()
        assert "prompts/fallback_python.prompt" in files
        assert m["discover"].call_count == 1

        call = m["discover"].call_args
        modified_prompts = call.kwargs.get("modified_prompts") or call.args[0]
        prompt_names = {p.name for p in modified_prompts}
        assert prompt_names == {"fallback_python.prompt"}

        step10_ctx = None
        for sub_call in m["sub"].call_args_list:
            ctx = sub_call.args[1]
            if "associated_documents" in ctx:
                step10_ctx = ctx
                break
        assert step10_ctx is not None
        assert step10_ctx["files_created"] == ""
        assert step10_ctx["files_modified"] == ""
        assert step10_ctx["files_to_stage"] == "prompts/fallback_python.prompt, README.md"
        assert step10_ctx["associated_documents"] == ", ".join(sentinel_docs)

    def test_discover_not_called_when_no_modified_prompts(self, orchestrator_mocks: dict) -> None:
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        m = orchestrator_mocks

        def fake_step(instruction, **kwargs):
            label = kwargs.get("label", "")
            if "step9" in label:
                return (True, "DIRECT_EDITS: src/foo.py", 0.1, "gpt-4")
            if "step10" in label:
                return (True, "Arch updated", 0.1, "gpt-4")
            if "step11" in label:
                return (True, "No Issues Found", 0.1, "gpt-4")
            if "step13" in label:
                return (True, "PR Created: https://example/pr/2", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        m["run"].side_effect = fake_step
        success, *_ = run_agentic_change_orchestrator(
            issue_url="http://issue", issue_content="Direct edit only",
            repo_owner="owner", repo_name="repo", issue_number=99,
            issue_author="me", issue_title="Direct-only test",
            cwd=m["tmp_path"], quiet=True,
        )
        assert success is True
        assert m["discover"].call_count == 0

        step10_ctx = None
        for sub_call in m["sub"].call_args_list:
            ctx = sub_call.args[1]
            if "associated_documents" in ctx:
                step10_ctx = ctx
                break
        assert step10_ctx is not None
        assert step10_ctx["associated_documents"] == "None"

    def test_discover_failure_sets_none_does_not_crash(self, orchestrator_mocks: dict) -> None:
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        m = orchestrator_mocks
        m["discover"].side_effect = RuntimeError("simulated discovery failure")

        def fake_step(instruction, **kwargs):
            label = kwargs.get("label", "")
            if "step9" in label:
                return (True, "FILES_MODIFIED: prompts/foo_python.prompt", 0.1, "gpt-4")
            if "step10" in label:
                return (True, "Arch updated", 0.1, "gpt-4")
            if "step11" in label:
                return (True, "No Issues Found", 0.1, "gpt-4")
            if "step13" in label:
                return (True, "PR Created: https://example/pr/3", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        m["run"].side_effect = fake_step
        success, *_ = run_agentic_change_orchestrator(
            issue_url="http://issue", issue_content="Test error handling",
            repo_owner="owner", repo_name="repo", issue_number=99,
            issue_author="me", issue_title="Discovery crash test",
            cwd=m["tmp_path"], quiet=True,
        )
        assert success is True
        step10_ctx = None
        for sub_call in m["sub"].call_args_list:
            ctx = sub_call.args[1]
            if "associated_documents" in ctx:
                step10_ctx = ctx
                break
        assert step10_ctx is not None
        assert step10_ctx["associated_documents"] == "None"
