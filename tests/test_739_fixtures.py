"""Synthetic fixture tests for the change-time doc-sync pipeline.

These tests build real on-disk mini-repos and exercise the *deterministic*
parts of the change pipeline (discovery + verification) end-to-end. The LLM
calls themselves are mocked so the tests are fast, free, and reproducible —
but everything around them is real file I/O so we catch path/IO bugs that
pure mocks can miss.

Five canonical scenarios:
  1. Clean state — no drift, single prompt change → discovery returns []
  2. Direct include — prompt has <include>doc.md → discovery finds it
  3. Transitive — modify A; B depends on A; B includes doc → BFS finds it
  4. Conflict — discovery finds doc, Step 10 flags conflict → not silent drop
  5. Silent drop — discovery finds doc, Step 10 ignores it → contract catches it
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from pdd.sync_order import discover_associated_documents
from pdd.agentic_change_orchestrator import _verify_doc_sync_contract


def _make_repo(tmp_path: Path) -> Path:
    """Create a minimal repo skeleton at tmp_path."""
    (tmp_path / "prompts").mkdir()
    (tmp_path / "docs").mkdir()
    (tmp_path / "context").mkdir()
    return tmp_path


# ---------------------------------------------------------------------------
# Scenario 1 — Clean state
# ---------------------------------------------------------------------------

class TestScenario1Clean:
    """No <include>-ed docs anywhere → discovery is empty, contract trivially passes."""

    def test_discovery_empty_on_doc_free_prompt(self, tmp_path: Path) -> None:
        repo = _make_repo(tmp_path)
        prompt = repo / "prompts" / "calc_python.prompt"
        prompt.write_text(
            "<include>./context/python_preamble.prompt</include>\n"
            "% Write a calculator module.\n",
            encoding="utf-8",
        )
        # Note: python_preamble is a .prompt file, not a doc.

        docs = discover_associated_documents(
            modified_prompts={prompt},
            prompts_dir=repo / "prompts",
            architecture_path=None,
        )
        assert docs == []

    def test_contract_passes_with_empty_discovery(self) -> None:
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            discovered_docs=[],
            step10_output="Arch updated. ARCHITECTURE_FILES_MODIFIED: architecture.json",
        )
        assert mod == [] and conflict == [] and dropped == []


# ---------------------------------------------------------------------------
# Scenario 2 — Direct include
# ---------------------------------------------------------------------------

class TestScenario2DirectInclude:
    """Modify prompt with <include>docs/spec.md → discovery returns [docs/spec.md]."""

    def test_discovery_finds_direct_doc(self, tmp_path: Path) -> None:
        repo = _make_repo(tmp_path)
        spec = repo / "docs" / "spec.md"
        spec.write_text("# Spec\nendpoint: GET /users", encoding="utf-8")
        prompt = repo / "prompts" / "users_python.prompt"
        prompt.write_text(
            "% Build a users service.\n"
            "<include>docs/spec.md</include>\n",
            encoding="utf-8",
        )

        docs = discover_associated_documents(
            modified_prompts={prompt},
            prompts_dir=repo / "prompts",
            architecture_path=None,
        )
        assert docs == ["docs/spec.md"]

    def test_step10_modifies_doc_satisfies_contract(self) -> None:
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            discovered_docs=["docs/spec.md"],
            step10_output=(
                "Arch updated.\n"
                "ARCHITECTURE_FILES_MODIFIED: architecture.json\n"
                "ASSOCIATED_DOCS_MODIFIED: docs/spec.md\n"
            ),
        )
        assert mod == ["docs/spec.md"]
        assert dropped == []


# ---------------------------------------------------------------------------
# Scenario 3 — Transitive via architecture.json BFS
# ---------------------------------------------------------------------------

class TestScenario3Transitive:
    """Modify leaf prompt A; B depends on A; B's prompt has <include>docs/api.md.
    Discovery's phase 2 BFS through architecture.json must surface docs/api.md."""

    def test_bfs_finds_dependent_modules_doc(self, tmp_path: Path) -> None:
        repo = _make_repo(tmp_path)

        # Leaf prompt — no doc includes
        a = repo / "prompts" / "a_python.prompt"
        a.write_text("% Module A\n", encoding="utf-8")

        # Dependent — has a doc include
        api_doc = repo / "docs" / "api.md"
        api_doc.write_text("# API spec\nGET /a → invokes a()", encoding="utf-8")
        b = repo / "prompts" / "b_python.prompt"
        b.write_text(
            "% Module B uses A.\n"
            "<include>docs/api.md</include>\n",
            encoding="utf-8",
        )

        # architecture.json says B depends on A
        arch = repo / "architecture.json"
        arch.write_text(json.dumps([
            {"filename": "a_python.prompt", "dependencies": []},
            {"filename": "b_python.prompt", "dependencies": ["a_python.prompt"]},
        ]), encoding="utf-8")

        docs = discover_associated_documents(
            modified_prompts={a},
            prompts_dir=repo / "prompts",
            architecture_path=arch,
            max_depth=3,
        )
        assert docs == ["docs/api.md"]

    def test_bfs_respects_depth_cap(self, tmp_path: Path) -> None:
        """A ← B ← C; modify A; C's prompt has the doc. max_depth=1 stops at B."""
        repo = _make_repo(tmp_path)

        a = repo / "prompts" / "a_python.prompt"
        a.write_text("% A", encoding="utf-8")
        b = repo / "prompts" / "b_python.prompt"
        b.write_text("% B uses A", encoding="utf-8")  # B's prompt has no docs
        c = repo / "prompts" / "c_python.prompt"
        (repo / "docs" / "deep.md").write_text("# deep doc", encoding="utf-8")
        c.write_text(
            "% C uses B\n<include>docs/deep.md</include>\n", encoding="utf-8"
        )

        arch = repo / "architecture.json"
        arch.write_text(json.dumps([
            {"filename": "a_python.prompt", "dependencies": []},
            {"filename": "b_python.prompt", "dependencies": ["a_python.prompt"]},
            {"filename": "c_python.prompt", "dependencies": ["b_python.prompt"]},
        ]), encoding="utf-8")

        depth1 = discover_associated_documents(
            modified_prompts={a},
            prompts_dir=repo / "prompts",
            architecture_path=arch,
            max_depth=1,
        )
        assert depth1 == []  # only B reachable, B has no doc

        depth3 = discover_associated_documents(
            modified_prompts={a},
            prompts_dir=repo / "prompts",
            architecture_path=arch,
            max_depth=3,
        )
        assert depth3 == ["docs/deep.md"]


# ---------------------------------------------------------------------------
# Scenario 4 — Conflict path
# ---------------------------------------------------------------------------

class TestScenario4Conflict:
    """Discovery finds doc; Step 10 flags it as conflict → contract passes
    (not silent drop)."""

    def test_conflict_explicitly_flagged_satisfies_contract(self, tmp_path: Path) -> None:
        repo = _make_repo(tmp_path)
        (repo / "docs" / "ambiguous.md").write_text("# ambiguous", encoding="utf-8")
        prompt = repo / "prompts" / "x_python.prompt"
        prompt.write_text(
            "<include>docs/ambiguous.md</include>\n", encoding="utf-8"
        )

        docs = discover_associated_documents(
            modified_prompts={prompt},
            prompts_dir=repo / "prompts",
            architecture_path=None,
        )
        assert docs == ["docs/ambiguous.md"]

        # LLM correctly flags it as conflict instead of editing
        step10_output = (
            "Arch updated.\n"
            "ASSOCIATED_DOCS_MODIFIED: \n"
            "ASSOCIATED_DOCS_CONFLICTS: docs/ambiguous.md\n"
        )
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            discovered_docs=docs,
            step10_output=step10_output,
        )
        assert mod == []
        assert conflict == ["docs/ambiguous.md"]
        assert dropped == [], (
            "Explicit conflict tag must satisfy the contract — only silent "
            "drops should appear in the dropped list."
        )


# ---------------------------------------------------------------------------
# Scenario 5 — Silent drop (the bug we built this for)
# ---------------------------------------------------------------------------

class TestScenario5SilentDrop:
    """Discovery finds doc; Step 10 ignores it entirely → 10.5 catches it.
    This is the silent-drop failure class applied to docs."""

    def test_silent_drop_caught_by_contract(self, tmp_path: Path) -> None:
        repo = _make_repo(tmp_path)
        (repo / "docs" / "endpoint.md").write_text("# endpoint", encoding="utf-8")
        prompt = repo / "prompts" / "api_python.prompt"
        prompt.write_text(
            "<include>docs/endpoint.md</include>\n", encoding="utf-8"
        )

        docs = discover_associated_documents(
            modified_prompts={prompt},
            prompts_dir=repo / "prompts",
            architecture_path=None,
        )
        assert docs == ["docs/endpoint.md"]

        # Step 10 LLM forgot to handle it
        step10_output = "Arch updated.\nARCHITECTURE_FILES_MODIFIED: architecture.json\n"
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            discovered_docs=docs,
            step10_output=step10_output,
        )
        assert dropped == ["docs/endpoint.md"], (
            "Silent doc drops must be caught by the Step 10.5 contract verifier "
            "— this is the silent-drop failure mode the workflow is designed "
            "to catch."
        )

    def test_partial_silent_drop_caught(self, tmp_path: Path) -> None:
        """Discovery finds 3 docs, Step 10 handles 2 → 1 silent drop."""
        repo = _make_repo(tmp_path)
        for n in ("a", "b", "c"):
            (repo / "docs" / f"{n}.md").write_text(f"# {n}", encoding="utf-8")
        prompt = repo / "prompts" / "multi_python.prompt"
        prompt.write_text(
            "<include>docs/a.md</include>\n"
            "<include>docs/b.md</include>\n"
            "<include>docs/c.md</include>\n",
            encoding="utf-8",
        )

        docs = discover_associated_documents(
            modified_prompts={prompt},
            prompts_dir=repo / "prompts",
            architecture_path=None,
        )
        assert set(docs) == {"docs/a.md", "docs/b.md", "docs/c.md"}

        step10_output = (
            "Arch updated.\n"
            "ASSOCIATED_DOCS_MODIFIED: docs/a.md, docs/c.md\n"
        )
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            discovered_docs=docs,
            step10_output=step10_output,
        )
        assert set(mod) == {"docs/a.md", "docs/c.md"}
        assert dropped == ["docs/b.md"], (
            "Partial coverage must surface the dropped doc, even when most "
            "were handled."
        )
