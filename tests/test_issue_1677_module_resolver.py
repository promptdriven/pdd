"""Regression tests for issue #1677: pdd sync must resolve modules by canonical
path, not ambiguous short basenames.

Four bugs are covered (CROSS_CUTTING scope — all root causes in module identity
resolution, not N independent call sites):

Bug 1 — ``_filter_invalid_basenames`` (agentic_sync.py:391): the guard
    ``if fp_stem not in basename_counts`` prevents a repeated filepath stem from
    being counted past 1, so two ``page.tsx`` entries in different directories
    never produce a count > 1 for the bare ``"page"`` stem.

Bug 2 — same function (agentic_sync.py:394): ``set(basename_counts.keys())``
    discards count data before the validity loop, so even when a basename IS
    counted > 1 (via the filename path), the ambiguity is invisible and the
    basename is accepted as valid.

Bug 3 — ``_get_filepath_from_architecture`` (sync_determine_operation.py:528):
    the filepath cross-check that filters ambiguous matches is gated on
    ``"/" in basename``; bare names like ``"page"`` fall through to a
    first-match return, silently selecting the wrong module.

Bug 4 — ``run_agentic_sync`` (agentic_sync.py:2279-2289): the ``AsyncSyncRunner``
    in the agentic code path is constructed without ``module_targets``, so
    ``_build_command`` in agentic_sync_runner.py:2098 falls back to the bare
    basename instead of the canonical path-qualified form when building child
    sync subprocess commands.
"""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

pytestmark = pytest.mark.timeout(120)

from pdd.agentic_sync import _filter_invalid_basenames, run_agentic_sync
from pdd.agentic_sync_runner import DepGraphFromArchitectureResult
from pdd.sync_determine_operation import _get_filepath_from_architecture


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _two_page_arch_same_filename():
    """Two ``page.tsx`` modules that share an identical prompt filename.

    This is the exact pattern observed in ``pdd_cloud`` PR #1828 (commits
    82f2723b / 7782f10c, 2026-05-29): both the login page and the settings
    page had ``filename: page_TypeScriptReact.prompt`` but different ``filepath``
    values.  The filename-based counter correctly reaches 2 (Bug 2), but the
    counter is discarded by ``set(basename_counts.keys())`` before the validity
    check, so ``"page"`` passes through as valid.
    """
    return [
        {
            "filename": "page_TypeScriptReact.prompt",
            "filepath": "frontend/src/app/login/page.tsx",
            "dependencies": [],
        },
        {
            "filename": "page_TypeScriptReact.prompt",
            "filepath": "frontend/src/app/settings/page.tsx",
            "dependencies": [],
        },
    ]


def _two_page_arch_different_filenames():
    """Two ``page.tsx`` modules whose prompt filenames differ.

    When the filenames differ (e.g. ``loginPage_TypeScriptReact.prompt`` vs
    ``settingsPage_TypeScriptReact.prompt``), the filename counter never
    reaches 2 for the bare ``"page"`` stem.  Bug 1 then prevents the filepath
    stem from being counted at all: after the first entry adds ``"page"`` to
    ``basename_counts``, the guard ``if fp_stem not in basename_counts`` blocks
    the second entry from incrementing the counter.  So the final count stays
    at 1 and the set conversion (Bug 2) keeps ``"page"`` as apparently valid.
    """
    return [
        {
            "filename": "loginPage_TypeScriptReact.prompt",
            "filepath": "frontend/src/app/login/page.tsx",
            "dependencies": [],
        },
        {
            "filename": "settingsPage_TypeScriptReact.prompt",
            "filepath": "frontend/src/app/settings/page.tsx",
            "dependencies": [],
        },
    ]


# ---------------------------------------------------------------------------
# Bug 2: set(basename_counts.keys()) discards count data
# (two entries share the same filename → count is 2 but set loses it)
# ---------------------------------------------------------------------------


class TestFilterInvalidBasenamesBug2SameFilenameAmbiguous:
    """Bug 2 regression: count information is thrown away before the validity
    check, so a basename that is counted twice (two architecture entries with
    the same filename) is still accepted.

    Scenario mirrors ``pdd_cloud`` PR #1828 where both the login page and the
    settings page used ``page_TypeScriptReact.prompt`` as their filename.
    """

    def test_bare_basename_rejected_when_two_entries_share_same_filename(self):
        """Bug #1677 (Bug 2): bare ``"page"`` must be rejected as ambiguous when
        two architecture entries both declare ``filename: page_TypeScriptReact.prompt``
        (different ``filepath`` values).

        Currently ``set(basename_counts.keys())`` at agentic_sync.py:394 converts
        the Counter to a plain set, discarding the count=2 information.  The
        validity loop then tests set-membership only, so ``"page"`` (count=2)
        is treated the same as ``"page"`` (count=1) and incorrectly accepted.

        After the fix the count is consulted before accepting a basename, and
        ``"page"`` with count > 1 must land in ``invalid``.
        """
        architecture = _two_page_arch_same_filename()
        valid, invalid = _filter_invalid_basenames(["page"], architecture)

        assert "page" not in valid, (
            "Bug #1677 (Bug 2): bare 'page' incorrectly accepted as valid even though "
            "two architecture entries share the same filename 'page_TypeScriptReact.prompt'. "
            "set(basename_counts.keys()) at agentic_sync.py:394 discards the count=2, "
            "making the ambiguity invisible."
        )
        assert "page" in invalid, (
            "Bug #1677 (Bug 2): 'page' must be in invalid when it is an ambiguous basename "
            "matching multiple architecture entries."
        )

    def test_path_qualified_login_page_accepted_when_bare_page_ambiguous(self):
        """Path-qualified ``"app/login/page"`` must be accepted even when bare
        ``"page"`` is ambiguous (the directory path disambiguates).

        This verifies the fix does not regress the existing behaviour for
        path-qualified basenames accepted by the tail-match branch.
        """
        architecture = _two_page_arch_same_filename()
        valid, invalid = _filter_invalid_basenames(
            ["app/login/page", "app/settings/page"], architecture
        )

        assert "app/login/page" in valid, (
            "Path-qualified 'app/login/page' must be accepted — the path disambiguates."
        )
        assert "app/settings/page" in valid, (
            "Path-qualified 'app/settings/page' must be accepted — the path disambiguates."
        )
        assert invalid == []


# ---------------------------------------------------------------------------
# Bug 1: ``if fp_stem not in basename_counts`` prevents counting > 1
# (two entries have different filenames but share a filepath stem)
# ---------------------------------------------------------------------------


class TestFilterInvalidBasenamesBug1FilepathStemGuard:
    """Bug 1 regression: the guard ``if fp_stem not in basename_counts`` at
    agentic_sync.py:391 prevents a filepath stem from incrementing past 1.

    When two architecture entries use different filenames (e.g.
    ``loginPage_TypeScriptReact.prompt`` and ``settingsPage_TypeScriptReact.prompt``)
    but both have a ``filepath`` whose stem is ``page`` (e.g. ``page.tsx``):

    * The first entry adds ``fp_stem="page"`` to ``basename_counts`` (count=1).
    * The second entry hits ``if "page" not in basename_counts`` → False → skip.
    * ``basename_counts["page"]`` stays at 1 (never reaches 2).
    * Bug 2 then converts this to a set and accepts ``"page"`` as valid.

    Both Bug 1 and Bug 2 must be fixed for this scenario to be correctly
    rejected.
    """

    def test_bare_basename_rejected_when_two_filepath_stems_match(self):
        """Bug #1677 (Bug 1 + Bug 2): bare ``"page"`` must be rejected when two
        entries with *different* filenames share the filepath stem ``page``.

        Currently the guard ``if fp_stem not in basename_counts`` at line 391
        prevents the counter from exceeding 1, so ``"page"`` appears unambiguous
        and lands in ``valid`` instead of ``invalid``.
        """
        architecture = _two_page_arch_different_filenames()
        valid, invalid = _filter_invalid_basenames(["page"], architecture)

        assert "page" not in valid, (
            "Bug #1677 (Bug 1): bare 'page' incorrectly accepted even though two "
            "architecture entries share the same filepath stem 'page' (page.tsx). "
            "The guard 'if fp_stem not in basename_counts' at agentic_sync.py:391 "
            "prevents the counter from reaching 2, making the ambiguity invisible."
        )
        assert "page" in invalid, (
            "Bug #1677 (Bug 1): 'page' must land in invalid — it is an ambiguous stem "
            "that appears in multiple architecture filepaths."
        )

    def test_unique_filepath_stem_still_accepted(self):
        """A basename that is the filepath stem of exactly one entry must remain valid.

        This verifies the fix does not accidentally reject unambiguous basenames
        that happen to only appear in the ``filepath`` field (not in any
        ``filename`` field with a known language suffix).
        """
        architecture = [
            {
                "filename": "GitHubAppCTA.tsx",
                "filepath": "src/components/GitHubAppCTA.tsx",
                "dependencies": [],
            },
        ]
        valid, invalid = _filter_invalid_basenames(["GitHubAppCTA"], architecture)

        assert "GitHubAppCTA" in valid, (
            "Unambiguous filepath-derived stem must still be accepted after the fix."
        )
        assert invalid == []

    def test_path_qualified_page_still_accepted_when_bare_page_ambiguous(self):
        """Path-qualified basenames like ``"frontend/app/login/page"`` must be
        accepted even when the bare tail ``"page"`` would be ambiguous.

        The path itself disambiguates which module is meant.
        """
        architecture = _two_page_arch_different_filenames()
        valid, invalid = _filter_invalid_basenames(
            ["frontend/app/login/page", "frontend/app/settings/page"], architecture
        )

        assert "frontend/app/login/page" in valid, (
            "Path-qualified 'frontend/app/login/page' must be valid — path disambiguates."
        )
        assert "frontend/app/settings/page" in valid, (
            "Path-qualified 'frontend/app/settings/page' must be valid — path disambiguates."
        )
        assert invalid == []


# ---------------------------------------------------------------------------
# Bug 3: _get_filepath_from_architecture bare-basename bypass
# (the filepath cross-check only runs when "/" in basename)
# ---------------------------------------------------------------------------


class TestGetFilepathFromArchitectureBug3BareBasenameBypass:
    """Bug 3 regression: ``_get_filepath_from_architecture`` in
    sync_determine_operation.py applies a filepath cross-check at line 528 only
    when ``"/" in basename``.  For bare basenames like ``"page"`` the check is
    skipped and the first matching architecture entry is returned unconditionally,
    silently generating code at the wrong path.

    Real-world evidence: pdd_cloud PR #1828 generated ``frontend/src/page.tsx``
    (first match) instead of ``frontend/src/app/login/page.tsx`` (correct path).
    """

    def test_bare_ambiguous_basename_does_not_silently_return_first_match(
        self, tmp_path
    ):
        """Bug #1677 (Bug 3): ``_get_filepath_from_architecture`` must NOT silently
        return the first matching filepath when a bare basename like ``"page"``
        matches multiple architecture entries.

        Currently lines 492-497 iterate modules and return the first exact
        filename match without checking whether more than one entry matches —
        the ``"/" in basename`` guard at line 528 that would apply the filepath
        cross-check is never reached for bare basenames.

        After the fix, when multiple entries share the same filename and a bare
        basename is given, the function must return ``(None, None)`` to signal
        that the module cannot be resolved without path qualification.
        """
        arch_data = [
            {
                "filename": "page_TypeScriptReact.prompt",
                "filepath": "frontend/src/app/login/page.tsx",
            },
            {
                "filename": "page_TypeScriptReact.prompt",
                "filepath": "frontend/src/app/settings/page.tsx",
            },
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch_data), encoding="utf-8")

        filepath, matched_filename = _get_filepath_from_architecture(
            arch_path,
            "page_TypeScriptReact.prompt",
            basename="page",
            language="TypeScriptReact",
        )

        # Bug 3: currently returns ('frontend/src/app/login/page.tsx', ...)
        # After fix: must return (None, None) for an ambiguous bare basename
        assert filepath is None, (
            f"Bug #1677 (Bug 3): bare basename 'page' matched multiple architecture "
            f"entries but _get_filepath_from_architecture silently returned "
            f"'{filepath}' (the first match). The '/' in basename gate at "
            f"sync_determine_operation.py:528 is never reached for bare names, "
            f"so the filepath cross-check is bypassed and the wrong path wins."
        )
        assert matched_filename is None, (
            "Bug #1677 (Bug 3): matched_filename must also be None when filepath is None."
        )

    def test_path_qualified_basename_resolves_to_correct_filepath(self, tmp_path):
        """Path-qualified basename ``"app/login/page"`` must still resolve to the
        correct ``filepath`` even when multiple entries share the same filename.

        After the fix, the cross-check at line 528 (previously gated on ``"/"
        in basename``) applies and picks the entry whose filepath matches the
        requested directory prefix, returning the correct path.
        """
        arch_data = [
            {
                "filename": "page_TypeScriptReact.prompt",
                "filepath": "frontend/src/app/login/page.tsx",
            },
            {
                "filename": "page_TypeScriptReact.prompt",
                "filepath": "frontend/src/app/settings/page.tsx",
            },
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch_data), encoding="utf-8")

        filepath, _ = _get_filepath_from_architecture(
            arch_path,
            "page_TypeScriptReact.prompt",
            basename="app/login/page",
            language="TypeScriptReact",
        )

        assert filepath == "frontend/src/app/login/page.tsx", (
            f"Path-qualified 'app/login/page' must resolve to the login filepath, "
            f"got {filepath!r}."
        )

    def test_single_entry_bare_basename_still_resolves(self, tmp_path):
        """When only one entry exists for a given filename, a bare basename
        must still resolve correctly after the fix (no false ambiguity).
        """
        arch_data = [
            {
                "filename": "page_TypeScriptReact.prompt",
                "filepath": "src/app/login/page.tsx",
            },
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch_data), encoding="utf-8")

        filepath, _ = _get_filepath_from_architecture(
            arch_path,
            "page_TypeScriptReact.prompt",
            basename="page",
            language="TypeScriptReact",
        )

        # Single match → unambiguous → should resolve
        assert filepath == "src/app/login/page.tsx", (
            f"Unambiguous single-entry bare basename must resolve, got {filepath!r}."
        )


# ---------------------------------------------------------------------------
# Bug 4: AsyncSyncRunner in agentic path missing module_targets
# (caller-behavior test: verify the caller passes the correct kwarg)
# ---------------------------------------------------------------------------


class TestAgenticSyncRunnerReceivesModuleTargets:
    """Bug 4 regression: ``run_agentic_sync`` constructs ``AsyncSyncRunner``
    without the ``module_targets`` kwarg (agentic_sync.py:2279-2289).

    ``AsyncSyncRunner._build_command`` at agentic_sync_runner.py:2098 does:

        cmd.append(self.module_targets.get(basename, basename))

    When ``module_targets`` is empty (the default when not passed), the child
    sync subprocess always receives the bare ``basename`` (e.g. ``"page"``)
    instead of the canonical path-qualified form (e.g.
    ``"frontend/app/login/page"``).  This is how the wrong file
    ``frontend/src/page.tsx`` was generated in pdd_cloud PR #1828.

    Compare with the global-sync path at agentic_sync.py:1220 which correctly
    passes ``module_targets=analysis.module_targets``.
    """

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._filter_already_synced")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"page": []}, []),
    )
    @patch(
        "pdd.agentic_sync.load_prompt_template",
        return_value="template {issue_content} {architecture_json}",
    )
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_async_runner_receives_module_targets_in_agentic_path(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_load_prompt,
        mock_build_graph,
        mock_branch_diff,
        mock_dry_run,
        mock_filter_synced,
        mock_runner_cls,
    ):
        """Bug #1677 (Bug 4): ``AsyncSyncRunner`` in the agentic path must receive
        ``module_targets`` so that ``_build_command`` passes canonical path-qualified
        identifiers to child sync subprocesses.

        Currently ``module_targets`` is NOT passed to ``AsyncSyncRunner`` at
        agentic_sync.py:2279-2289, causing ``_build_command`` to fall back to
        the bare basename (e.g. ``"page"`` instead of
        ``"frontend/app/login/page"``).  This test verifies that the caller
        passes the kwarg.
        """
        issue_data = {"title": "Fix login page", "body": "Fix page.tsx", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))

        # Architecture with a module whose filepath provides a path-qualified identity
        architecture = [
            {
                "filename": "page_TypeScriptReact.prompt",
                "filepath": "frontend/src/app/login/page.tsx",
                "dependencies": [],
            }
        ]
        mock_load_arch.return_value = (architecture, Path("/tmp/architecture.json"))

        # LLM identifies the page module
        mock_agentic_task.return_value = (
            True,
            'MODULES_TO_SYNC: ["page"]\nDEPS_VALID: true',
            0.05,
            "anthropic",
        )
        mock_dry_run.return_value = (True, {"page": Path("/tmp")}, [], 0.0)
        mock_filter_synced.return_value = ["page"]

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "done", 0.10)
        mock_runner_cls.return_value = mock_runner

        run_agentic_sync(
            "https://github.com/owner/repo/issues/1677",
            quiet=True,
        )

        mock_runner_cls.assert_called()  # Runner was constructed
        runner_kwargs = mock_runner_cls.call_args.kwargs

        # Bug 4: module_targets is not passed at all in the current (buggy) code.
        # After the fix it must be present and map each basename to its canonical form.
        assert "module_targets" in runner_kwargs, (
            "Bug #1677 (Bug 4): 'module_targets' kwarg is missing from AsyncSyncRunner "
            "constructor in the agentic code path (agentic_sync.py:2279-2289). "
            "Without it, _build_command falls back to the bare basename and the "
            "child sync subprocess receives 'page' instead of the canonical "
            "'frontend/app/login/page', generating code at the wrong path."
        )

        module_targets = runner_kwargs["module_targets"]
        # module_targets must not be empty when the architecture provided a filepath
        assert module_targets, (
            "Bug #1677 (Bug 4): module_targets must be non-empty when architecture "
            "data contains filepath information for the synced modules."
        )


# ---------------------------------------------------------------------------
# Integration test: pdd_cloud PR #1828 fixture
# (wrong path 'frontend/src/page.tsx' must not be generated)
# ---------------------------------------------------------------------------


class TestPddCloudPr1828Fixture:
    """End-to-end regression fixture modelling the exact architecture data from
    pdd_cloud PR #1828 (2026-05-29) that produced the wrong path.

    Root entry in architecture.json:
      prompt:   frontend/app/login/page_TypeScriptReact.prompt
      filepath: frontend/src/app/login/page.tsx

    Frontend nested entry used a bare filename:
      filename: page_TypeScriptReact.prompt
      filepath: src/app/login/page.tsx

    ``pdd sync`` then generated the wrong path ``frontend/src/page.tsx``
    instead of ``frontend/src/app/login/page.tsx``.

    The combined fixture below verifies that the central module identity
    resolver correctly rejects bare ``"page"`` as ambiguous when multiple
    modules share that short basename.
    """

    def test_ambiguous_bare_page_rejected_not_silently_resolved(self):
        """Bug #1677 integration: bare ``"page"`` must be rejected (or raise an
        error) when the combined architecture contains multiple modules whose
        filepath stem is ``page``.

        This directly models the pdd_cloud situation where an agentic sync job
        passed the bare ``"page"`` basename into a child sync job, which then
        silently wrote ``frontend/src/page.tsx`` instead of the correct path.
        """
        # Mirrors the combined architecture seen by pdd sync in the cloud run
        architecture = [
            # Root-level entry (from main architecture.json)
            {
                "filename": "page_TypeScriptReact.prompt",
                "filepath": "frontend/src/app/login/page.tsx",
                "dependencies": [],
            },
            # Settings page entry — same short basename, different path
            {
                "filename": "page_TypeScriptReact.prompt",
                "filepath": "frontend/src/app/settings/page.tsx",
                "dependencies": [],
            },
            # Other modules that should be unaffected
            {
                "filename": "layout_TypeScriptReact.prompt",
                "filepath": "frontend/src/app/layout.tsx",
                "dependencies": [],
            },
        ]

        # Bare "page" must NOT pass the filter as if it were unambiguous
        valid, invalid = _filter_invalid_basenames(["page"], architecture)
        assert "page" not in valid, (
            "Bug #1677: bare 'page' passed _filter_invalid_basenames as valid even "
            "though two architecture entries share that short basename. This is the "
            "root cause of pdd_cloud PR #1828 generating 'frontend/src/page.tsx' "
            "instead of 'frontend/src/app/login/page.tsx'."
        )
        assert "page" in invalid

        # Path-qualified form must still resolve correctly
        valid, invalid = _filter_invalid_basenames(
            ["frontend/app/login/page", "layout"], architecture
        )
        assert "frontend/app/login/page" in valid, (
            "Path-qualified 'frontend/app/login/page' must be accepted."
        )
        assert "layout" in valid, "Unambiguous 'layout' module must be accepted."
        assert invalid == []
