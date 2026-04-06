# tests/test_issue_1049_reproduction.py
#
# Tests for GitHub Issue #1049:
# "pdd sync can't resolve prompts in extension prompt directories"
#
# The bug: prefix extraction in _relative_basename_for_context() and
# _detect_context_from_basename() uses `normalized.startswith('prompts/')`
# which fails for extension paths like "extensions/github_pdd_app/prompts/frontend"
# where "prompts/" appears in the middle of the path, not at the start.
# This causes double-prefix template expansions (e.g., "frontend/frontend/...")
# that never match actual files on disk.
#
# 8 reproduction tests from Step 5 + 3 new fix-detection tests = 11 total.

import os
import textwrap
from pathlib import Path
from typing import Generator
from unittest.mock import patch

import pytest

from pdd.sync_main import (
    _find_prompt_in_contexts,
    _detect_languages_with_context,
    _normalize_prompts_root,
    _relative_basename_for_context as sync_main_relative_basename,
)
from pdd.construct_paths import (
    _detect_context_from_basename,
    _load_pddrc_config,
    _find_pddrc_file,
)
from pdd.template_expander import expand_template


@pytest.fixture
def extension_project(tmp_path: Path) -> Generator[Path, None, None]:
    """
    Creates a project with both primary and extension prompt directories,
    mimicking the structure described in issue #1049.

    Primary tree:
        prompts/frontend/app/jobs/page_TypeScriptReact.prompt
    Extension tree:
        extensions/github_pdd_app/prompts/frontend/src/app/jobs/page_TypeScriptReact.prompt

    The .pddrc defines a frontend context with prompts_dir=prompts/frontend
    and an extension context (github_pdd_app) with
    prompts_dir=extensions/github_pdd_app/prompts/frontend.
    """
    original_cwd = Path.cwd()
    project_root = tmp_path / "test_extension_project"
    project_root.mkdir()

    # Primary prompt tree
    primary_prompts = project_root / "prompts" / "frontend" / "app" / "jobs"
    primary_prompts.mkdir(parents=True)
    (primary_prompts / "page_TypeScriptReact.prompt").write_text(
        "Primary prompt for page component"
    )

    # Extension prompt tree (note the extra src/ segment)
    ext_prompts = (
        project_root
        / "extensions"
        / "github_pdd_app"
        / "prompts"
        / "frontend"
        / "src"
        / "app"
        / "jobs"
    )
    ext_prompts.mkdir(parents=True)
    (ext_prompts / "page_TypeScriptReact.prompt").write_text(
        "Extension prompt for page component"
    )

    # Create .pddrc with both primary and extension contexts
    pddrc_content = textwrap.dedent("""\
        version: "1.0"

        contexts:
          frontend:
            paths: ["frontend/**"]
            defaults:
              generate_output_path: "frontend/src/"
              test_output_path: "frontend/__tests__/"
              prompts_dir: "prompts/frontend"
              default_language: "typescriptreact"
              outputs:
                prompt:
                  path: "prompts/frontend/{dir_prefix}{name}_{language}.prompt"

          github_pdd_app:
            paths: ["extensions/github_pdd_app/**"]
            defaults:
              generate_output_path: "extensions/github_pdd_app/src/"
              test_output_path: "extensions/github_pdd_app/tests/"
              prompts_dir: "extensions/github_pdd_app/prompts/frontend"
              default_language: "typescriptreact"
              outputs:
                prompt:
                  path: "extensions/github_pdd_app/prompts/frontend/{dir_prefix}{name}_{language}.prompt"

          default:
            defaults:
              generate_output_path: "./"
              test_output_path: "tests/"
              default_language: "python"
    """)
    (project_root / ".pddrc").write_text(pddrc_content)

    # Standard dirs
    (project_root / "src").mkdir(exist_ok=True)
    (project_root / "tests").mkdir(exist_ok=True)

    os.chdir(project_root)
    yield project_root
    os.chdir(original_cwd)


@pytest.fixture
def extension_project_no_context(tmp_path: Path) -> Generator[Path, None, None]:
    """
    Creates a project where the extension prompt directory is NOT registered
    as a context in .pddrc (Possibility A from the issue).
    """
    original_cwd = Path.cwd()
    project_root = tmp_path / "test_ext_no_context"
    project_root.mkdir()

    # Primary prompt tree
    primary_prompts = project_root / "prompts" / "frontend" / "app" / "jobs"
    primary_prompts.mkdir(parents=True)
    (primary_prompts / "page_TypeScriptReact.prompt").write_text(
        "Primary prompt for page component"
    )

    # Extension prompt tree (exists on disk but NOT in .pddrc)
    ext_prompts = (
        project_root
        / "extensions"
        / "github_pdd_app"
        / "prompts"
        / "frontend"
        / "src"
        / "app"
        / "jobs"
    )
    ext_prompts.mkdir(parents=True)
    (ext_prompts / "page_TypeScriptReact.prompt").write_text(
        "Extension prompt for page component"
    )

    # .pddrc only has the primary frontend context — no extension context
    pddrc_content = textwrap.dedent("""\
        version: "1.0"

        contexts:
          frontend:
            paths: ["frontend/**"]
            defaults:
              generate_output_path: "frontend/src/"
              test_output_path: "frontend/__tests__/"
              prompts_dir: "prompts/frontend"
              default_language: "typescriptreact"
              outputs:
                prompt:
                  path: "prompts/frontend/{dir_prefix}{name}_{language}.prompt"

          default:
            defaults:
              generate_output_path: "./"
              test_output_path: "tests/"
              default_language: "python"
    """)
    (project_root / ".pddrc").write_text(pddrc_content)

    os.chdir(project_root)
    yield project_root
    os.chdir(original_cwd)


# =============================================================================
# Reproduction tests from Step 5 — prove the bug exists on current code.
# After the bug is fixed, these should PASS as permanent regression tests.
# =============================================================================


class TestIssue1049ExtensionPromptResolution:
    """Tests for issue #1049: pdd sync fails to find prompts in extension
    prompt directories."""

    # --- Reproduction test from Step 5 ---
    def test_find_prompt_in_extension_context(self, extension_project: Path) -> None:
        """_find_prompt_in_contexts should find the prompt file in the extension
        context (github_pdd_app) when given basename 'src/app/jobs/page'."""
        result = _find_prompt_in_contexts("src/app/jobs/page")
        assert result is not None, (
            "Expected _find_prompt_in_contexts to find the extension prompt file "
            "at extensions/github_pdd_app/prompts/frontend/src/app/jobs/page_TypeScriptReact.prompt "
            "but got None. This is the core of issue #1049."
        )
        context_name, prompt_path, language = result
        assert context_name == "github_pdd_app"
        assert prompt_path.exists()
        assert "extensions/github_pdd_app" in str(prompt_path)

    # --- Reproduction test from Step 5 ---
    def test_find_prompt_in_primary_context(self, extension_project: Path) -> None:
        """_find_prompt_in_contexts should still find prompts in the primary tree
        when given basename 'app/jobs/page'."""
        result = _find_prompt_in_contexts("app/jobs/page")
        assert result is not None, (
            "Expected _find_prompt_in_contexts to find the primary prompt file "
            "at prompts/frontend/app/jobs/page_TypeScriptReact.prompt"
        )
        context_name, prompt_path, language = result
        assert context_name == "frontend"
        assert prompt_path.exists()
        assert "prompts/frontend/app/jobs" in str(prompt_path)

    # --- Reproduction test from Step 5 ---
    def test_detect_languages_in_extension_dir(self, extension_project: Path) -> None:
        """_detect_languages_with_context should find TypeScriptReact prompt
        in the extension prompts directory."""
        ext_prompts_dir = (
            extension_project
            / "extensions"
            / "github_pdd_app"
            / "prompts"
            / "frontend"
        )
        lang_to_path = _detect_languages_with_context(
            "src/app/jobs/page",
            ext_prompts_dir,
            context_name="github_pdd_app",
        )
        assert lang_to_path, (
            "Expected to find TypeScriptReact prompt in extension directory "
            f"{ext_prompts_dir} for basename 'src/app/jobs/page', but got empty dict. "
            "This is the path resolution failure described in issue #1049."
        )
        assert "typescriptreact" in lang_to_path

    # --- Reproduction test from Step 5 ---
    def test_detect_context_from_basename_matches_extension(
        self, extension_project: Path
    ) -> None:
        """_detect_context_from_basename should be able to match a basename
        that includes the src/ prefix to the extension context."""
        pddrc_path = _find_pddrc_file()
        assert pddrc_path is not None
        config = _load_pddrc_config(pddrc_path)

        context = _detect_context_from_basename(
            "frontend/src/app/jobs/page", config
        )
        assert context is not None, (
            "Expected _detect_context_from_basename to match "
            "'frontend/src/app/jobs/page' to a context, but got None"
        )

    # --- Reproduction test from Step 5 ---
    def test_full_basename_resolves_to_extension_prompt(
        self, extension_project: Path
    ) -> None:
        """End-to-end test: 'pdd sync frontend/src/app/jobs/page' should find
        the prompt file in the extension tree."""
        result = _find_prompt_in_contexts("frontend/src/app/jobs/page")
        if result is not None:
            context_name, prompt_path, language = result
            assert prompt_path.exists(), (
                f"Template discovery returned path {prompt_path} but it doesn't exist"
            )
            assert "extensions" in str(prompt_path) or "src/app/jobs" in str(prompt_path), (
                f"Expected prompt path to be in extension tree, got: {prompt_path}"
            )
            return

        pytest.fail(
            "Neither _find_prompt_in_contexts nor fallback could resolve "
            "'frontend/src/app/jobs/page' to a prompt file. "
            "This confirms issue #1049: extension prompt directories are not searchable."
        )


class TestIssue1049ConfigGap:
    """Tests for Possibility A: extension prompt directory not registered in .pddrc."""

    # --- Reproduction test from Step 5 ---
    def test_unregistered_extension_dir_not_searched(
        self, extension_project_no_context: Path
    ) -> None:
        """When the extension directory is NOT registered as a context in .pddrc,
        _find_prompt_in_contexts should not find extension prompts."""
        result = _find_prompt_in_contexts("src/app/jobs/page")
        assert result is None, (
            "Unexpectedly found a prompt for 'src/app/jobs/page' even though "
            "the extension directory is not registered in .pddrc. "
            "If this assertion fails, the config gap theory is disproven."
        )

    # --- Reproduction test from Step 5 ---
    def test_registered_extension_dir_is_searched(
        self, extension_project: Path
    ) -> None:
        """When the extension directory IS registered as a context in .pddrc,
        _find_prompt_in_contexts SHOULD find extension prompts."""
        result = _find_prompt_in_contexts("src/app/jobs/page")
        assert result is not None, (
            "Even with extension context registered in .pddrc, "
            "_find_prompt_in_contexts failed to find 'src/app/jobs/page'. "
            "This suggests Possibility B (path prefix mismatch) is also in play."
        )


class TestIssue1049PathPrefixMismatch:
    """Tests for Possibility B: src/ prefix mismatch between primary and extension trees."""

    # --- Reproduction test from Step 5 ---
    def test_basename_with_src_prefix_resolves_in_extension(
        self, extension_project: Path
    ) -> None:
        """Template expansion for the github_pdd_app context should produce the
        correct extension path when basename is 'src/app/jobs/page'."""
        pddrc_path = _find_pddrc_file()
        assert pddrc_path is not None
        config = _load_pddrc_config(pddrc_path)

        ext_context_config = config["contexts"]["github_pdd_app"]
        relative = sync_main_relative_basename(
            "src/app/jobs/page", ext_context_config
        )
        assert "page" in relative, (
            f"Expected relative basename to contain 'page', got: {relative}"
        )

        template = ext_context_config["defaults"]["outputs"]["prompt"]["path"]
        parts = relative.split("/") if relative else [""]
        name_part = parts[-1]
        category = "/".join(parts[:-1]) if len(parts) > 1 else ""
        dir_prefix = f"{category}/" if category else ""

        expanded = expand_template(template, {
            "name": name_part,
            "category": category,
            "dir_prefix": dir_prefix,
            "ext": ".tsx",
            "language": "TypeScriptReact",
        })

        expected_path = (
            "extensions/github_pdd_app/prompts/frontend/"
            "src/app/jobs/page_TypeScriptReact.prompt"
        )
        assert expanded == expected_path, (
            f"Template expansion produced '{expanded}' but expected '{expected_path}'. "
            "The src/ prefix is being lost or incorrectly stripped during "
            "relative basename computation."
        )


# =============================================================================
# New fix-detection tests — these MUST FAIL on the current buggy code.
# They verify the fix for the prefix extraction pattern that only handles
# prompts_dir values starting with "prompts/" but fails for extension paths
# where "prompts/" appears deeper (e.g., "extensions/.../prompts/frontend").
# =============================================================================


class TestIssue1049FixDetection:
    """Tests that specifically detect the prefix extraction bug in issue #1049.

    The bug: when prompts_dir="extensions/github_pdd_app/prompts/frontend",
    the code checks `normalized.startswith('prompts/')` which is False,
    so the prefix stays as the full path instead of extracting "frontend"
    (the part after "prompts/"). This causes:
    - _relative_basename_for_context to not strip the "frontend/" prefix
    - Template expansion to produce doubled paths like "frontend/frontend/..."
    - _find_prompt_in_contexts to miss the extension prompt file
    """

    def test_relative_basename_strips_frontend_for_extension_context(
        self, extension_project: Path
    ) -> None:
        """_relative_basename_for_context (sync_main) should strip 'frontend/'
        from basename when the extension context's prompts_dir contains
        'prompts/frontend' in the middle of the path.

        On buggy code: returns "frontend/src/app/jobs/page" unchanged because
        the prefix extraction fails (startswith('prompts/') is False for
        "extensions/github_pdd_app/prompts/frontend").
        After fix: returns "src/app/jobs/page" (stripped of "frontend/" prefix).
        """
        pddrc_path = _find_pddrc_file()
        assert pddrc_path is not None
        config = _load_pddrc_config(pddrc_path)
        ext_config = config["contexts"]["github_pdd_app"]

        result = sync_main_relative_basename(
            "frontend/src/app/jobs/page", ext_config
        )
        # The fix should extract "frontend" as the prefix from
        # "extensions/github_pdd_app/prompts/frontend" by finding "prompts/"
        # anywhere in the path (not just at the start), then strip "frontend/"
        # from the basename.
        assert not result.startswith("frontend/"), (
            f"Expected 'frontend/' to be stripped from basename for extension context, "
            f"but got: '{result}'. The extension context's prompts_dir is "
            "'extensions/github_pdd_app/prompts/frontend' — the prefix 'frontend' "
            "should be extracted from after 'prompts/' and stripped from the basename."
        )

    def test_template_expansion_no_double_frontend_prefix(
        self, extension_project: Path
    ) -> None:
        """Template expansion for extension context must NOT produce doubled
        'frontend/frontend/' paths.

        This is the observable symptom of the bug: _relative_basename_for_context
        returns the basename with "frontend/" still attached, and the template
        already contains "prompts/frontend/", so expansion produces
        "extensions/.../prompts/frontend/frontend/src/..." — a path that
        doesn't exist on disk.
        """
        pddrc_path = _find_pddrc_file()
        assert pddrc_path is not None
        config = _load_pddrc_config(pddrc_path)
        ext_config = config["contexts"]["github_pdd_app"]

        # Step 1: Get the relative basename (buggy code doesn't strip "frontend/")
        relative = sync_main_relative_basename(
            "frontend/src/app/jobs/page", ext_config
        )

        # Step 2: Expand template the same way _find_prompt_in_contexts does
        parts = relative.split("/") if relative else [""]
        name_part = parts[-1]
        category = "/".join(parts[:-1]) if len(parts) > 1 else ""
        dir_prefix = f"{category}/" if category else ""

        template = ext_config["defaults"]["outputs"]["prompt"]["path"]
        expanded = expand_template(template, {
            "name": name_part,
            "category": category,
            "dir_prefix": dir_prefix,
            "ext": ".tsx",
            "language": "TypeScriptReact",
        })

        # The expanded path should NOT contain doubled "frontend/frontend/"
        assert "frontend/frontend/" not in expanded, (
            f"Template expansion produced doubled 'frontend/' prefix: '{expanded}'. "
            "This is the root cause of issue #1049 — the prefix extraction pattern "
            "fails for extension paths where 'prompts/' is not at the start."
        )

    def test_agentic_sync_is_catchall_match_recognizes_extension_prompts_dir(
        self, extension_project: Path
    ) -> None:
        """agentic_sync._is_catchall_match should recognize that a basename
        matches the extension context's prompts_dir prefix, even when
        prompts_dir has 'prompts/' in the middle of the path.

        On buggy code: _is_catchall_match has the same startswith('prompts/')
        bug at line 328. For prompts_dir="extensions/github_pdd_app/prompts/frontend",
        it fails to extract prefix "frontend", so the prompts_dir matching
        branch never triggers. We test this with a config where NO path patterns
        can match the basename, so the ONLY way to get a non-catchall match
        is through the prompts_dir prefix extraction.

        After fix: the prefix "frontend" is correctly extracted from the
        extension prompts_dir, so "frontend/src/app/jobs/page" is recognized
        as belonging to the github_pdd_app context (not a catch-all match).
        """
        from pdd.agentic_sync import _is_catchall_match

        # Build a config where the extension context has NO path patterns,
        # so prompts_dir is the ONLY way to match. This isolates the bug.
        config = {
            "contexts": {
                "github_pdd_app": {
                    "paths": [],  # No path patterns — prompts_dir is the only match source
                    "defaults": {
                        "prompts_dir": "extensions/github_pdd_app/prompts/frontend",
                    },
                },
                "default": {
                    "defaults": {},
                },
            }
        }

        # "frontend/src/app/jobs/page" should match via prompts_dir prefix "frontend"
        # (extracted from "extensions/github_pdd_app/prompts/frontend").
        # _is_catchall_match returns False when a specific (non-catchall) match exists.
        result = _is_catchall_match("frontend/src/app/jobs/page", config)
        assert result is False, (
            "Expected _is_catchall_match to return False for 'frontend/src/app/jobs/page' "
            "because it should match the github_pdd_app context's prompts_dir prefix "
            "'frontend' (extracted from 'extensions/github_pdd_app/prompts/frontend'). "
            "Got True, meaning the prompts_dir prefix extraction failed — the same "
            "startswith('prompts/') bug as the other fix locations."
        )
