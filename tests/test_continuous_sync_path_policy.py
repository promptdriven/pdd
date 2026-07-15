"""Path-policy regressions for legacy continuous-sync metadata repair."""

from pathlib import Path
from typing import Dict, Any

import pytest

from pdd import continuous_sync


def test_artifact_path_violation_rejects_resolved_project_escape(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    root.mkdir()
    outside = tmp_path / "outside.py"
    outside.write_text("def value():\n    return 1\n", encoding="utf-8")

    assert (
        continuous_sync._artifact_path_violation(root / "../outside.py", root)
        == "resolves outside project"
    )


def test_repair_search_skips_symlink_candidate_without_hashing(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = tmp_path / "repo"
    root.mkdir()
    archive = root / "archive"
    archive.mkdir()
    outside = tmp_path / "widget.py"
    outside.write_text("def value():\n    return 1\n", encoding="utf-8")
    try:
        (archive / "widget.py").symlink_to(outside)
    except OSError as exc:  # pragma: no cover - platform permission guard
        pytest.skip(f"symlink creation unavailable: {exc}")

    def fail_if_hashed(path: Path) -> str:
        raise AssertionError(f"unexpected hash read: {path}")

    monkeypatch.setattr(continuous_sync, "calculate_sha256", fail_if_hashed)

    match, failure = continuous_sync._find_matching_artifact(root, "widget.py", "unused")
    assert match is None
    assert failure is None


# ---------------------------------------------------------------------------
# Issue #2082: _prompt_ownership alphabetical tiebreak bug
# ---------------------------------------------------------------------------
# When multiple .pddrc contexts share the same resolved prompts_dir (because
# all default to "prompts/" which symlinks to "pdd/prompts/"), _prompt_ownership
# builds an `owned` list where all entries have the same depth score.  Python's
# max() then breaks ties alphabetically on context_name: "utils" > "pdd_cli"
# lexicographically, so provider_manager and cli_theme are silently assigned the
# wrong context.  The fix must use each context's `paths` patterns to
# disambiguate, falling back to context_name=None (UNBASELINED) when ambiguous.
# ---------------------------------------------------------------------------


def _write_pddrc(base: Path, content: str) -> None:
    """Write a .pddrc YAML config as a regular file at base/.pddrc."""
    (base / ".pddrc").write_text(content, encoding="utf-8")


def test_prompt_ownership_selects_paths_pattern_over_alphabetical_tiebreak(
    tmp_path: Path,
) -> None:
    """Bug #2082: _prompt_ownership must use paths patterns to break depth ties.

    Both 'utils' and 'pdd_cli' share prompts_dir='pdd/prompts', producing equal
    depth scores in the owned list.  The current max() tiebreak picks 'utils'
    because 'utils' > 'pdd_cli' alphabetically, even though only the 'pdd/**'
    pattern (pdd_cli) matches the prompt path.  The fix must select 'pdd_cli'.
    """
    base = tmp_path / "repo"
    (base / "pdd" / "prompts").mkdir(parents=True)
    (base / "pdd" / "prompts" / "provider_manager_python.prompt").write_text(
        "# provider manager prompt\n", encoding="utf-8"
    )
    _write_pddrc(
        base,
        "contexts:\n"
        "  utils:\n"
        "    paths: [\"utils/**\"]\n"
        "    defaults:\n"
        "      prompts_dir: \"pdd/prompts\"\n"
        "      generate_output_path: \"utils/\"\n"
        "      test_output_path: \"tests/utils/\"\n"
        "  pdd_cli:\n"
        "    paths: [\"pdd/**\"]\n"
        "    defaults:\n"
        "      prompts_dir: \"pdd/prompts\"\n"
        "      generate_output_path: \"pdd\"\n"
        "      test_output_path: \"tests\"\n",
    )

    prompt_path = base / "pdd" / "prompts" / "provider_manager_python.prompt"
    _basename, context_name, _pddrc, _root = continuous_sync._prompt_ownership(
        prompt_path, "provider_manager", base / "pdd" / "prompts", base
    )

    # Bug: max(owned) picks "utils" (alphabetically largest) even though
    # "utils/**" does NOT match the relative path "pdd/prompts/provider_manager_python.prompt".
    # Fix: paths-pattern filtering selects "pdd_cli" (pattern "pdd/**" matches).
    assert context_name == "pdd_cli", (
        f"expected 'pdd_cli' (paths-pattern match) but got {context_name!r}; "
        "alphabetical tiebreak bug is present — 'utils' must not win over 'pdd_cli'"
    )


def test_prompt_ownership_returns_none_when_no_paths_pattern_matches_prompt(
    tmp_path: Path,
) -> None:
    """Bug #2082: when tied contexts have no matching paths pattern, return None.

    If 'utils' (paths: ["utils/**"]) and 'backend' (paths: ["backend/**"]) both
    share the same prompts_dir depth but neither pattern covers a prompt under
    pdd/prompts/, the function must return context_name=None rather than guessing
    the alphabetically-largest context name ("utils" > "backend").
    """
    base = tmp_path / "repo"
    (base / "pdd" / "prompts").mkdir(parents=True)
    (base / "pdd" / "prompts" / "orphan_python.prompt").write_text(
        "# orphan prompt\n", encoding="utf-8"
    )
    _write_pddrc(
        base,
        "contexts:\n"
        "  utils:\n"
        "    paths: [\"utils/**\"]\n"
        "    defaults:\n"
        "      prompts_dir: \"pdd/prompts\"\n"
        "  backend:\n"
        "    paths: [\"backend/**\"]\n"
        "    defaults:\n"
        "      prompts_dir: \"pdd/prompts\"\n",
    )

    prompt_path = base / "pdd" / "prompts" / "orphan_python.prompt"
    _basename, context_name, _pddrc, _root = continuous_sync._prompt_ownership(
        prompt_path, "orphan", base / "pdd" / "prompts", base
    )

    # Bug: max(owned) picks "utils" ("utils" > "backend" alphabetically).
    # Fix: neither "utils/**" nor "backend/**" matches → return None so callers
    # surface an explicit UNBASELINED failure rather than a fabricated context.
    assert context_name is None, (
        f"expected None (no paths pattern matches) but got {context_name!r}; "
        "context must not be guessed when no pattern covers the prompt path"
    )


def test_prompt_units_propagates_correct_context_via_shared_symlink(
    tmp_path: Path,
) -> None:
    """Bug #2082: _prompt_units must assign pdd_cli not utils when prompts→pdd/prompts symlink ties.

    In the real repo prompts/ is a symlink to pdd/prompts/.  All contexts that
    default to prompts_dir='prompts' (both 'utils' and 'pdd_cli') resolve to the
    same physical path, creating an equal-depth tie in _prompt_ownership.  The
    alphabetical tiebreak picks "utils" for cli_theme.  The fix must assign "pdd_cli"
    using the paths pattern "pdd/**", which covers "pdd/prompts/cli_theme_python.prompt".
    """
    base = tmp_path / "repo"
    (base / "pdd" / "prompts").mkdir(parents=True)
    (base / "pdd" / "prompts" / "cli_theme_python.prompt").write_text(
        "# cli theme prompt\n", encoding="utf-8"
    )
    try:
        (base / "prompts").symlink_to(base / "pdd" / "prompts")
    except OSError as exc:  # pragma: no cover - platform permission guard
        pytest.skip(f"symlink creation unavailable: {exc}")

    # Both contexts use the default prompts_dir ("prompts"), which resolves via
    # the symlink to the same physical directory as "pdd/prompts".
    _write_pddrc(
        base,
        "contexts:\n"
        "  utils:\n"
        "    paths: [\"utils/**\"]\n"
        "    defaults:\n"
        "      generate_output_path: \"utils/\"\n"
        "      test_output_path: \"tests/utils/\"\n"
        "  pdd_cli:\n"
        "    paths: [\"pdd/**\"]\n"
        "    defaults:\n"
        "      generate_output_path: \"pdd\"\n"
        "      test_output_path: \"tests\"\n",
    )

    prompt_root = base / "pdd" / "prompts"
    budget: Dict[str, int] = {"entries": 0, "files": 0}
    config_cache: Dict[Path, Any] = {}
    units, failures = continuous_sync._prompt_units(
        prompt_root, budget, [prompt_root], base, config_cache
    )

    assert not failures, f"unexpected discovery failures: {failures}"
    cli_theme_units = [u for u in units if "cli_theme" in u.basename]
    assert cli_theme_units, "cli_theme unit was not discovered by _prompt_units"

    # Bug: symlink makes both contexts resolve to the same depth; max() picks
    # "utils" (alphabetically largest).  Fix: "pdd/**" matches the relative
    # path "pdd/prompts/cli_theme_python.prompt" → "pdd_cli" wins.
    assert cli_theme_units[0].context_name == "pdd_cli", (
        f"expected context_name='pdd_cli' but got {cli_theme_units[0].context_name!r}; "
        "symlink-induced tie must be broken with paths-pattern matching, not alphabetical order"
    )


def test_configured_output_defaults_secondary_ownership_call_uses_paths_patterns(
    tmp_path: Path,
) -> None:
    """Bug #2082: secondary _prompt_ownership call in _configured_output_defaults must use paths.

    When SyncUnit.context_name is None and _detect_context_from_basename returns None
    (no basename-level match), _configured_output_defaults calls _prompt_ownership a
    second time.  That secondary call has the same alphabetical-tiebreak bug.  The fix
    must apply paths-pattern disambiguation in both call sites.
    """
    base = tmp_path / "repo"
    # Create the shared prompts dir but NO orphan_*.prompt file, so the
    # _detect_context_from_basename filesystem glob finds nothing and returns None,
    # which triggers the secondary _prompt_ownership call path.
    (base / "pdd" / "prompts").mkdir(parents=True)
    _write_pddrc(
        base,
        "contexts:\n"
        "  utils:\n"
        "    paths: [\"utils/**\"]\n"
        "    defaults:\n"
        "      prompts_dir: \"pdd/prompts\"\n"
        "      generate_output_path: \"utils/\"\n"
        "      test_output_path: \"tests/utils/\"\n"
        "  pdd_cli:\n"
        "    paths: [\"pdd/**\"]\n"
        "    defaults:\n"
        "      prompts_dir: \"pdd/prompts\"\n"
        "      generate_output_path: \"pdd\"\n"
        "      test_output_path: \"tests\"\n",
    )

    # prompt_path is a logical path — the file need not exist for the ownership
    # check (_is_within_root is purely path-arithmetic, not filesystem access).
    prompt_path = base / "pdd" / "prompts" / "orphan_python.prompt"
    unit = continuous_sync.SyncUnit(
        basename="orphan",
        language="python",
        prompt_path=prompt_path,
        prompts_dir=base / "pdd" / "prompts",
        context_name=None,   # triggers secondary lookup in _configured_output_defaults
        pddrc_path=None,
    )

    _defaults, context_name, _pddrc_path, _config = continuous_sync._configured_output_defaults(
        unit, base
    )

    # Bug: secondary _prompt_ownership call returns "utils" (alphabetical tiebreak).
    # Fix: paths pattern "pdd/**" matches the prompt path → "pdd_cli" is returned.
    assert context_name == "pdd_cli", (
        f"expected 'pdd_cli' from secondary _prompt_ownership but got {context_name!r}; "
        "the secondary call site must also use paths-pattern disambiguation"
    )


def test_resolve_report_paths_returns_pdd_code_path_not_utils_for_unregistered_module(
    tmp_path: Path,
) -> None:
    """Bug #2082: end-to-end regression — provider_manager code path must be pdd/ not utils/.

    This reproduces the exact symptom from the issue: 'pdd reconcile --module
    provider_manager --json' reported utils/provider_manager.py instead of
    pdd/provider_manager.py because the wrong context was picked.  No architecture.json
    entry exists for provider_manager, so _architecture_filepath returns None and
    cannot mask the wrong context assignment.
    """
    base = tmp_path / "repo"
    # Prompts dir exists but no provider_manager_*.prompt file — the filesystem
    # glob in _detect_context_from_basename finds nothing → triggers secondary
    # _prompt_ownership call that historically returned the wrong "utils" context.
    (base / "pdd" / "prompts").mkdir(parents=True)
    _write_pddrc(
        base,
        "contexts:\n"
        "  utils:\n"
        "    paths: [\"utils/**\"]\n"
        "    defaults:\n"
        "      prompts_dir: \"pdd/prompts\"\n"
        "      generate_output_path: \"utils/\"\n"
        "      test_output_path: \"tests/utils/\"\n"
        "      example_output_path: \"utils/examples/\"\n"
        "      default_language: \"python\"\n"
        "  pdd_cli:\n"
        "    paths: [\"pdd/**\"]\n"
        "    defaults:\n"
        "      prompts_dir: \"pdd/prompts\"\n"
        "      generate_output_path: \"pdd\"\n"
        "      test_output_path: \"tests\"\n"
        "      example_output_path: \"context\"\n"
        "      default_language: \"python\"\n",
    )
    # No architecture.json → _architecture_filepath returns None → cannot override paths

    prompt_path = base / "pdd" / "prompts" / "provider_manager_python.prompt"
    unit = continuous_sync.SyncUnit(
        basename="provider_manager",
        language="python",
        prompt_path=prompt_path,
        prompts_dir=base / "pdd" / "prompts",
        context_name=None,
        pddrc_path=None,
    )

    paths = continuous_sync._resolve_report_paths(unit, base)

    code_path = paths.get("code")
    assert code_path is not None, "_resolve_report_paths did not return a 'code' entry"
    code_str = str(code_path)

    # Bug: wrong context "utils" → code_path = <base>/utils/provider_manager.py
    # Fix: correct context "pdd_cli" → code_path = <base>/pdd/provider_manager.py
    assert "utils" not in code_str.split("/"), (
        f"code path {code_str!r} was placed under 'utils/' — "
        "provider_manager belongs to pdd/ (pdd_cli context), not utils/"
    )
    assert str(base / "pdd") in code_str, (
        f"code path {code_str!r} does not point inside pdd/ — "
        "expected code under pdd/ for the pdd_cli context"
    )


def test_prompt_ownership_uses_pattern_specificity_over_alphabetical_for_multiple_matches(
    tmp_path: Path,
) -> None:
    """Bug #2082: when multiple patterns match, the most-specific (longest) prefix wins.

    With contexts 'z_generic' (paths: ["pdd/**"]) and 'a_specific'
    (paths: ["pdd/prompts/**"]), both patterns cover the prompt.  The fix must
    select 'a_specific' because its prefix "pdd/prompts" (len 11) is longer than
    "pdd" (len 3), regardless of alphabetical ordering.  The current bug selects
    'z_generic' because "z_generic" > "a_specific" lexicographically.
    """
    base = tmp_path / "repo"
    (base / "pdd" / "prompts").mkdir(parents=True)
    (base / "pdd" / "prompts" / "provider_manager_python.prompt").write_text(
        "# provider manager prompt\n", encoding="utf-8"
    )
    _write_pddrc(
        base,
        "contexts:\n"
        "  z_generic:\n"
        "    paths: [\"pdd/**\"]\n"
        "    defaults:\n"
        "      prompts_dir: \"pdd/prompts\"\n"
        "      generate_output_path: \"pdd\"\n"
        "  a_specific:\n"
        "    paths: [\"pdd/prompts/**\"]\n"
        "    defaults:\n"
        "      prompts_dir: \"pdd/prompts\"\n"
        "      generate_output_path: \"pdd/prompts\"\n",
    )

    prompt_path = base / "pdd" / "prompts" / "provider_manager_python.prompt"
    _basename, context_name, _pddrc, _root = continuous_sync._prompt_ownership(
        prompt_path, "provider_manager", base / "pdd" / "prompts", base
    )

    # Bug: "z_generic" > "a_specific" alphabetically → max(owned) picks "z_generic"
    # even though "pdd/prompts/**" is a more specific match for this prompt.
    # Fix: longest-prefix pattern wins → "a_specific" (prefix "pdd/prompts", len 11)
    # beats "z_generic" (prefix "pdd", len 3).
    assert context_name == "a_specific", (
        f"expected 'a_specific' (longer/more-specific pattern) but got {context_name!r}; "
        "pattern specificity must take precedence over alphabetical context-name ordering"
    )
