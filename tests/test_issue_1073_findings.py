"""Regression tests for the three review findings raised against PR #1073.

Each finding pairs a negative case (the bug being fixed — should produce drift
or honor the override) with a positive case (matching configurations still
pass without false positives), so a future regression in any direction is
caught.
"""
from __future__ import annotations

import json
from pathlib import Path

from pdd.architecture_include_validation import (
    cross_validate_architecture_with_prompt_includes,
)
from pdd.architecture_sync import (
    _prompt_dependency_union,
    parse_prompt_tags,
)


def _write_arch(tmp_path: Path, modules: list[dict]) -> None:
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": modules}), encoding="utf-8"
    )


# ---- Finding 1: bare include into path-qualified arch entry --------------


def test_finding1_bare_include_into_path_qualified_arch_entry(tmp_path: Path) -> None:
    """A bare ``<include>b_python.prompt</include>`` from a path-qualified
    prompt (``commands/a_python.prompt``) must not produce a false-positive
    drift warning when arch.json keys the dep as ``commands/b_python.prompt``
    (which is what sync's fuzzy resolver writes). Pre-fix, the validator keyed
    the include as bare ``b`` and the arch entry as ``commands/b``, so the
    sets disagreed and reverse-drift fired on a perfectly synced repo."""
    prompts = tmp_path / "prompts"
    (prompts / "commands").mkdir(parents=True)
    (prompts / "commands" / "a_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n\n"
        "<include>b_python.prompt</include>\n\n"
        "% body\n",
        encoding="utf-8",
    )
    (prompts / "commands" / "b_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n", encoding="utf-8"
    )
    modules = [
        {
            "filename": "commands/a_python.prompt",
            "filepath": "pdd/commands/a.py",
            "dependencies": ["commands/b_python.prompt"],
            "module_tags": ["commands"],
            "priority": 10,
            "reason": "r",
        },
        {
            "filename": "commands/b_python.prompt",
            "filepath": "pdd/commands/b.py",
            "dependencies": [],
            "module_tags": ["commands"],
            "priority": 20,
            "reason": "r",
        },
    ]
    _write_arch(tmp_path, modules)
    warnings = cross_validate_architecture_with_prompt_includes(modules, tmp_path)
    drift = [w for w in warnings if "architecture.json / <include> mismatch" in w]
    assert drift == [], f"Validator flagged false-positive drift: {drift}"


def test_finding1_truly_missing_module_still_warns(tmp_path: Path) -> None:
    """The resolver-based normalization must not mask genuine drift. A bare
    include that names no arch entry at all still keys to a bare stem and
    still surfaces as reverse drift."""
    prompts = tmp_path / "prompts"
    (prompts / "commands").mkdir(parents=True)
    (prompts / "commands" / "a_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n\n"
        "<include>ghost_python.prompt</include>\n\n"
        "% body\n",
        encoding="utf-8",
    )
    (prompts / "commands" / "ghost_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n", encoding="utf-8"
    )
    modules = [
        {
            "filename": "commands/a_python.prompt",
            "filepath": "pdd/commands/a.py",
            "dependencies": [],
            "module_tags": ["commands"],
            "priority": 10,
            "reason": "r",
        }
    ]
    _write_arch(tmp_path, modules)
    warnings = cross_validate_architecture_with_prompt_includes(modules, tmp_path)
    drift = [w for w in warnings if "architecture.json / <include> mismatch" in w]
    assert drift, "Genuine missing include must still produce drift, got none"


# ---- Finding 2: reverse check must catch <pdd-dependency> drift --------


def test_finding2_pdd_dependency_drift_warns(tmp_path: Path) -> None:
    """A ``<pdd-dependency>`` tag with no matching entry in
    arch.dependencies must surface as drift. Pre-fix, the reverse check
    only inspected ``<include>`` tags; the documented union semantics
    treat both as architecture edges, so both must produce drift warnings."""
    prompts = tmp_path / "prompts"
    prompts.mkdir(parents=True)
    (prompts / "a_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n\n"
        "<pdd-dependency>b_python.prompt</pdd-dependency>\n\n"
        "% body\n",
        encoding="utf-8",
    )
    (prompts / "b_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n", encoding="utf-8"
    )
    modules = [
        {
            "filename": "a_python.prompt",
            "filepath": "pdd/a.py",
            "dependencies": [],
            "module_tags": [],
            "priority": 10,
            "reason": "r",
        },
        {
            "filename": "b_python.prompt",
            "filepath": "pdd/b.py",
            "dependencies": [],
            "module_tags": [],
            "priority": 20,
            "reason": "r",
        },
    ]
    _write_arch(tmp_path, modules)
    warnings = cross_validate_architecture_with_prompt_includes(modules, tmp_path)
    drift = [w for w in warnings if "<pdd-dependency>" in w and "a_python.prompt" in w]
    assert drift, (
        "Expected reverse drift warning for <pdd-dependency> not listed in "
        f"arch.dependencies, got: {warnings}"
    )


def test_finding2_pdd_dependency_aligned_no_warning(tmp_path: Path) -> None:
    """When the prompt and arch.json agree on a ``<pdd-dependency>``, no
    warning fires. Guards against over-firing the new reverse check."""
    prompts = tmp_path / "prompts"
    prompts.mkdir(parents=True)
    (prompts / "a_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n\n"
        "<pdd-dependency>b_python.prompt</pdd-dependency>\n\n"
        "% body\n",
        encoding="utf-8",
    )
    (prompts / "b_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n", encoding="utf-8"
    )
    modules = [
        {
            "filename": "a_python.prompt",
            "filepath": "pdd/a.py",
            "dependencies": ["b_python.prompt"],
            "module_tags": [],
            "priority": 10,
            "reason": "r",
        },
        {
            "filename": "b_python.prompt",
            "filepath": "pdd/b.py",
            "dependencies": [],
            "module_tags": [],
            "priority": 20,
            "reason": "r",
        },
    ]
    _write_arch(tmp_path, modules)
    warnings = cross_validate_architecture_with_prompt_includes(modules, tmp_path)
    assert warnings == [], f"Aligned config must not warn, got: {warnings}"


# ---- Finding 3: prompt_content_override must reach include scan -------


def test_finding3_prompt_content_override_threaded_to_includes(tmp_path: Path) -> None:
    """``_prompt_dependency_union`` must scan ``prompt_content`` for includes
    when supplied, not silently re-read the on-disk file. Without the
    threading, an in-memory override with a NEW include would be dropped
    from the union."""
    prompts = tmp_path / "prompts"
    prompts.mkdir(parents=True)
    (prompts / "a_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n\n% body\n", encoding="utf-8"
    )
    (prompts / "b_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n", encoding="utf-8"
    )
    override_content = (
        "<pdd-reason>r</pdd-reason>\n\n"
        "<include>b_python.prompt</include>\n\n"
        "% body\n"
    )
    tags = parse_prompt_tags(override_content)
    arch_data = [
        {"filename": "a_python.prompt", "filepath": "pdd/a.py", "dependencies": []},
        {"filename": "b_python.prompt", "filepath": "pdd/b.py", "dependencies": []},
    ]
    union, has_intent = _prompt_dependency_union(
        tags,
        arch_data,
        override_content,
        self_filename="a_python.prompt",
    )
    assert has_intent, "Override declares intent via include; expected has_intent=True"
    assert "b_python.prompt" in union, (
        f"Override include must appear in union, got {union}"
    )


def test_finding3_disk_content_passed_directly(tmp_path: Path) -> None:
    """When the caller wants on-disk semantics, it reads the file once
    and passes the content. Verifies that the same content-only API
    works for the legacy disk-backed flow (regression for the previously
    optional-content default that re-read from disk silently)."""
    prompts = tmp_path / "prompts"
    prompts.mkdir(parents=True)
    on_disk = (
        "<pdd-reason>r</pdd-reason>\n\n"
        "<include>b_python.prompt</include>\n\n"
        "% body\n"
    )
    (prompts / "a_python.prompt").write_text(on_disk, encoding="utf-8")
    (prompts / "b_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n", encoding="utf-8"
    )
    tags = parse_prompt_tags(on_disk)
    arch_data = [
        {"filename": "a_python.prompt", "filepath": "pdd/a.py", "dependencies": []},
        {"filename": "b_python.prompt", "filepath": "pdd/b.py", "dependencies": []},
    ]
    union, has_intent = _prompt_dependency_union(
        tags,
        arch_data,
        on_disk,
        self_filename="a_python.prompt",
    )
    assert has_intent and "b_python.prompt" in union
