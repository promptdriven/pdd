"""Deterministic, read-only architecture completeness gate.

Enforces a bijection between prompt files, ``architecture.json`` entries, code
artifacts, tests, and examples.  Runs in shadow mode by default:
set ``PDD_ARCH_COMPLETENESS_MODE=required`` to exit 1 on any unwaived gap.

Pattern follows ``tests/test_architecture.py`` (hand-written, no companion
``pdd/`` module).  No LLM credentials or cloud access required.
"""
from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path, PurePosixPath

import pytest

from pdd.architecture_registry import find_architecture_for_project
from pdd.sync_core.language import LanguageRegistry

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

REPO_ROOT = Path(__file__).parents[1]
_WAIVER_PATH = PurePosixPath(".pdd/arch-waivers.json")
_MODE = os.environ.get("PDD_ARCH_COMPLETENESS_MODE", "shadow").strip().lower()
_BASE_REF = os.environ.get("PDD_BASE_REF", "").strip()
_HEAD_REF = os.environ.get("PDD_HEAD_REF", "").strip()

# ---------------------------------------------------------------------------
# Waiver loading — base/head union (modeled on pdd/sync_core/waivers.py)
# ---------------------------------------------------------------------------


def _read_git_blob(ref: str, path: PurePosixPath) -> bytes | None:
    result = subprocess.run(
        ["git", "show", f"{ref}:{path.as_posix()}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    return result.stdout if result.returncode == 0 else None


def _parse_waived_stems(raw: bytes | None) -> set[str]:
    """Return the set of waived module stems from raw waiver JSON bytes."""
    if raw is None:
        return set()
    try:
        payload = json.loads(raw)
    except (json.JSONDecodeError, UnicodeDecodeError):
        return set()
    if not isinstance(payload, dict):
        return set()
    rows = payload.get("waivers")
    if not isinstance(rows, list):
        return set()
    stems: set[str] = set()
    for row in rows:
        if isinstance(row, dict) and isinstance(row.get("module_stem"), str):
            stems.add(row["module_stem"].strip())
    return stems


def _load_waived_stems() -> set[str]:
    """Load waived stems using base/head union when git refs are available."""
    if _BASE_REF and _HEAD_REF:
        base = _parse_waived_stems(_read_git_blob(_BASE_REF, _WAIVER_PATH))
        head = _parse_waived_stems(_read_git_blob(_HEAD_REF, _WAIVER_PATH))
        return base | head
    disk = REPO_ROOT / _WAIVER_PATH
    if disk.exists():
        return _parse_waived_stems(disk.read_bytes())
    return set()


# ---------------------------------------------------------------------------
# Language suffix helpers
# ---------------------------------------------------------------------------

def _all_lang_suffixes() -> frozenset[str]:
    """Return all language suffixes known to the bundled LanguageRegistry."""
    registry = LanguageRegistry.bundled()
    return frozenset(f"_{spec.language_id}" for spec in registry.specs)


def _prompt_stem(filename: str, lang_suffixes: frozenset[str]) -> str:
    """Strip language suffix from a prompt filename to get the module stem."""
    name = filename.removesuffix(".prompt")
    for suffix in lang_suffixes:
        if name.endswith(suffix):
            return name[: -len(suffix)]
    return name


# ---------------------------------------------------------------------------
# Inventory enumeration
# ---------------------------------------------------------------------------

def _enumerate_prompts() -> set[str]:
    """Return the set of prompt *filenames* (not paths) in prompts/."""
    prompts_dir = REPO_ROOT / "prompts"
    if not prompts_dir.is_dir():
        return set()
    return {
        p.name
        for p in prompts_dir.iterdir()
        if p.suffix == ".prompt" and p.is_file()
    }


def _enumerate_arch_entries(arch_files: list[Path]) -> dict[str, dict]:
    """Map prompt filename → architecture entry for all discovered arch files.

    Duplicate filenames are already caught by ``tests/test_architecture.py``
    so we take the first occurrence here.
    """
    entries: dict[str, dict] = {}
    for arch_file in arch_files:
        try:
            data = json.loads(arch_file.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            continue
        if not isinstance(data, list):
            continue
        for entry in data:
            if not isinstance(entry, dict):
                continue
            fname = entry.get("filename")
            if isinstance(fname, str) and fname.endswith(".prompt") and fname not in entries:
                entries[fname] = entry
    return entries


# ---------------------------------------------------------------------------
# Existence helpers
# ---------------------------------------------------------------------------

def _code_exists(filepath: str) -> bool:
    return bool(filepath) and (REPO_ROOT / filepath).is_file()


def _test_exists(stem: str) -> bool:
    return (REPO_ROOT / "tests" / f"test_{stem}.py").is_file()


def _example_exists(stem: str) -> bool:
    examples = REPO_ROOT / "examples"
    return (examples / f"{stem}.py").is_file() or (examples / stem).is_dir()


# ---------------------------------------------------------------------------
# Gate
# ---------------------------------------------------------------------------

def test_architecture_completeness() -> None:
    """Bijection gate: prompts ↔ architecture.json ↔ code / tests / examples.

    Failure categories (reported separately for unambiguous triage):

    * ``PROMPT_WITHOUT_ARCH``     — prompt file on disk, no architecture entry
    * ``ARCH_WITHOUT_PROMPT``     — architecture entry whose prompt is missing
    * ``PROMPT_WITHOUT_CODE``     — prompt+arch pair with no code artifact
    * ``CODE_WITHOUT_PROMPT``     — architecture code exists but prompt is missing
    * ``MISSING_TESTS``           — matched prompt–code pair has no test file
    * ``MISSING_EXAMPLES``        — matched prompt–code pair has no example
    * ``UNRESOLVABLE_ARCH_PATH``  — architecture filepath does not exist on disk

    ``DUPLICATE_ARCH_ENTRY`` is delegated to ``tests/test_architecture.py``.

    Shadow mode (default, ``PDD_ARCH_COMPLETENESS_MODE=shadow``): prints all
    gaps and exits 0.  Required mode (``=required``): calls ``pytest.fail``.
    """
    waived = _load_waived_stems()
    lang_suffixes = _all_lang_suffixes()
    arch_files = find_architecture_for_project(REPO_ROOT)
    arch_entries = _enumerate_arch_entries(arch_files)
    all_prompts = _enumerate_prompts()
    arch_filenames = set(arch_entries.keys())

    gaps: dict[str, list[str]] = {
        "PROMPT_WITHOUT_ARCH": [],
        "ARCH_WITHOUT_PROMPT": [],
        "PROMPT_WITHOUT_CODE": [],
        "CODE_WITHOUT_PROMPT": [],
        "MISSING_TESTS": [],
        "MISSING_EXAMPLES": [],
        "UNRESOLVABLE_ARCH_PATH": [],
    }

    # --- PROMPT_WITHOUT_ARCH ---
    for pf in sorted(all_prompts):
        stem = _prompt_stem(pf, lang_suffixes)
        if stem in waived:
            continue
        if pf not in arch_filenames:
            gaps["PROMPT_WITHOUT_ARCH"].append(pf)

    # --- Per-architecture-entry checks ---
    for arch_fname, entry in sorted(arch_entries.items()):
        stem = _prompt_stem(arch_fname, lang_suffixes)
        if stem in waived:
            continue

        prompt_on_disk = arch_fname in all_prompts
        filepath: str = entry.get("filepath") or ""
        code_on_disk = _code_exists(filepath)

        # ARCH_WITHOUT_PROMPT: architecture references a prompt that is missing
        if not prompt_on_disk:
            gaps["ARCH_WITHOUT_PROMPT"].append(arch_fname)

        # CODE_WITHOUT_PROMPT: code exists in architecture but no prompt on disk
        if code_on_disk and not prompt_on_disk:
            gaps["CODE_WITHOUT_PROMPT"].append(
                f"{filepath} (architecture entry: {arch_fname})"
            )

        # UNRESOLVABLE_ARCH_PATH: filepath declared but does not exist
        if filepath and not code_on_disk:
            gaps["UNRESOLVABLE_ARCH_PATH"].append(
                f"{arch_fname}: filepath {filepath!r} not found on disk"
            )

        # PROMPT_WITHOUT_CODE: prompt+arch exist but no code artifact
        if prompt_on_disk and filepath and not code_on_disk:
            gaps["PROMPT_WITHOUT_CODE"].append(
                f"{arch_fname} -> {filepath} (not found)"
            )
        elif prompt_on_disk and not filepath:
            gaps["PROMPT_WITHOUT_CODE"].append(
                f"{arch_fname} (no filepath in architecture.json)"
            )

        # MISSING_TESTS / MISSING_EXAMPLES: only for fully matched pairs
        if prompt_on_disk and code_on_disk:
            if not _test_exists(stem):
                gaps["MISSING_TESTS"].append(
                    f"{stem} (expected tests/test_{stem}.py)"
                )
            if not _example_exists(stem):
                gaps["MISSING_EXAMPLES"].append(
                    f"{stem} (expected examples/{stem}.py or examples/{stem}/)"
                )

    # --- Report ---
    total = sum(len(v) for v in gaps.values())
    if total == 0:
        return

    _MAX_PER_CATEGORY = 30
    lines = [f"\nArchitecture completeness: {total} gap(s) found\n"]
    for category, items in gaps.items():
        if not items:
            continue
        lines.append(f"  {category} ({len(items)}):")
        for item in items[:_MAX_PER_CATEGORY]:
            lines.append(f"    - {item}")
        if len(items) > _MAX_PER_CATEGORY:
            lines.append(f"    ... and {len(items) - _MAX_PER_CATEGORY} more")
        lines.append("")

    report = "\n".join(lines)

    if _MODE == "required":
        pytest.fail(report)
    else:
        # Shadow mode: surface gaps without failing CI.
        print(report)
