"""Bijection gate for architecture.json completeness.

``architecture.json`` is the module registry that drives project-wide sync: a
no-arg ``pdd sync`` enumerates modules *from* this file
(``pdd.agentic_sync._architecture_sync_modules``), so any top-level ``pdd/*.py``
module without an entry is invisible to global sync and dependency-ordered heal.

This test asserts a **bijection**: every top-level ``pdd/*.py`` module (after
applying ``.pddignore``) has exactly one architecture entry, UNLESS it is listed
in ``architecture_waivers.json`` under ``modules_without_architecture_entry``
(hand-written utilities/CLI wiring with no generating prompt). It also asserts
every entry's ``filepath`` and ``filename`` exist on disk, and ratchets the
adjacent orphan gaps (prompt-no-code, code-no-prompt, code-no-test) so new gaps
must be documented rather than appearing silently.

To fix a failure:
- module missing an entry -> run ``pdd sync-architecture`` or author the entry,
  or (for promptless hand-written modules) add it to the waiver with a reason.
- stale waiver -> delete the line once the module has an entry / is removed.
- new orphan -> add a one-line justification under the relevant ``orphans`` list.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, List, Set

import pytest

from pdd.agentic_sync_runner import _basename_from_architecture_filename
from pdd.architecture_registry import extract_modules
from pdd.update_main import _is_pddignored, _load_pddignore

REPO_ROOT = Path(__file__).resolve().parent.parent
ARCHITECTURE_JSON = REPO_ROOT / "architecture.json"
WAIVERS_JSON = REPO_ROOT / "architecture_waivers.json"

# Fields present in every architecture entry today (the hard invariant).
REQUIRED_ENTRY_FIELDS = (
    "reason",
    "dependencies",
    "priority",
    "filename",
    "filepath",
    "tags",
    "interface",
)


# --------------------------------------------------------------------------- #
# Fixtures / shared computation                                               #
# --------------------------------------------------------------------------- #
@pytest.fixture(scope="module")
def entries() -> List[dict]:
    return extract_modules(json.loads(ARCHITECTURE_JSON.read_text(encoding="utf-8")))


@pytest.fixture(scope="module")
def waivers() -> dict:
    return json.loads(WAIVERS_JSON.read_text(encoding="utf-8"))


def _candidate_modules() -> Dict[str, Path]:
    """Top-level ``pdd/*.py`` modules that survive ``.pddignore`` (the sync scope)."""
    patterns, pddignore_root = _load_pddignore(str(REPO_ROOT))
    modules: Dict[str, Path] = {}
    for path in sorted(REPO_ROOT.glob("pdd/*.py")):
        if _is_pddignored(str(path), pddignore_root, patterns):
            continue
        modules[path.stem] = path
    return modules


def _covered_toplevel_modules(entries: List[dict]) -> Set[str]:
    """Module basenames covered by an entry whose ``filepath`` is ``pdd/<mod>.py``."""
    covered: Set[str] = set()
    for entry in entries:
        filepath = str(entry.get("filepath") or "").replace("\\", "/").strip().lstrip("/")
        if not filepath:
            continue
        path = Path(filepath)
        if path.parent == Path("pdd") and path.suffix == ".py":
            covered.add(path.stem)
    return covered


def _prompt_basenames() -> Dict[str, List[str]]:
    """Top-level ``prompts/*.prompt`` grouped by module basename (LLM-only skipped)."""
    grouped: Dict[str, List[str]] = {}
    for prompt in sorted((REPO_ROOT / "prompts").glob("*.prompt")):
        base = _basename_from_architecture_filename(prompt.name)
        if base:
            grouped.setdefault(base, []).append(prompt.name)
    return grouped


def _resolve_prompt(filename: str) -> bool:
    filename = (filename or "").replace("\\", "/").lstrip("/")
    if not filename:
        return False
    candidates = [
        REPO_ROOT / "prompts" / filename,
        REPO_ROOT / filename,
        REPO_ROOT / "prompts" / Path(filename).name,
        REPO_ROOT / "pdd" / "prompts" / filename,
        REPO_ROOT / "pdd" / "prompts" / Path(filename).name,
    ]
    return any(candidate.exists() for candidate in candidates)


def _bijection_gap(entries: List[dict], waivers: dict):
    """Return (undocumented_missing, stale_waivers) for the module<->entry bijection."""
    modules = set(_candidate_modules())
    covered = _covered_toplevel_modules(entries) & modules
    missing = modules - covered
    waived = set(waivers.get("modules_without_architecture_entry", {}))
    undocumented_missing = sorted(missing - waived)
    # stale = waived but the module now has an entry, or no longer exists on disk
    stale = sorted((waived & covered) | {m for m in waived if m not in modules})
    return undocumented_missing, stale


# --------------------------------------------------------------------------- #
# Structural sanity                                                           #
# --------------------------------------------------------------------------- #
def test_architecture_json_is_nonempty_list(entries: List[dict]) -> None:
    assert entries, "architecture.json parsed to zero module entries"


def test_entries_have_required_fields(entries: List[dict]) -> None:
    offenders: List[str] = []
    for entry in entries:
        missing = [f for f in REQUIRED_ENTRY_FIELDS if f not in entry]
        if missing:
            offenders.append(f"{entry.get('filename') or entry.get('filepath')!r}: missing {missing}")
    assert not offenders, "architecture entries missing required fields:\n  " + "\n  ".join(offenders)


def test_entries_have_description(entries: List[dict], waivers: dict) -> None:
    """Every entry should carry a description, minus documented pre-existing gaps."""
    allowed = set(waivers["known_registry_exceptions"]["entries_without_description"])
    offenders = sorted(
        str(e.get("filename"))
        for e in entries
        if "description" not in e and str(e.get("filename")) not in allowed
    )
    assert not offenders, (
        "architecture entries missing 'description' (add one, or document under "
        "known_registry_exceptions.entries_without_description):\n  " + "\n  ".join(offenders)
    )


def test_no_duplicate_filepaths(entries: List[dict], waivers: dict) -> None:
    """Bijection direction: at most one entry per code file (minus tracked pre-existing dupes)."""
    allowed = set(waivers["known_registry_exceptions"]["duplicate_filepaths"])
    seen: Dict[str, int] = {}
    for entry in entries:
        fp = str(entry.get("filepath") or "").strip()
        if fp:
            seen[fp] = seen.get(fp, 0) + 1
    dupes = {fp: n for fp, n in seen.items() if n > 1 and fp not in allowed}
    assert not dupes, (
        "duplicate filepaths in architecture.json (one entry per module expected; "
        "document a known pre-existing dupe under known_registry_exceptions.duplicate_filepaths):\n  "
        + "\n  ".join(f"{fp} x{n}" for fp, n in sorted(dupes.items()))
    )


def test_every_entry_points_at_real_files(entries: List[dict]) -> None:
    """Every entry's filepath (code) and filename (prompt) must exist on disk."""
    bad_filepath: List[str] = []
    bad_filename: List[str] = []
    for entry in entries:
        fp = str(entry.get("filepath") or "").replace("\\", "/").strip().lstrip("/")
        if not fp or not (REPO_ROOT / fp).exists():
            bad_filepath.append(f"{entry.get('filename')!r} -> filepath {entry.get('filepath')!r}")
        if not _resolve_prompt(entry.get("filename", "")):
            bad_filename.append(f"{entry.get('filename')!r} (filepath {entry.get('filepath')!r})")
    msg = []
    if bad_filepath:
        msg.append("entries whose filepath is missing on disk:\n  " + "\n  ".join(bad_filepath))
    if bad_filename:
        msg.append("entries whose filename prompt is missing on disk:\n  " + "\n  ".join(bad_filename))
    assert not msg, "\n".join(msg)


# --------------------------------------------------------------------------- #
# The bijection gate                                                          #
# --------------------------------------------------------------------------- #
def test_module_entry_bijection(entries: List[dict], waivers: dict) -> None:
    undocumented_missing, stale = _bijection_gap(entries, waivers)
    problems: List[str] = []
    if undocumented_missing:
        problems.append(
            "top-level pdd/*.py modules with no architecture.json entry and no waiver:\n  "
            + "\n  ".join(undocumented_missing)
            + "\n-> run `pdd sync-architecture` / author an entry, or add each to "
            "architecture_waivers.json 'modules_without_architecture_entry' with a one-line reason."
        )
    if stale:
        problems.append(
            "stale waivers in architecture_waivers.json 'modules_without_architecture_entry' "
            "(module now has an entry or no longer exists):\n  " + "\n  ".join(stale)
            + "\n-> delete these lines."
        )
    assert not problems, "\n\n".join(problems)


def test_waived_modules_have_no_entry(entries: List[dict], waivers: dict) -> None:
    """A waived module must genuinely lack an entry (keeps the waiver honest)."""
    covered = _covered_toplevel_modules(entries)
    both = sorted(set(waivers.get("modules_without_architecture_entry", {})) & covered)
    assert not both, (
        "modules both waived AND present in architecture.json (remove the waiver):\n  "
        + "\n  ".join(both)
    )


# --------------------------------------------------------------------------- #
# Orphan ratchet (new gaps must be documented; fixing a gap needs no edit)    #
# --------------------------------------------------------------------------- #
def test_prompt_without_code_ratchet(waivers: dict) -> None:
    prompt_bases = _prompt_basenames()
    computed = {b for b in prompt_bases if not (REPO_ROOT / "pdd" / f"{b}.py").exists()}
    documented = set(waivers["orphans"]["prompt_without_code"])
    undocumented = sorted(computed - documented)
    assert not undocumented, (
        "prompt(s) with no corresponding pdd/<name>.py not documented in "
        "architecture_waivers.json orphans.prompt_without_code:\n  " + "\n  ".join(undocumented)
    )


def test_code_without_prompt_ratchet(waivers: dict) -> None:
    modules = _candidate_modules()
    prompt_bases = _prompt_basenames()
    computed = {m for m in modules if m not in prompt_bases}
    documented = set(waivers["orphans"]["code_without_prompt"])
    undocumented = sorted(computed - documented)
    assert not undocumented, (
        "module(s) with no top-level prompt not documented in "
        "architecture_waivers.json orphans.code_without_prompt:\n  " + "\n  ".join(undocumented)
    )


def test_code_without_test_ratchet(waivers: dict) -> None:
    modules = _candidate_modules()
    computed = {m for m in modules if not (REPO_ROOT / "tests" / f"test_{m}.py").exists()}
    documented = set(waivers["orphans"]["code_without_test"])
    undocumented = sorted(computed - documented)
    assert not undocumented, (
        "module(s) with no tests/test_<module>.py not documented in "
        "architecture_waivers.json orphans.code_without_test:\n  " + "\n  ".join(undocumented)
    )


# --------------------------------------------------------------------------- #
# Meta: prove the gate has teeth (acceptance criterion)                       #
# --------------------------------------------------------------------------- #
def test_gate_detects_removed_entry(entries: List[dict], waivers: dict) -> None:
    """Deleting a covered module's entry must surface as an undocumented gap."""
    covered = sorted(_covered_toplevel_modules(entries) & set(_candidate_modules()))
    assert covered, "expected at least one covered top-level module"
    victim = "construct_paths" if "construct_paths" in covered else covered[0]
    pruned = [e for e in entries if Path(str(e.get("filepath") or "")).stem != victim]
    undocumented_missing, _ = _bijection_gap(pruned, waivers)
    assert victim in undocumented_missing, (
        f"bijection gate failed to detect a removed entry for {victim!r}"
    )


def test_gate_detects_unwaived_new_module(entries: List[dict], waivers: dict) -> None:
    """A module present neither as an entry nor a waiver must fail the gate."""
    phantom = "zzz_phantom_module_for_test"
    waived = set(waivers.get("modules_without_architecture_entry", {}))
    covered = _covered_toplevel_modules(entries)
    # Simulate the gap computation with an extra on-disk module.
    modules = set(_candidate_modules()) | {phantom}
    missing = modules - (covered & modules)
    undocumented = sorted(missing - waived)
    assert phantom in undocumented, "bijection gate failed to detect an unwaived new module"
