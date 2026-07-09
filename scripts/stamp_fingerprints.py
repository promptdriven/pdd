#!/usr/bin/env python3
"""Stamp / verify ``.pdd/meta`` fingerprints for every PDD dev unit (stdlib only).

The committed ``.pdd/meta/<unit>.json`` fingerprints are the oracle ``pdd sync``
trusts to decide whether a unit changed. When they are missing or stale, sync
diffs current files against absent/old hashes, sees phantom "changed" verdicts,
and regenerates mature modules (issue #1938). This script keeps that oracle
current for the whole tree:

* ``stamp`` (default): for every unit, recompute all hashes from the files on
  disk and write the fingerprint JSON, byte-identically to how ``pdd`` writes
  it (``pdd/sync_orchestration.py`` ``_atomic_write`` / ``operation_log.save_fingerprint``
  -> ``json.dump(..., indent=2)`` with no trailing newline, ``Fingerprint``
  dataclass key order). Existing units keep their ``command``; new units get a
  neutral ``command`` (see ``NEW_UNIT_COMMAND``).

* ``--check``: recompute every unit's hashes and compare to the committed
  fingerprint. Exit non-zero listing units whose stored hashes are stale (drift
  or a hand-edit) or that have no committed fingerprint and are not waived. This
  is the primitive the CI gate reuses.

Stdlib only, no ``pdd`` import, no LLM: the hashing is vendored verbatim from
``pdd/sync_determine_operation.py`` (pinned byte-for-byte by the cross-check in
``tests/test_stamp_fingerprints.py``). Path resolution mirrors the repo's
``.pddrc`` convention: a prompt at ``pdd/prompts/<sub>/<leaf>_python.prompt``
maps to code ``pdd/<sub>/<leaf>.py``, example ``context/<sub>/<leaf>_example.py``,
tests ``tests/<sub>/test_<leaf>*.py``.

Never hand-edit ``.pdd/meta``; regenerate via this stamper (see CONTRIBUTING.md).
"""
from __future__ import annotations

import argparse
import fnmatch
import glob
import hashlib
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# --- Repo layout -------------------------------------------------------------

REPO_ROOT = Path(__file__).resolve().parent.parent
PROMPTS_ROOT = REPO_ROOT / "pdd" / "prompts"
META_DIR = REPO_ROOT / ".pdd" / "meta"
WAIVERS_FILE = REPO_ROOT / "scripts" / "fingerprint_waivers.json"
ARCHITECTURE_FILE = REPO_ROOT / "architecture.json"

LANGUAGE = "python"
PROMPT_SUFFIX = "_python.prompt"

# The ``command`` recorded for a freshly-created fingerprint. ``pdd sync``'s
# completion gate (sync_determine_operation.py: COMPLETED_VERIFY_COMMANDS /
# COMPLETED_TEST_COMMANDS = {'verify','test','fix','update'} / {'test','fix',
# 'update'}) treats a unit as "workflow complete" -> nothing to do only when the
# command is in {test, fix, update}. 'fix' is chosen because it satisfies both
# gates, triggers none of the special branches ('auto-deps' forces generate,
# 'crash' forces a retry, a 'skip:' prefix means skipped), and is already the
# modal command among committed fingerprints. The epoch stamp declares the
# current tree the agreed baseline, so a terminal at-rest command is truthful.
NEW_UNIT_COMMAND = "fix"

# Fingerprint dataclass field order (pdd/sync_determine_operation.py Fingerprint).
# Written key order MUST match so a subsequent `pdd sync` produces no spurious diff.
FIELD_ORDER = (
    "pdd_version",
    "timestamp",
    "command",
    "prompt_hash",
    "code_hash",
    "example_hash",
    "test_hash",
    "test_files",
    "include_deps",
)

# Hash fields --check recomputes and compares (metadata fields pdd_version /
# timestamp / command are not content-derived and are not checked).
HASH_FIELDS = (
    "prompt_hash",
    "code_hash",
    "example_hash",
    "test_hash",
    "test_files",
    "include_deps",
)


# --- BEGIN verbatim copies from pdd/pdd/sync_determine_operation.py -----------
# Keep byte-for-byte identical to pdd so recomputed hashes match the CLI. Pinned
# by tests/test_stamp_fingerprints.py::test_hash_parity_with_pdd.

_INCLUDE_PATTERN = re.compile(r"<include\b[^>]*>(.*?)</include>")
_BACKTICK_INCLUDE_PATTERN = re.compile(r"```<([^>]*?)>```")


def calculate_sha256(file_path: Path) -> Optional[str]:
    """Calculates the SHA256 hash of a file if it exists."""
    if not file_path.exists():
        return None

    try:
        hasher = hashlib.sha256()
        with open(file_path, "rb") as f:
            for chunk in iter(lambda: f.read(4096), b""):
                hasher.update(chunk)
        return hasher.hexdigest()
    except (IOError, OSError):
        return None


def _resolve_include_path(include_ref: str, prompt_dir: Path) -> Optional[Path]:
    """Resolve an <include> reference to an absolute Path."""
    p = Path(include_ref)
    if p.is_absolute() and p.exists():
        return p
    candidate = prompt_dir / include_ref
    if candidate.exists():
        return candidate
    candidate = Path.cwd() / include_ref
    if candidate.exists():
        return candidate
    return None


def extract_include_deps(prompt_path: Path) -> Dict[str, str]:
    """Extract include dependency paths and their hashes from a prompt file.

    Returns a dict mapping resolved dependency paths to their SHA256 hashes.
    Only includes dependencies that exist on disk.
    """
    if not prompt_path.exists():
        return {}

    try:
        prompt_content = prompt_path.read_text(encoding="utf-8", errors="ignore")
    except (IOError, OSError):
        return {}

    include_refs = _INCLUDE_PATTERN.findall(prompt_content)
    include_refs += _BACKTICK_INCLUDE_PATTERN.findall(prompt_content)

    if not include_refs:
        return {}

    deps = {}
    prompt_dir = prompt_path.parent
    for ref in sorted(set(r.strip() for r in include_refs)):
        dep_path = _resolve_include_path(ref, prompt_dir)
        if dep_path and dep_path.exists():
            dep_hash = calculate_sha256(dep_path)
            if dep_hash:
                try:
                    rel_path = dep_path.relative_to(Path.cwd())
                except ValueError:
                    rel_path = dep_path
                deps[str(rel_path)] = dep_hash

    return deps


def calculate_prompt_hash(
    prompt_path: Path, stored_deps: Optional[Dict[str, str]] = None
) -> Optional[str]:
    """Hash a prompt file including the content of all its <include> dependencies.

    If the prompt has <include> tags, extracts and hashes those dependencies.
    If no tags are found but stored_deps is provided (from a previous fingerprint),
    uses those stored dependency paths to compute the hash. This handles the case
    where the auto-deps step strips <include> tags from the prompt file.
    """
    if not prompt_path.exists():
        return None

    try:
        prompt_content = prompt_path.read_text(encoding="utf-8", errors="ignore")
    except (IOError, OSError):
        return None

    # Try to find include refs in current prompt content
    include_refs = _INCLUDE_PATTERN.findall(prompt_content)
    include_refs += _BACKTICK_INCLUDE_PATTERN.findall(prompt_content)

    # Resolve to actual paths
    prompt_dir = prompt_path.parent
    dep_paths = []
    if include_refs:
        for ref in sorted(set(r.strip() for r in include_refs)):
            dep_path = _resolve_include_path(ref, prompt_dir)
            if dep_path and dep_path.exists():
                dep_paths.append(dep_path)
    elif stored_deps:
        # No include tags in prompt - use stored dependency paths from fingerprint
        for dep_path_str in sorted(stored_deps.keys()):
            dep_path = Path(dep_path_str)
            if dep_path.exists():
                dep_paths.append(dep_path)

    if not dep_paths:
        return calculate_sha256(prompt_path)

    # Build composite hash: prompt bytes + sorted dependency contents
    hasher = hashlib.sha256()
    try:
        with open(prompt_path, "rb") as f:
            for chunk in iter(lambda: f.read(4096), b""):
                hasher.update(chunk)
    except (IOError, OSError):
        return None

    for dep_path in dep_paths:
        try:
            with open(dep_path, "rb") as f:
                for chunk in iter(lambda: f.read(4096), b""):
                    hasher.update(chunk)
        except (IOError, OSError):
            pass

    return hasher.hexdigest()


# --- END verbatim copies -----------------------------------------------------


def refresh_include_deps(
    prompt_path: Path, stored_deps: Optional[Dict[str, str]] = None
) -> Dict[str, str]:
    """Recompute ``include_deps`` mirroring pdd's ``calculate_current_hashes``.

    Ports the prompt branch of ``sync_determine_operation.calculate_current_hashes``:
    extract fresh deps from the prompt's <include> tags; if the prompt no longer
    has tags but stored deps exist (auto-deps stripped, issue #522), re-hash the
    stored dependency keys.
    """
    deps = extract_include_deps(prompt_path)
    if not deps and stored_deps:
        updated_deps: Dict[str, str] = {}
        for dep_path_str, _old_hash in stored_deps.items():
            dep_path = Path(dep_path_str)
            if dep_path.exists():
                new_hash = calculate_sha256(dep_path)
                if new_hash:
                    updated_deps[dep_path_str] = new_hash
        deps = updated_deps
    return deps


def _safe_basename(basename: str) -> str:
    """Sanitize basename for use in metadata filenames ('/' -> '_')."""
    return basename.replace("/", "_")


# --- architecture.json resolution --------------------------------------------
# pdd's get_pdd_file_paths consults architecture.json FIRST for a module's code
# filepath (issue #225), and disambiguates example/test stems for a bare leaf
# that maps to more than one module (issue #1677). Both are pure JSON+path logic
# (no LLM), so they are mirrored here. For the ~99% of units whose architecture
# filepath equals the .pddrc convention pdd/<basename>.py, this changes nothing;
# it corrects the handful whose code lives outside the prompt's subdir (e.g.
# commands/checkup_simplify -> pdd/checkup_simplify.py) and the ambiguous leaves
# cli/gate.


def _load_architecture():
    """Return ``(by_filename, by_leaf, ambiguous_leaves)`` from architecture.json.

    * ``by_filename``: full architecture filename (lower) -> set of filepaths.
      Architecture filenames are frequently path-qualified (``core/cli_python.prompt``).
    * ``by_leaf``: filename leaf (lower) -> set of filepaths.
    * ``ambiguous_leaves``: basenames whose bare leaf maps to >1 distinct filepath
      (mirrors ``_architecture_module_choices``; these get a disambiguated stem).
    """
    by_filename: Dict[str, set] = {}
    by_leaf: Dict[str, set] = {}
    if not ARCHITECTURE_FILE.is_file():
        return by_filename, by_leaf, frozenset()
    try:
        data = json.loads(ARCHITECTURE_FILE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return by_filename, by_leaf, frozenset()
    modules = data if isinstance(data, list) else data.get("modules", []) if isinstance(data, dict) else []
    for module in modules:
        if not isinstance(module, dict):
            continue
        filename = str(module.get("filename") or "").strip()
        filepath = str(module.get("filepath") or "").strip()
        if not filename or not filepath or filename.endswith("_LLM.prompt"):
            continue
        fp = Path(filepath).as_posix()
        by_filename.setdefault(filename.lower(), set()).add(fp)
        by_leaf.setdefault(Path(filename).name.lower(), set()).add(fp)
    ambiguous = frozenset(
        leaf[: -len(f"_{LANGUAGE}.prompt")]
        for leaf, fps in by_leaf.items()
        if leaf.endswith(f"_{LANGUAGE}.prompt") and len(fps) > 1
    )
    return by_filename, by_leaf, ambiguous


_ARCH_BY_FILENAME, _ARCH_BY_LEAF, _AMBIGUOUS_LEAVES = _load_architecture()


def _resolve_code_and_stem(basename: str) -> Tuple[Path, str]:
    """Return ``(code_path, artifact_stem)`` mirroring pdd's resolution.

    ``code_path`` is the architecture.json filepath when the prompt is listed
    there, else the ``pdd/<basename>.py`` convention. ``artifact_stem`` is the
    stem used for the example/test filenames: the code file's stem, replaced by
    a ``_safe_basename(<filepath sans suffix>)`` disambiguation when the bare leaf
    is ambiguous (issue #1677).
    """
    leaf = basename.rsplit("/", 1)[-1]
    pf_full = f"{basename}_{LANGUAGE}.prompt".lower()
    pf_leaf = f"{leaf}_{LANGUAGE}.prompt".lower()

    arch_fp: Optional[str] = None
    full_fps = _ARCH_BY_FILENAME.get(pf_full)
    if full_fps and len(full_fps) == 1:
        arch_fp = next(iter(full_fps))
    if arch_fp is None:
        leaf_fps = _ARCH_BY_LEAF.get(pf_leaf, set())
        if len(leaf_fps) == 1:
            arch_fp = next(iter(leaf_fps))
        elif len(leaf_fps) > 1:
            # Ambiguous bare leaf: accept only if exactly one filepath aligns
            # with the path-qualified basename (flat ambiguous units are waived).
            aligned = [
                fp for fp in leaf_fps
                if Path(fp).with_suffix("").as_posix().endswith(basename)
            ]
            if len(aligned) == 1:
                arch_fp = aligned[0]

    if arch_fp:
        code = REPO_ROOT / arch_fp
        if leaf in _AMBIGUOUS_LEAVES:
            stem = _safe_basename(Path(arch_fp).with_suffix("").as_posix())
        else:
            stem = Path(arch_fp).stem
    else:
        code = REPO_ROOT / "pdd" / f"{basename}.py"
        stem = leaf
    return code, stem


# --- Unit enumeration & path resolution --------------------------------------


class Unit:
    """A single PDD dev unit resolved from a ``*_python.prompt`` file."""

    __slots__ = ("basename", "prompt", "code", "example", "test", "test_files", "meta")

    def __init__(self, basename: str, prompt: Path) -> None:
        self.basename = basename
        self.prompt = prompt
        # Code path + artifact stem come from architecture.json (falling back to
        # the pdd/<basename>.py convention); the example/test DIRECTORY follows
        # the prompt's subdir (context/<subdir>, tests/<subdir>), mirroring pdd.
        subdir = str(Path(basename).parent) if "/" in basename else ""
        self.code, stem = _resolve_code_and_stem(basename)
        example_dir = REPO_ROOT / "context" / subdir if subdir else REPO_ROOT / "context"
        self.example = example_dir / f"{stem}_example.py"
        test_dir = REPO_ROOT / "tests" / subdir if subdir else REPO_ROOT / "tests"
        self.test = test_dir / f"test_{stem}.py"
        self.test_files = _discover_test_files(test_dir, stem)
        self.meta = META_DIR / f"{_safe_basename(basename)}_{LANGUAGE}.json"


def _discover_test_files(test_dir: Path, stem: str) -> List[Path]:
    """Mirror pdd's Bug #156 test-file globbing: sorted ``test_<stem>*.py``.

    Matches ``get_pdd_file_paths``: glob ``test_<stem>*.py`` in the test dir,
    falling back to the single primary test path when the dir or matches are
    absent.
    """
    primary = test_dir / f"test_{stem}.py"
    if test_dir.is_dir():
        pattern = glob.escape(f"test_{stem}")
        matches = sorted(test_dir.glob(f"{pattern}*.py"))
    else:
        matches = [primary] if primary.exists() else []
    return matches or [primary]


def infer_basename(prompt_path: Path) -> Optional[str]:
    """Return the unit basename for a ``*_python.prompt`` file, or None.

    Basename is the path relative to ``pdd/prompts`` with the ``_python.prompt``
    suffix dropped, subdirectories preserved (e.g. ``commands/which``).
    """
    name = prompt_path.name
    if not name.endswith(PROMPT_SUFFIX):
        return None
    rel = prompt_path.relative_to(PROMPTS_ROOT)
    stem = rel.name[: -len(PROMPT_SUFFIX)]
    subdir = rel.parent
    if str(subdir) == ".":
        return stem
    return (subdir / stem).as_posix()


def enumerate_units() -> List[Unit]:
    """Return every python unit under ``pdd/prompts`` sorted by basename."""
    units: List[Unit] = []
    for prompt in sorted(PROMPTS_ROOT.rglob(f"*{PROMPT_SUFFIX}")):
        basename = infer_basename(prompt)
        if basename is None:
            continue
        units.append(Unit(basename, prompt))
    return units


# --- .pddignore --------------------------------------------------------------


def load_pddignore() -> List[str]:
    """Load ``.pddignore`` patterns from the repo root (comments/blank stripped)."""
    path = REPO_ROOT / ".pddignore"
    patterns: List[str] = []
    if not path.is_file():
        return patterns
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        patterns.append(line)
    return patterns


def is_pddignored(code_path: Path, patterns: List[str]) -> bool:
    """Mirror pdd/update_main.py ``_is_pddignored`` against the code path.

    Matches the repo-relative POSIX path and the basename via fnmatch, plus
    directory-prefix patterns ending in '/'.
    """
    try:
        rel_path = code_path.resolve().relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return False
    basename = code_path.name
    for pat in patterns:
        if pat.endswith("/"):
            dir_name = pat.rstrip("/")
            parts = rel_path.split("/")
            if dir_name in parts[:-1]:
                return True
        else:
            if fnmatch.fnmatch(rel_path, pat):
                return True
            if fnmatch.fnmatch(basename, pat):
                return True
    return False


# --- Waivers -----------------------------------------------------------------


def load_waivers() -> Dict[str, str]:
    """Return ``{basename: reason}`` from the committed waiver file."""
    if not WAIVERS_FILE.is_file():
        return {}
    data = json.loads(WAIVERS_FILE.read_text(encoding="utf-8"))
    waivers: Dict[str, str] = {}
    for entry in data.get("waivers", []):
        waivers[entry["basename"]] = entry.get("reason", "")
    return waivers


# --- Meta read / write -------------------------------------------------------


def read_meta(meta_path: Path) -> Optional[Dict]:
    """Read an existing fingerprint JSON, or None if absent/unreadable."""
    if not meta_path.exists():
        return None
    try:
        data = json.loads(meta_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return data if isinstance(data, dict) else None


def compute_hashes(unit: Unit, stored_deps: Optional[Dict[str, str]]) -> Dict:
    """Recompute all fingerprint hash fields for a unit from disk.

    Mirrors ``calculate_current_hashes``: composite ``prompt_hash`` (with stored
    deps fallback), per-file sha256, and the Bug #156 ``test_files`` map.
    """
    test_files = {
        f.name: calculate_sha256(f) for f in unit.test_files if f.exists()
    }
    return {
        "prompt_hash": calculate_prompt_hash(unit.prompt, stored_deps=stored_deps),
        "code_hash": calculate_sha256(unit.code),
        "example_hash": calculate_sha256(unit.example),
        "test_hash": calculate_sha256(unit.test),
        "test_files": test_files,
        "include_deps": refresh_include_deps(unit.prompt, stored_deps),
    }


def build_fingerprint(unit: Unit, pdd_version: str) -> Dict:
    """Build the full fingerprint dict for a unit (preserving prior command)."""
    existing = read_meta(unit.meta)
    stored_deps = None
    command = NEW_UNIT_COMMAND
    if existing is not None:
        sd = existing.get("include_deps")
        stored_deps = sd if isinstance(sd, dict) else None
        if existing.get("command"):
            command = existing["command"]
    hashes = compute_hashes(unit, stored_deps)
    fingerprint = {
        "pdd_version": pdd_version,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "command": command,
        "prompt_hash": hashes["prompt_hash"],
        "code_hash": hashes["code_hash"],
        "example_hash": hashes["example_hash"],
        "test_hash": hashes["test_hash"],
        "test_files": hashes["test_files"],
        "include_deps": hashes["include_deps"],
    }
    return {k: fingerprint[k] for k in FIELD_ORDER}


def write_meta(meta_path: Path, content: Dict) -> None:
    """Write meta JSON byte-identically to pdd (indent=2, no trailing newline)."""
    meta_path.parent.mkdir(parents=True, exist_ok=True)
    with open(meta_path, "w", encoding="utf-8") as handle:
        json.dump(content, handle, indent=2)


def current_pdd_version() -> str:
    """Return the current tree's pdd version (``git describe`` tag, no leading v).

    setuptools_scm generates ``pdd/_version.py`` only at build time, so derive
    from git tags for a source checkout. Falls back to '0.0.0' when git tags are
    unavailable (the version field is metadata; --check does not compare it).
    """
    try:
        out = subprocess.run(
            ["git", "-C", str(REPO_ROOT), "describe", "--tags", "--abbrev=0"],
            capture_output=True,
            text=True,
            check=False,
        )
        tag = (out.stdout or "").strip()
        if tag:
            return tag[1:] if tag.startswith("v") else tag
    except (OSError, subprocess.SubprocessError):
        pass
    return "0.0.0"


# --- Unit classification -----------------------------------------------------


def classify(units: List[Unit], pddignore: List[str], waivers: Dict[str, str]):
    """Split units into (stampable, ignored, waived, no_code) buckets.

    * ignored: code path matches ``.pddignore`` (pdd never tracks these).
    * waived: basename appears in the committed waiver file.
    * no_code: code file absent and not already waived (cannot be hashed).
    * stampable: everything else.
    """
    stampable: List[Unit] = []
    ignored: List[Unit] = []
    waived: List[Unit] = []
    no_code: List[Unit] = []
    for unit in units:
        if is_pddignored(unit.code, pddignore):
            ignored.append(unit)
        elif unit.basename in waivers:
            waived.append(unit)
        elif not unit.code.exists():
            no_code.append(unit)
        else:
            stampable.append(unit)
    return stampable, ignored, waived, no_code


# --- Commands ----------------------------------------------------------------


def cmd_stamp(args: argparse.Namespace) -> int:
    """Recompute and write fingerprints for every stampable unit."""
    units = enumerate_units()
    pddignore = load_pddignore()
    waivers = load_waivers()
    stampable, ignored, waived, no_code = classify(units, pddignore, waivers)
    pdd_version = current_pdd_version()

    prev_cwd = Path.cwd()
    os.chdir(REPO_ROOT)  # include resolution + dep keys are cwd-relative
    written = 0
    try:
        for unit in stampable:
            fingerprint = build_fingerprint(unit, pdd_version)
            write_meta(unit.meta, fingerprint)
            written += 1
    finally:
        os.chdir(prev_cwd)

    print(
        f"stamped {written} units (pdd_version={pdd_version}); "
        f"ignored={len(ignored)} waived={len(waived)} no_code={len(no_code)}"
    )
    if no_code:
        print("WARNING: units with no code file (add to waivers):", file=sys.stderr)
        for unit in no_code:
            print(f"  {unit.basename} -> {unit.code.relative_to(REPO_ROOT)}", file=sys.stderr)
        return 1
    return 0


def cmd_check(args: argparse.Namespace) -> int:
    """Recompute hashes and diff against committed metas. Non-zero on drift."""
    units = enumerate_units()
    pddignore = load_pddignore()
    waivers = load_waivers()
    stampable, ignored, waived, no_code = classify(units, pddignore, waivers)

    missing: List[str] = []
    stale: List[Tuple[str, List[str]]] = []
    unwaived_no_code: List[str] = []

    prev_cwd = Path.cwd()
    os.chdir(REPO_ROOT)
    try:
        for unit in no_code:
            unwaived_no_code.append(unit.basename)
        for unit in stampable:
            existing = read_meta(unit.meta)
            if existing is None:
                missing.append(unit.basename)
                continue
            sd = existing.get("include_deps")
            stored_deps = sd if isinstance(sd, dict) else None
            current = compute_hashes(unit, stored_deps)
            diffs = [
                field
                for field in HASH_FIELDS
                if (existing.get(field) or None) != (current.get(field) or None)
            ]
            if diffs:
                stale.append((unit.basename, diffs))
    finally:
        os.chdir(prev_cwd)

    ok = not (missing or stale or unwaived_no_code)
    total = len(stampable)
    print(
        f"checked {total} stampable units; "
        f"ignored={len(ignored)} waived={len(waived)}"
    )
    if unwaived_no_code:
        print(f"\n{len(unwaived_no_code)} unit(s) have no code file and no waiver:", file=sys.stderr)
        for name in sorted(unwaived_no_code):
            print(f"  {name}", file=sys.stderr)
    if missing:
        print(f"\n{len(missing)} unit(s) missing a committed fingerprint:", file=sys.stderr)
        for name in sorted(missing):
            print(f"  {name}", file=sys.stderr)
    if stale:
        print(f"\n{len(stale)} unit(s) have stale fingerprints (run: python scripts/stamp_fingerprints.py):", file=sys.stderr)
        for name, diffs in sorted(stale):
            print(f"  {name}: {', '.join(diffs)}", file=sys.stderr)
    if ok:
        print("all fingerprints current")
        return 0
    return 1


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--check",
        action="store_true",
        help="Verify committed fingerprints are current; exit non-zero on drift.",
    )
    args = parser.parse_args(argv)
    if args.check:
        return cmd_check(args)
    return cmd_stamp(args)


if __name__ == "__main__":
    sys.exit(main())
