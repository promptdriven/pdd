"""Tests for scripts/stamp_fingerprints.py — the .pdd/meta fingerprint stamper.

The load-bearing guarantee is hash parity with the pdd CLI: a fingerprint the
stamper writes must equal what ``pdd sync`` would compute, or sync sees phantom
drift. ``test_hash_parity_with_pdd`` pins the vendored hashing against pdd's own
functions for representative units (flat, subdir, architecture-overridden, and
ambiguous-leaf). Exhaustive parity across all units is enforced by the stamper's
own ``--check`` on the committed tree (``test_check_passes_on_committed_tree``).
"""
import importlib.util
import json
import logging
import os
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
STAMPER_PATH = REPO_ROOT / "scripts" / "stamp_fingerprints.py"


def _load_stamper():
    spec = importlib.util.spec_from_file_location("stamp_fingerprints", STAMPER_PATH)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


stamp = _load_stamper()


# Representative units: flat, each subdir context, the two architecture.json
# code-path overrides (checkup_simplify -> pdd/checkup_simplify.py,
# remote_session -> pdd/remote_session.py), and the two ambiguous leaves
# (core/cli, commands/gate) whose example/test stems are disambiguated.
_SAMPLE_UNITS = [
    "sync_orchestration",
    "code_generator",
    "commands/which",
    "server/executor",
    "server/routes/auth",
    "core/cloud",
    "commands/checkup_simplify",
    "core/remote_session",
    "core/cli",
    "commands/gate",
]


def test_stamper_is_stdlib_only():
    """The stamper must not import pdd (it runs offline in CI / the nightly runner)."""
    import ast

    tree = ast.parse(STAMPER_PATH.read_text(encoding="utf-8"))
    imported = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported.update(alias.name.split(".")[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imported.add(node.module.split(".")[0])
    assert "pdd" not in imported


def test_write_meta_byte_format(tmp_path):
    """Meta JSON is indent=2, no trailing newline, Fingerprint dataclass key order."""
    content = {k: None for k in stamp.FIELD_ORDER}
    content["command"] = "fix"
    content["test_files"] = {}
    content["include_deps"] = {}
    out = tmp_path / "x.json"
    stamp.write_meta(out, content)
    raw = out.read_text(encoding="utf-8")
    assert not raw.endswith("\n")  # matches pdd's json.dump(indent=2) writers
    assert list(json.loads(raw).keys()) == list(stamp.FIELD_ORDER)
    assert '\n  "timestamp"' in raw  # indent=2


@pytest.mark.parametrize("basename", _SAMPLE_UNITS)
def test_hash_parity_with_pdd(basename):
    """Stamper hashes must equal pdd's calculate_current_hashes for each unit."""
    logging.disable(logging.CRITICAL)
    from pdd.sync_determine_operation import (
        get_pdd_file_paths,
        calculate_current_hashes,
    )

    prev = Path.cwd()
    os.chdir(REPO_ROOT)  # cwd-relative include resolution for both sides
    try:
        unit = stamp.Unit(basename, REPO_ROOT / "pdd" / "prompts" / f"{basename}_python.prompt")
        existing = stamp.read_meta(unit.meta)
        stored_deps = None
        if existing is not None and isinstance(existing.get("include_deps"), dict):
            stored_deps = existing["include_deps"]
        mine = stamp.compute_hashes(unit, stored_deps)
        paths = get_pdd_file_paths(basename, "python")
        theirs = calculate_current_hashes(paths, stored_include_deps=stored_deps)
    finally:
        os.chdir(prev)

    for field in stamp.HASH_FIELDS:
        assert (mine.get(field) or None) == (theirs.get(field) or None), (
            f"{basename}.{field} diverged from pdd"
        )


def test_check_passes_on_committed_tree():
    """--check exits 0 on the current tree (acceptance: fresh clone check is green)."""
    assert stamp.main(["--check"]) == 0


def test_check_detects_tampered_meta():
    """A hand-edited (tampered) fingerprint must fail --check (acceptance #5)."""
    units = stamp.enumerate_units()
    stampable, _ig, _wv, _nc = stamp.classify(
        units, stamp.load_pddignore(), stamp.load_waivers()
    )
    target = next(u for u in stampable if u.meta.exists())
    original = target.meta.read_bytes()
    try:
        data = json.loads(original)
        data["code_hash"] = "0" * 64  # simulate a hand-edit
        target.meta.write_text(json.dumps(data, indent=2), encoding="utf-8")
        assert stamp.main(["--check"]) == 1
    finally:
        target.meta.write_bytes(original)
    # tree restored -> check green again
    assert stamp.main(["--check"]) == 0


def test_waived_and_ignored_units_excluded():
    """Waived (ambiguous / no-code) and .pddignored units are not required to stamp."""
    units = stamp.enumerate_units()
    stampable, ignored, waived, no_code = stamp.classify(
        units, stamp.load_pddignore(), stamp.load_waivers()
    )
    waived_names = {u.basename for u in waived}
    assert {"cli", "gate", "core_dump_smoke", "server/routes/session"} <= waived_names
    assert not no_code  # every no-code unit is explicitly waived
    ignored_names = {u.basename for u in ignored}
    # __init__ prompts and architecture_registry are .pddignored
    assert "architecture_registry" in ignored_names
    assert any(n.endswith("__init__") for n in ignored_names)
    # stampable and waived/ignored are disjoint
    stampable_names = {u.basename for u in stampable}
    assert stampable_names.isdisjoint(waived_names)


def test_every_stampable_unit_has_committed_meta():
    """Coverage: every stampable unit has a meta on disk (acceptance #2)."""
    units = stamp.enumerate_units()
    stampable, _ig, _wv, _nc = stamp.classify(
        units, stamp.load_pddignore(), stamp.load_waivers()
    )
    missing = [u.basename for u in stampable if not u.meta.exists()]
    assert not missing, f"units missing committed meta: {missing}"
