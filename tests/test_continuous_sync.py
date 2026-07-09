"""Tests for pdd.continuous_sync — the shared reconcile/stamp core (issue #1927).

Covers the four reconcile verdicts (current / stamped / conflict / unbaselined),
the --accept-current and --backfill stamping scopes, the issue #884 --json verdict
shape, idempotency (second run is a no-op; a single changed unit touches only its
own fingerprint), the two resolution regressions the #1954 command got wrong
(commands/firecrawl, core/remote_session vs remote_session), and script<->command
parity on the committed tree.
"""
import importlib.util
import json
from pathlib import Path

import pytest
from click.testing import CliRunner

from pdd import continuous_sync as cs
from pdd.commands.reconcile import reconcile

REPO_ROOT = Path(__file__).resolve().parent.parent
STAMPER_PATH = REPO_ROOT / "scripts" / "stamp_fingerprints.py"

_PDDRC = """version: "1.0"
contexts:
  default:
    paths: ["**"]
    defaults:
      generate_output_path: "pdd/"
      test_output_path: "tests/"
      example_output_path: "context/"
      default_language: "python"
"""


# --- Fixture repo helpers ----------------------------------------------------


def _make_repo(tmp_path: Path) -> Path:
    (tmp_path / ".pddrc").write_text(_PDDRC, encoding="utf-8")
    for sub in ("pdd/prompts", "context", "tests", ".pdd/meta"):
        (tmp_path / sub).mkdir(parents=True, exist_ok=True)
    return tmp_path


def _write_unit(  # pylint: disable=too-many-arguments
    root: Path,
    basename: str,
    *,
    prompt: str = "describe the module\n",
    code: str = "VALUE = 1\n",
    example: str | None = None,
    test: str | None = None,
) -> str:
    """Write a flat unit's prompt/code (+optional example/test) into ``root``."""
    (root / "pdd" / "prompts" / f"{basename}_python.prompt").write_text(
        prompt, encoding="utf-8"
    )
    (root / "pdd" / f"{basename}.py").write_text(code, encoding="utf-8")
    if example is not None:
        (root / "context" / f"{basename}_example.py").write_text(example, encoding="utf-8")
    if test is not None:
        (root / "tests" / f"test_{basename}.py").write_text(test, encoding="utf-8")
    return basename


def _classify_one(root: Path, basename: str) -> dict:
    report = cs.build_report(consumer="test", root=root, modules=[basename])
    units = report["units"]
    assert units, f"no unit classified for {basename}"
    return units[0]


# --- Four statuses -----------------------------------------------------------


def test_status_current(tmp_path):
    """A baselined, unmodified unit is IN_SYNC / status current."""
    root = _make_repo(tmp_path)
    _write_unit(root, "alpha")
    cs.stamp_units(cs.resolve_units(root), root)  # baseline
    verdict = _classify_one(root, "alpha")
    assert verdict["classification"] == "IN_SYNC"
    assert verdict["status"] == "current"
    assert verdict["remediation"] == ""


def test_status_stamped_on_heal(tmp_path):
    """Single-sided drift is stamped by --heal and becomes current."""
    root = _make_repo(tmp_path)
    _write_unit(root, "alpha", code="VALUE = 1\n")
    cs.stamp_units(cs.resolve_units(root), root)
    (root / "pdd" / "alpha.py").write_text("VALUE = 2  # hotfix\n", encoding="utf-8")

    drift = _classify_one(root, "alpha")
    assert drift["classification"] == "CODE_CHANGED"
    assert drift["status"] == "stale"
    assert drift["remediation"] == "pdd update alpha"

    report = cs.build_report(consumer="test", root=root, modules=["alpha"], heal=True)
    assert report["stamped"] == ["alpha"]
    assert report["units"][0]["status"] == "stamped"
    # Re-classify: now current.
    assert _classify_one(root, "alpha")["classification"] == "IN_SYNC"


def test_status_conflict_not_stamped_without_accept(tmp_path):
    """Prompt AND code both moved is CONFLICT; --heal must not stamp it."""
    root = _make_repo(tmp_path)
    _write_unit(root, "alpha", prompt="v0\n", code="VALUE = 1\n")
    cs.stamp_units(cs.resolve_units(root), root)
    (root / "pdd" / "prompts" / "alpha_python.prompt").write_text("v1\n", encoding="utf-8")
    (root / "pdd" / "alpha.py").write_text("VALUE = 2\n", encoding="utf-8")

    verdict = _classify_one(root, "alpha")
    assert verdict["classification"] == "CONFLICT"
    assert verdict["status"] == "conflict"
    assert "--accept-current" in verdict["remediation"]

    # --heal alone leaves a conflict untouched.
    healed = cs.build_report(consumer="test", root=root, modules=["alpha"], heal=True)
    assert not healed["stamped"]
    assert _classify_one(root, "alpha")["classification"] == "CONFLICT"


def test_status_unbaselined_not_stamped_without_backfill(tmp_path):
    """A unit with no fingerprint is UNBASELINED; --heal must not stamp it."""
    root = _make_repo(tmp_path)
    _write_unit(root, "alpha")  # never baselined -> no meta

    verdict = _classify_one(root, "alpha")
    assert verdict["classification"] == "UNBASELINED"
    assert verdict["status"] == "unbaselined"
    assert "--backfill" in verdict["remediation"]

    healed = cs.build_report(consumer="test", root=root, modules=["alpha"], heal=True)
    assert not healed["stamped"]
    assert _classify_one(root, "alpha")["classification"] == "UNBASELINED"


# --- Stamping scopes ---------------------------------------------------------


def test_accept_current_stamps_only_conflict(tmp_path):
    """--accept-current stamps CONFLICT units and nothing else (no --heal)."""
    root = _make_repo(tmp_path)
    _write_unit(root, "conf", prompt="v0\n", code="C0\n")
    _write_unit(root, "drift", code="D0\n")
    cs.stamp_units(cs.resolve_units(root), root)
    # conf: both sides move -> CONFLICT; drift: code only -> CODE_CHANGED
    (root / "pdd" / "prompts" / "conf_python.prompt").write_text("v1\n", encoding="utf-8")
    (root / "pdd" / "conf.py").write_text("C1\n", encoding="utf-8")
    (root / "pdd" / "drift.py").write_text("D1\n", encoding="utf-8")

    report = cs.build_report(consumer="test", root=root, accept_current=True)
    assert report["stamped"] == ["conf"]  # drift NOT stamped (heal not set)
    assert _classify_one(root, "drift")["classification"] == "CODE_CHANGED"


def test_backfill_stamps_only_unbaselined(tmp_path):
    """--backfill stamps UNBASELINED units and nothing else (no --heal)."""
    root = _make_repo(tmp_path)
    _write_unit(root, "fresh")  # unbaselined
    _write_unit(root, "drift", code="D0\n")
    # baseline only 'drift', then drift it
    cs.stamp_units([cs.resolve_unit("drift", root)], root)
    (root / "pdd" / "drift.py").write_text("D1\n", encoding="utf-8")

    report = cs.build_report(consumer="test", root=root, backfill=True)
    assert report["stamped"] == ["fresh"]  # drift NOT stamped
    assert _classify_one(root, "fresh")["classification"] == "IN_SYNC"
    assert _classify_one(root, "drift")["classification"] == "CODE_CHANGED"


# --- issue #884 verdict shape ------------------------------------------------


def test_json_verdict_shape(tmp_path):
    """Every verdict carries the #884 keys; report is JSON-serialisable."""
    root = _make_repo(tmp_path)
    _write_unit(root, "alpha")
    cs.stamp_units(cs.resolve_units(root), root)
    (root / "pdd" / "prompts" / "alpha_python.prompt").write_text("changed\n", encoding="utf-8")

    report = cs.build_report(consumer="test", root=root, modules=["alpha"])
    json.dumps(report)  # must not raise
    verdict = report["units"][0]
    for key in ("status", "reasons", "affected_artifacts", "remediation", "classification"):
        assert key in verdict
    assert verdict["classification"] == "PROMPT_CHANGED"
    assert verdict["affected_artifacts"] == ["prompt"]
    assert isinstance(verdict["reasons"], list) and verdict["reasons"]
    assert verdict["remediation"] == "pdd sync alpha"


# --- Idempotency -------------------------------------------------------------


def test_second_stamp_run_is_noop(tmp_path):
    """A repo-wide stamp writes changed units once; the second run writes nothing."""
    root = _make_repo(tmp_path)
    _write_unit(root, "alpha", code="A0\n")
    _write_unit(root, "beta", code="B0\n")
    cs.stamp_units(cs.resolve_units(root), root)  # baseline both
    (root / "pdd" / "alpha.py").write_text("A1\n", encoding="utf-8")

    first = cs.stamp_units(cs.resolve_units(root), root)
    assert first == ["alpha"]
    second = cs.stamp_units(cs.resolve_units(root), root)
    assert not second  # pdd#1932 DoD: second consecutive run is a no-op


def test_single_unit_touch(tmp_path):
    """Stamping touches only the changed unit's fingerprint file."""
    root = _make_repo(tmp_path)
    for name in ("alpha", "beta", "gamma"):
        _write_unit(root, name, code=f"{name} = 0\n")
    cs.stamp_units(cs.resolve_units(root), root)

    names = ("alpha", "beta", "gamma")
    metas = {name: root / ".pdd" / "meta" / f"{name}_python.json" for name in names}
    before = {name: path.read_bytes() for name, path in metas.items()}
    (root / "pdd" / "beta.py").write_text("beta = 999\n", encoding="utf-8")

    written = cs.stamp_units(cs.resolve_units(root), root)
    assert written == ["beta"]
    assert metas["alpha"].read_bytes() == before["alpha"]  # untouched
    assert metas["gamma"].read_bytes() == before["gamma"]  # untouched
    assert metas["beta"].read_bytes() != before["beta"]  # rewritten


# --- Resolution regressions (real repo) --------------------------------------


@pytest.mark.parametrize(
    "basename", ["commands/firecrawl", "core/remote_session", "remote_session"]
)
def test_resolution_regression_units_are_current(basename):
    """The units #1954 mis-resolved now classify IN_SYNC on the committed tree.

    commands/firecrawl (underscore-basename resolved a stray flat test) and the
    core/remote_session vs remote_session leaf collision were the two false
    positives; correct resolution clears both.
    """
    verdict = _classify_one(REPO_ROOT, basename)
    assert verdict["classification"] == "IN_SYNC", verdict["reason"]


# --- Script <-> command parity ----------------------------------------------


def _load_stamper():
    spec = importlib.util.spec_from_file_location("stamp_fingerprints", STAMPER_PATH)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_script_and_command_agree_on_clean_tree():
    """The CI stamper and `pdd reconcile --check` agree the committed tree is current."""
    assert cs.run_check(root=REPO_ROOT).ok is True
    stamper = _load_stamper()
    assert stamper.main(["--check"]) == 0


# --- reconcile CLI surface ---------------------------------------------------


def test_cli_check_exit_codes(tmp_path, monkeypatch):
    """`pdd reconcile --check` exits 0 when current, non-zero on drift (no writes)."""
    root = _make_repo(tmp_path)
    _write_unit(root, "alpha", code="A0\n")
    cs.stamp_units(cs.resolve_units(root), root)
    monkeypatch.chdir(root)
    runner = CliRunner()

    ok = runner.invoke(reconcile, ["--check"])
    assert ok.exit_code == 0, ok.output
    assert "all fingerprints current" in ok.output

    (root / "pdd" / "alpha.py").write_text("A1\n", encoding="utf-8")
    drifted = runner.invoke(reconcile, ["--check"])
    assert drifted.exit_code == 1, drifted.output


def test_cli_json_basename(tmp_path, monkeypatch):
    """`pdd reconcile BASENAME --json` reports only that unit, with the #884 shape."""
    root = _make_repo(tmp_path)
    _write_unit(root, "alpha")
    _write_unit(root, "beta")
    cs.stamp_units(cs.resolve_units(root), root)
    monkeypatch.chdir(root)

    result = CliRunner().invoke(reconcile, ["alpha", "--json"])
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert [u["basename"] for u in payload["units"]] == ["alpha"]
    assert payload["units"][0]["status"] == "current"
