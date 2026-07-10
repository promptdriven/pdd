# Hidden verifier for scenario pdd-language-extensions (design §4.4).
#
# Pins the duplicate-row contract the visible suite deliberately leaves
# open: when a language appears in language_format.csv more than once, the
# FIRST row wins deterministically.
#
# Adversarial-hardening (2026-07-07 review): the verifier must not trust any
# agent-controllable artifact. It loads the agent's FIXED module against a
# fresh, crafted CSV containing TWO duplicated languages — one (`YAML`) named
# in task.md and one (`Zeta`) that is not — and checks first-row-wins through
# the PUBLIC bundled_extension only. This defeats (a) deleting the duplicate
# row from the shipped CSV, (b) hardcoding `yaml -> yml`, and (c) renaming
# private module internals (nothing private is referenced). This tree is
# physically separate from the core and never enters the agent sandbox.

import importlib.util
import shutil
import tempfile
from pathlib import Path

import pdd.language_extensions as _agent_module

_AGENT_SOURCE = Path(_agent_module.__file__)

# Two duplicated languages; first row must win for BOTH. Zeta is absent from
# task.md, so a YAML-only hardcode cannot satisfy it.
_FIXTURE_CSV = (
    "language,comment,extension,run_command,run_test_command,outputs\n"
    "YAML,#,.yml,,,code\n"
    "YAML,#,.yaml,,,code\n"
    "Zeta,#,.z1,,,code\n"
    "Zeta,#,.z2,,,code\n"
    "Python,#,.py,,,code\n"
    "Makefile,#,,,,code\n"
)


def _load_agent_module_with_csv(csv_text: str):
    """Load the agent's fixed source fresh, reading a crafted data CSV.

    The module resolves its CSV as ``Path(__file__).parent/"data"/...``, so
    placing a copy of the agent's source beside a crafted ``data/`` directory
    exercises the agent's real parsing logic against inputs we control —
    without depending on any private name in the module.
    """
    tmp = Path(tempfile.mkdtemp())
    pkg = tmp / "pkg_le_fixture"
    (pkg / "data").mkdir(parents=True)
    shutil.copy(_AGENT_SOURCE, pkg / "language_extensions.py")
    (pkg / "data" / "language_format.csv").write_text(csv_text, encoding="utf-8")
    spec = importlib.util.spec_from_file_location(
        "le_fixture", pkg / "language_extensions.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_first_row_wins_for_every_duplicated_language():
    module = _load_agent_module_with_csv(_FIXTURE_CSV)
    # First row wins for the task.md-named duplicate AND the unnamed one.
    assert module.bundled_extension("YAML") == "yml"
    assert module.bundled_extension("yaml") == "yml"
    assert module.bundled_extension("Zeta") == "z1"
    assert module.bundled_extension("zeta") == "z1"


def test_singleton_and_extensionless_and_unknown_unchanged():
    module = _load_agent_module_with_csv(_FIXTURE_CSV)
    assert module.bundled_extension("Python") == "py"
    assert module.bundled_extension("Makefile") == ""
    assert module.bundled_extension("NoSuchLanguageXyz") is None


def test_shipped_csv_yaml_also_resolves_first_row():
    # Belt-and-suspenders against the shipped CSV specifically, through the
    # public API, using the module as imported on the agent's PYTHONPATH.
    assert _agent_module.bundled_extension("YAML") == "yml"
