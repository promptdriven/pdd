"""Tests for package version reporting."""

import re
import subprocess
from pathlib import Path
from click.testing import CliRunner

import pdd
from pdd.core.cli import cli as cli_command

_PEP440_VERSION = re.compile(r"^\d+\.\d+(?:\.\d+)?(?:\.(?:dev|rc|a|b|post)\d+)?$")
_SCM_FALLBACKS = {"0.0.0", "0.0.0+unknown"}
_SEMVER_TAG = re.compile(r"^\d+\.\d+\.\d+$")


def test_package_version_is_well_formed_and_not_a_fallback():
    """__version__ must be a real PEP 440 version, not a setuptools-scm fallback."""
    v = pdd.__version__
    assert v, "pdd.__version__ is empty"
    assert v not in _SCM_FALLBACKS, (
        f"pdd.__version__ is the setuptools-scm fallback {v!r} — "
        "git tags likely not visible to the build (check actions/checkout fetch-depth)."
    )
    assert _PEP440_VERSION.match(v), f"pdd.__version__ {v!r} is not valid PEP 440."


def test_cli_version_reports_package_version():
    """`pdd --version` reports ``pdd.__version__`` (git-aligned in dev checkouts)."""
    result = CliRunner().invoke(cli_command, ["--version"])
    assert result.exit_code == 0
    assert f"version {pdd.__version__}" in result.output


def test_importing_pdd_does_not_break_importlib_metadata_distribution():
    """Importing pdd must not replace stdlib Distribution objects."""
    import importlib.metadata as im

    dist = im.distribution("pdd-cli")
    assert hasattr(dist, "metadata"), (
        "importlib.metadata.distribution must return a real Distribution after `import pdd`"
    )
    assert dist.metadata["Name"] == "pdd-cli"
    assert dist.files is not None


def test_version_matches_expected_for_current_state():
    """At a tag: version == tag. Between tags: version starts with next-patch + '.dev'."""
    repo_root = Path(__file__).resolve().parents[1]
    if not (repo_root / ".git").exists():
        return  # installed wheel outside checkout

    result = subprocess.run(
        ["git", "tag", "--list", "--merged", "HEAD", "--sort=-v:refname", "v*"],
        cwd=repo_root, capture_output=True, text=True,
    )
    if result.returncode != 0:
        return
    semver_tags = [
        t for t in result.stdout.split()
        if _SEMVER_TAG.match(t.lstrip("v"))
    ]
    if not semver_tags:
        return  # no semver tags yet
    latest = semver_tags[0].lstrip("v")

    head_tags = subprocess.check_output(
        ["git", "tag", "--points-at", "HEAD"], cwd=repo_root, text=True,
    ).split()
    at_tag = f"v{latest}" in head_tags

    if at_tag:
        assert pdd.__version__ == latest, (
            f"At tag v{latest}, expected pdd.__version__ == {latest!r}, got {pdd.__version__!r}"
        )
    else:
        parts = [int(x) for x in latest.split(".")]
        parts[-1] += 1
        expected_prefix = ".".join(str(p) for p in parts) + ".dev"
        assert pdd.__version__.startswith(expected_prefix), (
            f"Between tags after v{latest}, expected pdd.__version__ to start with "
            f"{expected_prefix!r}, got {pdd.__version__!r}"
        )


def test_pep440_version_regex_validation():
    """Verify that _PEP440_VERSION matches valid PEP 440 formats, including 2-component dev versions, and rejects invalid ones."""
    # Valid PEP 440 versions expected by the regex
    assert _PEP440_VERSION.match("0.1.dev1")
    assert _PEP440_VERSION.match("0.1.0")
    assert _PEP440_VERSION.match("1.2.3")
    assert _PEP440_VERSION.match("1.2.3.dev4")
    assert _PEP440_VERSION.match("10.20.rc2")
    
    # Invalid or unsupported versions
    assert not _PEP440_VERSION.match("abc")
    assert not _PEP440_VERSION.match("1")
