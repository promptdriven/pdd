"""Tests for package version reporting."""

from importlib.metadata import version as metadata_version
from pathlib import Path
import tomllib

from click.testing import CliRunner

import pdd
from pdd.core.cli import cli as cli_command


def test_package_version_matches_distribution_metadata():
    """pdd.__version__ should report the installed pdd-cli version."""
    project_root = Path(__file__).resolve().parents[1]
    pyproject = tomllib.loads((project_root / "pyproject.toml").read_text())
    expected_version = pyproject["project"]["version"]

    assert metadata_version("pdd-cli") == expected_version
    assert pdd.__version__ == expected_version


def test_cli_version_reports_distribution_metadata():
    """`pdd --version` should report the installed pdd-cli version."""
    expected_version = metadata_version("pdd-cli")

    result = CliRunner().invoke(cli_command, ["--version"])

    assert result.exit_code == 0
    assert f"version {expected_version}" in result.output
