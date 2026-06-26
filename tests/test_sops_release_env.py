"""Tests for scripts/sops_release_env.py."""

from __future__ import annotations

import importlib.util
from pathlib import Path
from types import SimpleNamespace


SCRIPT_PATH = Path(__file__).resolve().parents[1] / "scripts" / "sops_release_env.py"


def load_module():
    """Load the script as an importable module for unit tests."""
    spec = importlib.util.spec_from_file_location("sops_release_env", SCRIPT_PATH)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_parse_dotenv_handles_export_quotes_and_sops_metadata():
    """The dotenv parser handles the syntax used by encrypted release files."""
    module = load_module()

    parsed = module.parse_dotenv(
        """
        # comment
        export PDS_RELEASE_TOKEN='release-token'
        CLAUDE_CODE_OAUTH_TOKEN="oauth-token"
        EMPTY=
        sops_mac=encrypted-metadata
        """
    )

    assert parsed == {
        "PDS_RELEASE_TOKEN": "release-token",
        "CLAUDE_CODE_OAUTH_TOKEN": "oauth-token",
        "EMPTY": "",
    }


def test_build_env_maps_distinct_claude_tokens_to_compact_slots(monkeypatch):
    """Distinct Claude OAuth tokens fill numbered slots without gaps."""
    module = load_module()

    decrypted = {
        Path("release.sops.env"): {"PDS_RELEASE_TOKEN": "release-token"},
        Path("dev.sops.env"): {"CLAUDE_CODE_OAUTH_TOKEN": "dev-token"},
        Path("staging.sops.env"): {"CLAUDE_CODE_OAUTH_TOKEN": "dev-token"},
        Path("prod.sops.env"): {"CLAUDE_CODE_OAUTH_TOKEN": "prod-token"},
    }

    monkeypatch.setattr(module.shutil, "which", lambda _: "/opt/homebrew/bin/sops")
    monkeypatch.setattr(
        module,
        "decrypt_env_file",
        lambda _sops, path: decrypted[Path(path)],
    )
    monkeypatch.setenv("CLAUDE_CODE_OAUTH_TOKEN_1", "old-token")
    monkeypatch.setenv("CLAUDE_CODE_OAUTH_TOKEN_2", "old-token")
    monkeypatch.setenv("CLAUDE_CODE_OAUTH_TOKEN_3", "old-token")

    env = module.build_env(
        SimpleNamespace(
            sops="sops",
            release_env_file="release.sops.env",
            claude_env_file=["dev.sops.env", "staging.sops.env", "prod.sops.env"],
            require_claude_slots="1",
            release_video="1",
        )
    )

    assert env["PDS_RELEASE_TOKEN"] == "release-token"
    assert env["CLAUDE_CODE_OAUTH_TOKEN_1"] == "dev-token"
    assert env["CLAUDE_CODE_OAUTH_TOKEN_2"] == "prod-token"
    assert "CLAUDE_CODE_OAUTH_TOKEN_3" not in env
    assert env["REQUIRE_CLAUDE_OAUTH_SLOTS"] == "1"
    assert env["RELEASE_VIDEO"] == "1"
