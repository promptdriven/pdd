"""Tests for scripts/sops_release_env.py."""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path
import subprocess
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

    monkeypatch.setattr(
        module.shutil, "which", lambda *_args, **_kwargs: "/opt/homebrew/bin/sops"
    )
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


def test_build_env_discards_make_controls_and_attestation_from_all_sources(monkeypatch):
    """SOPS data and ambient env cannot select credentialed executable state."""
    module = load_module()
    decrypted = {
        Path("release.sops.env"): {
            "PDS_RELEASE_TOKEN": "release-token",
            "MAKEFILES": "/decrypted/hostile.mk",
            "MAKEFLAGS": "--eval=override PDD_CLOUD_VALIDATED_SHA :=",
            "GNUMAKEFLAGS": "--include=/decrypted/hostile.mk",
            "MFLAGS": "--eval=override PDD_CLOUD_RELEASE_LEASE_OWNER :=",
            "MAKEOVERRIDES": "PDD_CLOUD_RELEASE_LEASE_REF=",
            "MAKE": "/decrypted/make",
            "SHELL": "/decrypted/shell",
            "PDD_CLOUD_RELEASE_ATTESTATION_VERSION": "attacker",
            "PDD_CLOUD_VALIDATED_SHA": "b" * 40,
            "PDD_CLOUD_RELEASE_LEASE_OWNER": "pdd-cloud-attacker",
            "PDD_CLOUD_RELEASE_LEASE_REF": "refs/attacker/lease",
            "BASH_ENV": "/decrypted/hostile-bash-env",
            "PYTHONPATH": "/decrypted/hostile-pythonpath",
            "SOPS": "/decrypted/hostile-sops",
            "CLAUDE_CLI": "/decrypted/hostile-claude",
            "PDS_CLI": "/decrypted/hostile-pds",
            "GIT_CONFIG_COUNT": "1",
            "GIT_CONFIG_KEY_0": "core.hooksPath",
            "GIT_CONFIG_VALUE_0": "/decrypted/hooks",
            "GIT_DIR": "/decrypted/repository",
            "GIT_OBJECT_DIRECTORY": "/decrypted/objects",
            "GIT_EXEC_PATH": "/decrypted/git-exec",
            "PATH": "/decrypted/bin",
            "HOME": "/decrypted/home",
            "XDG_CONFIG_HOME": "/decrypted/xdg-config",
            "LD_PRELOAD": "/decrypted/hostile.so",
            "NODE_OPTIONS": "--require /decrypted/hostile.js",
            "npm_config_registry": "https://attacker.invalid/npm",
        },
    }
    def trusted_sops_which(command: str, *, path: str) -> str:
        assert command == "sops"
        assert path == module.RELEASE_TRUSTED_PATH
        return "/usr/bin/sops"

    monkeypatch.setattr(module.shutil, "which", trusted_sops_which)
    monkeypatch.setattr(
        module,
        "decrypt_env_file",
        lambda _sops, path: decrypted[Path(path)],
    )
    for name in (
        *module.MAKE_CONTROL_NAMES,
        *module.ATTESTATION_NAMES,
        *(
            name
            for name in module.EXECUTION_CONTROL_NAMES
            if name not in {"PATH", "HOME"}
        ),
        "GIT_CONFIG_KEY_0",
        "GIT_CONFIG_VALUE_0",
        "LD_PRELOAD",
        "NODE_OPTIONS",
        "npm_config_registry",
        "XDG_CONFIG_HOME",
    ):
        monkeypatch.setenv(name, "ambient-hostile-value")

    env = module.build_env(
        SimpleNamespace(
            sops="sops",
            release_env_file="release.sops.env",
            claude_env_file=[],
            require_claude_slots="1",
            release_video="1",
        )
    )

    assert env["PDS_RELEASE_TOKEN"] == "release-token"
    assert env["PATH"] == module.RELEASE_TRUSTED_PATH
    assert env["HOME"] == module.pwd.getpwuid(module.os.getuid()).pw_dir
    for name in (
        *module.MAKE_CONTROL_NAMES,
        *module.ATTESTATION_NAMES,
        *(
            name
            for name in module.EXECUTION_CONTROL_NAMES
            if name not in {"PATH", "HOME"}
        ),
        "GIT_CONFIG_KEY_0",
        "GIT_CONFIG_VALUE_0",
        "LD_PRELOAD",
        "NODE_OPTIONS",
        "npm_config_registry",
        "XDG_CONFIG_HOME",
    ):
        assert name not in env


def test_decrypt_uses_a_clean_fixed_path_before_credentials_are_available(
    monkeypatch, tmp_path: Path
):
    """SOPS itself cannot be selected or loader-injected by ambient state."""
    module = load_module()
    encrypted = tmp_path / "release.sops.env"
    encrypted.write_text("placeholder", encoding="utf-8")
    observed: dict[str, str] = {}

    class Completed:
        returncode = 0
        stdout = "PDS_RELEASE_TOKEN=release-token\n"
        stderr = ""

    def fake_run(*_args, **kwargs):
        observed.update(kwargs["env"])
        return Completed()

    monkeypatch.setenv("PATH", "/hostile/bin")
    monkeypatch.setenv("LD_PRELOAD", "/hostile/library.so")
    monkeypatch.setenv("NODE_OPTIONS", "--require /hostile/module.js")
    monkeypatch.setenv("HOME", "/hostile/home")
    monkeypatch.setattr(module.subprocess, "run", fake_run)

    assert module.decrypt_env_file("/usr/bin/sops", encrypted) == {
        "PDS_RELEASE_TOKEN": "release-token"
    }
    assert observed["PATH"] == module.RELEASE_TRUSTED_PATH
    assert "LD_PRELOAD" not in observed
    assert "NODE_OPTIONS" not in observed
    assert observed["HOME"] == module.pwd.getpwuid(module.os.getuid()).pw_dir


def test_actual_make_sops_recursion_preserves_attestation_command_line_origin(
    tmp_path: Path,
) -> None:
    """The public Makefile's SOPS recursion ignores hostile env and plaintext."""
    fake_sops = tmp_path / "sops"
    decrypted = tmp_path / "decrypted.env"
    hostile_include = tmp_path / "hostile.mk"
    release_env = tmp_path / "release.sops.env"
    hostile_include.write_text(
        "override PDD_CLOUD_RELEASE_ATTESTATION_VERSION :=\n"
        "override PDD_CLOUD_VALIDATED_SHA :=\n"
        "override PDD_CLOUD_RELEASE_LEASE_OWNER :=\n"
        "override PDD_CLOUD_RELEASE_LEASE_REF :=\n",
        encoding="utf-8",
    )
    decrypted.write_text(
        "\n".join(
            (
                f"MAKEFILES={hostile_include}",
                "MAKEFLAGS=--eval=override PDD_CLOUD_VALIDATED_SHA :=",
                f"GNUMAKEFLAGS=--include={hostile_include}",
                "MFLAGS=--eval=override PDD_CLOUD_RELEASE_LEASE_OWNER :=",
                "MAKEOVERRIDES=PDD_CLOUD_RELEASE_LEASE_REF=",
                "MAKE=/tmp/hostile-make",
                "SHELL=/tmp/hostile-shell",
                "PDD_CLOUD_RELEASE_ATTESTATION_VERSION=attacker",
                f"PDD_CLOUD_VALIDATED_SHA={'b' * 40}",
                "PDD_CLOUD_RELEASE_LEASE_OWNER=pdd-cloud-attacker",
                "PDD_CLOUD_RELEASE_LEASE_REF=refs/attacker/lease",
            )
        )
        + "\n",
        encoding="utf-8",
    )
    release_env.write_text("unused\n", encoding="utf-8")
    fake_sops.write_text(
        "#!/usr/bin/env bash\nset -eu\ncat \"$FAKE_SOPS_DECRYPTED_ENV\"\n",
        encoding="utf-8",
    )
    fake_sops.chmod(0o755)
    hostile_pythonpath = tmp_path / "hostile-pythonpath"
    hostile_pythonpath.mkdir()
    pythonpath_marker = tmp_path / "pythonpath-executed"
    (hostile_pythonpath / "sitecustomize.py").write_text(
        f"from pathlib import Path\nPath({str(pythonpath_marker)!r}).touch()\n",
        encoding="utf-8",
    )

    sha = "a" * 40
    result = subprocess.run(
        [
            "make",
            "-C",
            str(SCRIPT_PATH.parents[1]),
            "--no-print-directory",
            "test-release-sops-attestation-recursion",
            f"SOPS={fake_sops}",
            f"SOPS_RELEASE_ENV_FILE={release_env}",
            f"SOPS_TEST_MAKEFILES={hostile_include}",
            "SOPS_TEST_MAKEFLAGS=--eval=override PDD_CLOUD_VALIDATED_SHA :=",
            f"SOPS_TEST_GNUMAKEFLAGS=--include={hostile_include}",
            "SOPS_TEST_MFLAGS=--eval=override PDD_CLOUD_RELEASE_LEASE_OWNER :=",
            "SOPS_TEST_MAKEOVERRIDES=PDD_CLOUD_RELEASE_LEASE_REF=",
            "PDD_CLOUD_RELEASE_ATTESTATION_VERSION=2",
            f"PDD_CLOUD_VALIDATED_SHA={sha}",
            "PDD_CLOUD_RELEASE_LEASE_OWNER=pdd-cloud-owner-a",
            "PDD_CLOUD_RELEASE_LEASE_REF=refs/pdd-cloud/release-lease",
        ],
        env={
            **os.environ,
            "FAKE_SOPS_DECRYPTED_ENV": str(decrypted),
            "PYTHONPATH": str(hostile_pythonpath),
        },
        text=True,
        capture_output=True,
        check=False,
    )

    assert result.returncode == 0, result.stderr
    assert not pythonpath_marker.exists(), "credentialed release Python honored PYTHONPATH"
