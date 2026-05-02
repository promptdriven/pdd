"""Tests for scripts/copy_package_data_to_public.py."""

from __future__ import annotations

import importlib.util
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_PATH = REPO_ROOT / "scripts" / "copy_package_data_to_public.py"


def _load_module():
    spec = importlib.util.spec_from_file_location(
        "copy_package_data_to_public",
        SCRIPT_PATH,
    )
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def _git(repo: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", "-C", str(repo), *args],
        check=True,
        capture_output=True,
        text=True,
    )


def test_sync_config_includes_public_ci_dependencies():
    module = _load_module()

    config = module.load_sync_config(str(REPO_ROOT / ".sync-config.yml"))

    assert "scripts/ci_detect_changed_modules.py" in config["shared"]
    assert "utils/mcp/prompts/" in config["shared"]


def test_sync_deletions_remove_stale_gitlinks_under_directory_patterns(tmp_path):
    module = _load_module()
    source = tmp_path / "source"
    dest = tmp_path / "dest"

    (source / "examples/hello/src").mkdir(parents=True)
    (source / "examples/hello/src/hello.py").write_text("print('hello')\n")
    (source / "scripts").mkdir()
    (source / "scripts/ci_detect_changed_modules.py").write_text("# helper\n")
    (source / "utils/mcp/prompts").mkdir(parents=True)
    (source / "utils/mcp/prompts/generate_prompt.prompt").write_text("prompt\n")
    (source / "utils/mcp/prompts/main_python.prompt").write_text("python\n")

    dest.mkdir()
    _git(dest, "init", "-q")
    _git(dest, "config", "user.email", "test@example.com")
    _git(dest, "config", "user.name", "Test User")
    (dest / "examples/hello").mkdir(parents=True)
    (dest / "examples/hello/old.txt").write_text("stale\n")
    _git(dest, "add", "examples/hello/old.txt")
    _git(
        dest,
        "update-index",
        "--add",
        "--cacheinfo",
        "160000,42bf4d61876814e52efdac8271fb1dc3db786400,examples/hello/repo_root",
    )
    _git(dest, "commit", "-qm", "seed public repo")

    copied, deleted = module.copy_from_sync_config(
        {
            "shared": [
                "examples/",
                "scripts/ci_detect_changed_modules.py",
                "utils/mcp/prompts/",
            ],
            "exclude": [],
        },
        sections=["shared"],
        exclude_section="exclude",
        dest=str(dest),
        project_root=str(source),
        sync_deletions=True,
    )

    assert copied == 4
    assert deleted == 2
    assert (dest / "examples/hello/src/hello.py").is_file()
    assert (dest / "scripts/ci_detect_changed_modules.py").is_file()
    assert (dest / "utils/mcp/prompts/generate_prompt.prompt").is_file()
    assert not (dest / "examples/hello/old.txt").exists()
    assert "examples/hello/repo_root" not in _git(dest, "ls-files", "-s").stdout
