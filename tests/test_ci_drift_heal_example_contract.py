"""Execution contract for the generated ``ci_drift_heal`` example."""

# pylint: disable=duplicate-code

from __future__ import annotations

import ast
import hashlib
import importlib.util
import inspect
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from types import ModuleType
from types import SimpleNamespace

import pytest

from pdd.ci_drift_heal import main as ci_drift_heal_main


ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "context" / "ci_drift_heal_example.py"
PROMPT = ROOT / "pdd" / "prompts" / "ci_drift_heal_python.prompt"


def _load_example() -> ModuleType:
    spec = importlib.util.spec_from_file_location("ci_drift_heal_example", EXAMPLE)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _tree_digest(root: Path) -> dict[str, str]:
    """Return a stable digest of files outside Git's administrative data."""
    return {
        path.relative_to(root).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(root.rglob("*"))
        if path.is_file() and ".git" not in path.relative_to(root).parts
    }


def _git_admin_snapshot(
    repo: Path, git_executable: str = "git"
) -> dict[str, object]:
    """Capture refs, config, HEAD, and every Git administrative file."""
    def git(*args: str) -> str:
        return subprocess.run(
            [git_executable, *args],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        ).stdout

    return {
        "head": git("rev-parse", "HEAD"),
        "refs": git("for-each-ref", "--format=%(refname) %(objectname)"),
        "config": git("config", "--local", "--null", "--list"),
        "files": _tree_digest(repo / ".git"),
    }


def _digest_admin_file(path: Path) -> str:
    """Hash a Git admin file or its symlink target without following links."""
    if path.is_symlink():
        return f"symlink:{os.readlink(path)}"
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _git_admin_files(git_dir: Path, common_dir: Path) -> dict[str, str]:
    """Hash applicable worktree/common admin state without traversing objects."""
    files: dict[str, str] = {}

    def add_tree(label: str, root: Path, relative: Path) -> None:
        target = root / relative
        if target.is_file() or target.is_symlink():
            files[f"{label}/{relative.as_posix()}"] = _digest_admin_file(target)
        elif target.is_dir():
            for path in sorted(target.rglob("*")):
                if path.is_file() or path.is_symlink():
                    rel = path.relative_to(root).as_posix()
                    files[f"{label}/{rel}"] = _digest_admin_file(path)

    if git_dir != common_dir:
        for path in sorted(git_dir.rglob("*")):
            if path.is_file() or path.is_symlink():
                rel = path.relative_to(git_dir).as_posix()
                files[f"worktree/{rel}"] = _digest_admin_file(path)
    else:
        for name in (
            "HEAD", "index", "ORIG_HEAD", "MERGE_HEAD", "CHERRY_PICK_HEAD",
            "REVERT_HEAD", "BISECT_LOG", "config.worktree",
        ):
            add_tree("worktree", git_dir, Path(name))

    for name in ("HEAD", "config", "packed-refs", "shallow", "refs", "logs"):
        add_tree("common", common_dir, Path(name))
    return files


def _source_checkout_snapshot(repo: Path) -> dict[str, object]:
    """Capture linked-worktree-aware source Git and administrative state."""
    # pylint: disable=too-many-locals
    def git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["git", *args],
            cwd=repo,
            check=check,
            capture_output=True,
            text=True,
        )

    git_dir_raw = git("rev-parse", "--git-dir").stdout.strip()
    common_dir_raw = git("rev-parse", "--git-common-dir").stdout.strip()

    def resolved(raw: str) -> Path:
        path = Path(raw)
        return (path if path.is_absolute() else repo / path).resolve()

    git_dir = resolved(git_dir_raw)
    common_dir = resolved(common_dir_raw)
    marker = repo / ".git"
    marker_state: dict[str, str] = {"kind": "missing"}
    if marker.is_file() or marker.is_symlink():
        marker_state = {"kind": "file", "digest": _digest_admin_file(marker)}
    elif marker.is_dir():
        marker_state = {"kind": "directory", "path": str(marker.resolve())}

    worktree_config = git(
        "config", "--worktree", "--null", "--list", check=False
    )
    return {
        "marker": marker_state,
        "git_dir": str(git_dir),
        "common_dir": str(common_dir),
        "head": git("rev-parse", "HEAD").stdout,
        "head_ref": git("symbolic-ref", "-q", "HEAD", check=False).stdout,
        "refs": git("for-each-ref", "--format=%(refname) %(objectname)").stdout,
        "local_config": git("config", "--local", "--null", "--list").stdout,
        "worktree_config": (worktree_config.returncode, worktree_config.stdout),
        "status": git("status", "--porcelain", "--untracked-files=all").stdout,
        "admin_files": _git_admin_files(git_dir, common_dir),
    }


def _write_git_shim(path: Path, log_path: Path, real_git: str) -> None:
    """Write the mutation-rejecting Git shim used by contract tests."""
    path.write_text(
        f"#!{sys.executable}\n"
        "import os\n"
        "import sys\n"
        f"REAL_GIT = {real_git!r}\n"
        f"LOG_PATH = {str(log_path)!r}\n"
        "args = sys.argv[1:]\n"
        "value_options = {\n"
        "    '-C', '-c', '--git-dir', '--work-tree', '--namespace',\n"
        "    '--config-env', '--exec-path', '--super-prefix',\n"
        "}\n"
        "flag_options = {\n"
        "    '--bare', '--no-pager', '--paginate', '--literal-pathspecs',\n"
        "    '--no-literal-pathspecs', '--glob-pathspecs', '--noglob-pathspecs',\n"
        "    '--icase-pathspecs', '--no-replace-objects', '--no-optional-locks',\n"
        "}\n"
        "index = 0\n"
        "while index < len(args):\n"
        "    arg = args[index]\n"
        "    if arg == '--':\n"
        "        index += 1\n"
        "        break\n"
        "    if arg in value_options:\n"
        "        if index + 1 >= len(args):\n"
        "            raise SystemExit(98)\n"
        "        index += 2\n"
        "        continue\n"
        "    if (arg.startswith(('-C', '-c')) and len(arg) > 2) or any(\n"
        "        arg.startswith(option + '=')\n"
        "        for option in value_options if option.startswith('--')\n"
        "    ):\n"
        "        index += 1\n"
        "        continue\n"
        "    if arg in flag_options:\n"
        "        index += 1\n"
        "        continue\n"
        "    if arg in {'--help', '--version'}:\n"
        "        os.execv(REAL_GIT, [REAL_GIT, *args])\n"
        "    if arg.startswith('-'):\n"
        "        raise SystemExit(98)\n"
        "    break\n"
        "command = args[index] if index < len(args) else ''\n"
        "with open(LOG_PATH, 'a', encoding='utf-8') as stream:\n"
        "    stream.write(command + '\\t' + ' '.join(args) + '\\n')\n"
        "read_only = {\n"
        "    'cat-file', 'describe', 'diff', 'for-each-ref', 'grep', 'log',\n"
        "    'ls-files', 'ls-tree', 'name-rev', 'rev-parse', 'show', 'status',\n"
        "    'version',\n"
        "}\n"
        "read_only_tag = command == 'tag' and index == len(args) - 1\n"
        "if command not in read_only and not read_only_tag:\n"
        "    raise SystemExit(97)\n"
        "os.execv(REAL_GIT, [REAL_GIT, *args])\n",
        encoding="utf-8",
    )
    path.chmod(0o755)


def _assert_safe_example_source(source: str) -> None:
    """Reject generated examples that can heal, mutate Git, or run live."""
    # pylint: disable=too-many-locals
    tree = ast.parse(source)
    forbidden = {"commit_and_push", "heal_module", "detect_drift"}
    imported_symbols: dict[str, str] = {}
    module_aliases: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module == "pdd.ci_drift_heal":
            for alias in node.names:
                imported_symbols[alias.asname or alias.name] = alias.name
                assert alias.name not in forbidden
        elif isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name == "pdd.ci_drift_heal":
                    module_aliases.add(alias.asname or alias.name)

    def dotted_name(node: ast.expr) -> str:
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            base = dotted_name(node.value)
            return f"{base}.{node.attr}" if base else node.attr
        return ""

    main_calls: list[ast.Call] = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        dotted = dotted_name(node.func)
        local_name = dotted.rsplit(".", 1)[-1]
        resolved = imported_symbols.get(local_name, local_name)
        module_qualified = any(
            dotted == alias or dotted.startswith(alias + ".")
            for alias in module_aliases
        )
        if resolved in forbidden or (
            module_qualified and local_name in forbidden
        ):
            raise AssertionError(f"forbidden call: {dotted}")
        assert resolved not in {"commit", "push"}
        if resolved == "main" or (module_qualified and local_name == "main"):
            main_calls.append(node)

    assert len(main_calls) == 1
    for call in main_calls:
        dry_run_values = [
            keyword.value for keyword in call.keywords if keyword.arg == "dry_run"
        ]
        assert len(dry_run_values) == 1
        dry_run = dry_run_values[0]
        assert isinstance(dry_run, ast.Constant) and dry_run.value is True


def _provider_free_env() -> dict[str, str]:
    env = os.environ.copy()
    for name in tuple(env):
        if name.endswith("_API_KEY") or name in {
            "ANTHROPIC_AUTH_TOKEN",
            "GOOGLE_APPLICATION_CREDENTIALS",
            "PDD_SYNC_PROTECTED_BASE_SHA",
        }:
            env.pop(name, None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["PYTHONPATH"] = os.pathsep.join(
        item for item in (str(ROOT), env.get("PYTHONPATH", "")) if item
    )
    return env


def test_example_propagates_dry_run_failure(monkeypatch, capsys):
    """A failed ``main(dry_run=True)`` must make the example fail truthfully."""
    assert "dry_run" in inspect.signature(ci_drift_heal_main).parameters
    example = _load_example()
    with tempfile.TemporaryDirectory() as temp:
        assert example.invoke_main(Path(temp), lambda **_kwargs: 7) == 7

    monkeypatch.setattr(example, "run_dry_run", lambda _workspace: 7)

    assert example.run() == 7
    output = capsys.readouterr()
    assert "failed with exit code 7" in output.err
    assert "completed successfully" not in output.out


def test_invoke_main_restores_cwd_after_failure(tmp_path: Path):
    """An exception from the real entry-point boundary cannot strand the CWD."""
    example = _load_example()
    original = Path.cwd()

    def fail(**_kwargs):
        raise RuntimeError("sentinel failure")

    with pytest.raises(RuntimeError, match="sentinel failure"):
        example.invoke_main(tmp_path, fail)
    assert Path.cwd() == original


def test_child_environment_is_minimal_isolated_and_bytecode_safe(
    monkeypatch, tmp_path: Path
):
    """Capture the actual child env and reject inherited secrets/config roots."""
    example = _load_example()
    credentials = {
        "CLAUDE_CODE_OAUTH_TOKEN": "sentinel-claude-oauth",
        "AWS_ACCESS_KEY_ID": "sentinel-aws-id",
        "AWS_SECRET_ACCESS_KEY": "sentinel-aws-secret",
        "AWS_SESSION_TOKEN": "sentinel-aws-session",
        "AZURE_CLIENT_ID": "sentinel-azure-id",
        "AZURE_CLIENT_SECRET": "sentinel-azure-secret",
        "GOOGLE_APPLICATION_CREDENTIALS": str(tmp_path / "ambient-adc.json"),
    }
    ambient_config = {
        "HOME": str(tmp_path / "ambient-home"),
        "XDG_CONFIG_HOME": str(tmp_path / "ambient-xdg"),
        "AWS_CONFIG_FILE": str(tmp_path / "ambient-aws-config"),
        "AWS_SHARED_CREDENTIALS_FILE": str(tmp_path / "ambient-aws-creds"),
        "AZURE_CONFIG_DIR": str(tmp_path / "ambient-azure"),
        "CLOUDSDK_CONFIG": str(tmp_path / "ambient-gcloud"),
        "PYTHONPATH": "sentinel-ambient-pythonpath",
    }
    for name, value in {**credentials, **ambient_config}.items():
        monkeypatch.setenv(name, value)

    captured: dict[str, object] = {}

    def capture_run(*_args, **kwargs):
        captured.update(kwargs)
        return SimpleNamespace(returncode=0)

    monkeypatch.setattr(example.subprocess, "run", capture_run)
    workspace = tmp_path / "workspace"
    workspace.mkdir()

    assert example.run_dry_run(workspace) == 0
    child_env = captured["env"]
    assert isinstance(child_env, dict)
    assert not set(credentials).intersection(child_env)
    assert not set(credentials.values()).intersection(child_env.values())
    assert not set(ambient_config.values()).intersection(child_env.values())
    isolated_paths = (
        "HOME",
        "XDG_CONFIG_HOME",
        "AWS_CONFIG_FILE",
        "AWS_SHARED_CREDENTIALS_FILE",
        "AZURE_CONFIG_DIR",
        "CLOUDSDK_CONFIG",
    )
    assert all(Path(child_env[name]).is_relative_to(workspace) for name in isolated_paths)
    assert child_env["PYTHONPATH"] == str(ROOT)
    assert child_env["PYTHONDONTWRITEBYTECODE"] == "1"
    assert example.sys.dont_write_bytecode is True


def test_example_runs_twice_without_checkout_or_caller_repo_residue(tmp_path: Path):
    """The provider-free example is repeatable and leaves both repos untouched."""
    caller_repo = tmp_path / "caller"
    caller_repo.mkdir()
    (caller_repo / "marker.txt").write_text("unchanged\n", encoding="utf-8")
    subprocess.run(["git", "init", "-q", "-b", "main"], cwd=caller_repo, check=True)
    subprocess.run(
        ["git", "config", "user.email", "example@example.com"],
        cwd=caller_repo,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Example"], cwd=caller_repo, check=True
    )
    subprocess.run(["git", "add", "marker.txt"], cwd=caller_repo, check=True)
    subprocess.run(
        ["git", "commit", "-q", "-m", "initial"], cwd=caller_repo, check=True
    )

    real_git = shutil.which("git")
    assert real_git is not None
    shim_dir = tmp_path / "bin"
    shim_dir.mkdir()
    shim_log = tmp_path / "git-shim.log"
    git_shim = shim_dir / "git"
    _write_git_shim(git_shim, shim_log, real_git)

    caller_before = _tree_digest(caller_repo)
    admin_before = _git_admin_snapshot(caller_repo)
    checkout_before = _source_checkout_snapshot(ROOT)

    env = _provider_free_env()
    env["PATH"] = os.pathsep.join((str(shim_dir), env["PATH"]))
    for _attempt in range(2):
        result = subprocess.run(
            [sys.executable, str(EXAMPLE)],
            cwd=caller_repo,
            env=env,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert "completed successfully" in result.stdout

    assert _tree_digest(caller_repo) == caller_before
    assert _git_admin_snapshot(caller_repo) == admin_before
    if shim_log.exists():
        forbidden = {
            "add", "commit", "push", "checkout", "reset", "restore", "clean",
            "update-ref", "write-tree", "read-tree", "merge", "rebase",
        }
        observed = {line.split(maxsplit=1)[0] for line in shim_log.read_text().splitlines()}
        assert observed.isdisjoint(forbidden)
    assert _source_checkout_snapshot(ROOT) == checkout_before


def test_prompt_pins_non_mutating_truthful_example_contract():
    """Hosted regeneration must preserve the safety contract from issue #2061."""
    prompt = PROMPT.read_text(encoding="utf-8")
    required = (
        "disposable temporary project",
        "provider credentials",
        "never call `commit_and_push`",
        "propagate that exact non-zero exit code",
        "must not write to the source checkout",
        "bounded timeout",
        "minimal environment allowlist",
        "isolated temporary HOME",
        "module-qualified aliases",
        "Git global options",
        "disposable workspace Git state",
        "linked-worktree pointer",
        "--git-common-dir",
        "admin/index/packed-refs/log state",
    )
    assert all(fragment in prompt for fragment in required)
    assert EXAMPLE.read_bytes().endswith(b"\n")


def test_example_ast_forbids_healing_git_and_non_dry_run_paths():
    """Generated bytes, not prompt prose, must exclude mutation entry points."""
    _assert_safe_example_source(EXAMPLE.read_text(encoding="utf-8"))


@pytest.mark.parametrize(
    "unsafe_call",
    (
        "drift.commit_and_push([])",
        "drift.heal_module(None, {})",
        "drift.main(dry_run=False)",
    ),
)
def test_ast_guard_rejects_module_qualified_bypasses(unsafe_call: str):
    """A regenerated module alias cannot hide mutation or a live main call."""
    source = (
        "from pdd.ci_drift_heal import main\n"
        "import pdd.ci_drift_heal as drift\n"
        "main(dry_run=True)\n"
        f"{unsafe_call}\n"
    )
    with pytest.raises(AssertionError):
        _assert_safe_example_source(source)


def test_ast_guard_rejects_imported_main_alias_bypass():
    """A renamed imported main must still require literal ``dry_run=True``."""
    source = (
        "from pdd.ci_drift_heal import main, main as run_live\n"
        "main(dry_run=True)\n"
        "run_live(dry_run=False)\n"
    )
    with pytest.raises(AssertionError):
        _assert_safe_example_source(source)


@pytest.mark.parametrize(
    "global_args",
    (
        ("-C", "{repo}", "commit", "--dry-run"),
        ("-c", "user.name=Sentinel", "push", "--dry-run"),
        ("--git-dir", "{git_dir}", "update-ref"),
        ("--work-tree={repo}", "clean", "-n"),
        ("--", "checkout"),
    ),
)
def test_git_shim_rejects_mutation_after_global_options(
    tmp_path: Path, global_args: tuple[str, ...]
):
    """Git global options cannot hide the first write-capable subcommand."""
    repo = tmp_path / "repo"
    repo.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
    real_git = shutil.which("git")
    assert real_git is not None
    shim = tmp_path / "git"
    _write_git_shim(shim, tmp_path / "shim.log", real_git)
    args = [
        item.format(repo=repo, git_dir=repo / ".git") for item in global_args
    ]

    result = subprocess.run(
        [str(shim), *args], cwd=repo, check=False, capture_output=True
    )
    assert result.returncode == 97


def test_disposable_workspace_git_admin_state_is_unchanged(
    monkeypatch, tmp_path: Path
):
    """The observable disposable repo keeps HEAD, refs, config, and admin bytes."""
    example = _load_example()
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    example.create_disposable_project(workspace)
    subprocess.run(["git", "init", "-q", "-b", "main"], cwd=workspace, check=True)
    subprocess.run(
        ["git", "config", "user.email", "example@example.com"],
        cwd=workspace,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Example"], cwd=workspace, check=True
    )
    subprocess.run(["git", "add", "."], cwd=workspace, check=True)
    subprocess.run(
        ["git", "commit", "-q", "-m", "fixture"], cwd=workspace, check=True
    )

    real_git = shutil.which("git")
    assert real_git is not None
    shim_dir = tmp_path / "bin"
    shim_dir.mkdir()
    _write_git_shim(shim_dir / "git", tmp_path / "workspace-git.log", real_git)
    monkeypatch.setenv("PATH", os.pathsep.join((str(shim_dir), os.environ["PATH"])))
    before = _git_admin_snapshot(workspace, real_git)

    assert example.run_dry_run(workspace) == 0
    assert _git_admin_snapshot(workspace, real_git) == before


def test_source_snapshot_detects_clean_status_linked_admin_mutation(tmp_path: Path):
    """A linked-worktree admin mutation must not hide behind clean status."""
    main_repo = tmp_path / "main"
    linked_repo = tmp_path / "linked"
    main_repo.mkdir()
    subprocess.run(["git", "init", "-q", "-b", "main"], cwd=main_repo, check=True)
    subprocess.run(
        ["git", "config", "user.email", "example@example.com"],
        cwd=main_repo,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Example"], cwd=main_repo, check=True
    )
    (main_repo / "tracked.txt").write_text("stable\n", encoding="utf-8")
    subprocess.run(["git", "add", "tracked.txt"], cwd=main_repo, check=True)
    subprocess.run(
        ["git", "commit", "-q", "-m", "fixture"], cwd=main_repo, check=True
    )
    subprocess.run(
        ["git", "worktree", "add", "-q", "-b", "linked", str(linked_repo)],
        cwd=main_repo,
        check=True,
    )

    before = _source_checkout_snapshot(linked_repo)
    git_dir_text = subprocess.run(
        ["git", "rev-parse", "--git-dir"],
        cwd=linked_repo,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    git_dir = Path(git_dir_text)
    if not git_dir.is_absolute():
        git_dir = linked_repo / git_dir
    head_log = git_dir.resolve() / "logs" / "HEAD"
    head_log.write_bytes(head_log.read_bytes() + b"admin sentinel\n")

    assert subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=all"],
        cwd=linked_repo,
        check=True,
        capture_output=True,
        text=True,
    ).stdout == ""
    assert _source_checkout_snapshot(linked_repo) != before
