from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from typing import Mapping, Sequence

from . import __version__

PACKAGE_NAME = "@promptdriven/pdd"
MAX_WRAPPER_DEPTH = 3


def _real_or_none(path: Path | str) -> str | None:
    try:
        return os.path.realpath(path)
    except OSError:
        return None


def _read_pkg_version(entry_mjs: Path) -> str | None:
    pkg_json = entry_mjs.parent.parent / "package.json"
    try:
        data = json.loads(pkg_json.read_text(encoding="utf-8"))
    except (OSError, ValueError, TypeError):
        return None
    if not isinstance(data, dict) or data.get("name") != PACKAGE_NAME:
        return None
    version = data.get("version")
    return version if isinstance(version, str) and version else None


def _cache_root(env: Mapping[str, str]) -> Path:
    explicit = env.get("PDD_CLI_CACHE_DIR", "").strip()
    if explicit:
        return Path(explicit).expanduser()
    xdg = env.get("XDG_CACHE_HOME", "").strip()
    if xdg:
        return Path(xdg).expanduser()
    home = Path(env.get("HOME") or Path.home())
    if sys.platform == "darwin":
        return home / "Library" / "Caches"
    if os.name == "nt":
        local_app_data = env.get("LOCALAPPDATA", "").strip()
        if local_app_data:
            return Path(local_app_data)
    return home / ".cache"


def _find_installed_on_path(version: str, env: Mapping[str, str], self_path: str | None) -> Path | None:
    raw_path = env.get("PATH", "")
    if not raw_path:
        return None
    exe_names = ("pdd.cmd", "pdd") if os.name == "nt" else ("pdd",)
    for folder in raw_path.split(os.pathsep):
        if not folder:
            continue
        for name in exe_names:
            candidate = Path(folder) / name
            if not candidate.is_file():
                continue
            resolved_str = _real_or_none(candidate)
            if not resolved_str or (self_path and resolved_str == self_path):
                continue
            resolved = Path(resolved_str)
            if resolved.name == "pdd.mjs" and _read_pkg_version(resolved) == version:
                return resolved
    return None


def _install_into_cache(version: str, cache_dir: Path, env: Mapping[str, str]) -> tuple[Path | None, str]:
    cached_entry = cache_dir / "node_modules" / "@promptdriven" / "pdd" / "bin" / "pdd.mjs"
    if cached_entry.is_file() and _read_pkg_version(cached_entry) == version:
        return cached_entry, ""
    if env.get("PDD_CLI_OFFLINE") == "1":
        return None, f"{PACKAGE_NAME}@{version} is not cached and PDD_CLI_OFFLINE=1 is set."

    npm_bin = env.get("PDD_NPM_BIN", "").strip() or shutil.which("npm", path=env.get("PATH"))
    if not npm_bin:
        return None, "npm was not found on PATH to install @promptdriven/pdd."

    try:
        cache_dir.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        return None, f"Could not create cache directory {cache_dir}: {exc}"

    specs = (
        f"{PACKAGE_NAME}@{version}",
        f"github:promptdriven/pdd#v{version}",
        f"github:promptdriven/pdd#alpha-v{version}",
    )
    last_err = ""
    for spec in specs:
        proc = subprocess.run(
            [
                npm_bin,
                "install",
                "--prefix",
                str(cache_dir),
                "--ignore-scripts",
                "--no-audit",
                "--no-fund",
                "--package-lock=false",
                spec,
            ],
            env=dict(env),
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
        )
        if proc.returncode == 0 and cached_entry.is_file() and _read_pkg_version(cached_entry) == version:
            return cached_entry, ""
        last_err = (proc.stderr or proc.stdout or "").strip()
    return None, last_err


def resolve_cli_entry(
    version: str = __version__,
    env: Mapping[str, str] | None = None,
    argv0: str | None = None,
) -> tuple[Path | None, str]:
    active_env = os.environ if env is None else env
    explicit = active_env.get("PDD_CLI_JS_ENTRY", "").strip()
    if explicit:
        override = Path(explicit).expanduser()
        if override.is_file():
            return override.resolve(), ""
        return None, f"PDD_CLI_JS_ENTRY does not exist: {override}"

    pkg_dir = Path(__file__).resolve().parent
    bundled = pkg_dir / "_bundled" / "bin" / "pdd.mjs"
    if bundled.is_file() and _read_pkg_version(bundled) == version:
        return bundled, ""

    if active_env.get("PDD_CLI_IGNORE_CHECKOUT") != "1":
        checkout = pkg_dir.parents[1] / "bin" / "pdd.mjs"
        if checkout.is_file() and _read_pkg_version(checkout) == version:
            return checkout, ""

    self_real = _real_or_none(argv0 or sys.argv[0])
    on_path = _find_installed_on_path(version, active_env, self_real)
    if on_path is not None:
        return on_path, ""

    cache_dir = _cache_root(active_env) / "pdd-cli" / version
    return _install_into_cache(version, cache_dir, active_env)


def _prepare_child_env(entry_mjs: Path, env: Mapping[str, str], depth: int) -> dict[str, str]:
    child_env = dict(env)
    child_env["PDD_PYTHON_WRAPPER_DEPTH"] = str(depth + 1)

    if os.name == "nt":
        return child_env

    if not os.access(entry_mjs, os.X_OK):
        try:
            os.chmod(entry_mjs, 0o755)
        except OSError:
            return child_env

    entry_real = _real_or_none(entry_mjs)
    if not entry_real:
        return child_env

    raw_path = child_env.get("PATH", "")
    for folder in raw_path.split(os.pathsep):
        if not folder:
            continue
        candidate = Path(folder) / "pdd"
        if candidate.is_file() and os.access(candidate, os.X_OK):
            if _real_or_none(candidate) == entry_real:
                return child_env
            break

    digest = hashlib.sha256(entry_real.encode("utf-8")).hexdigest()[:12]
    shim_bin = _cache_root(child_env) / "pdd-cli" / "shims" / digest / "bin"
    shim_target = shim_bin / "pdd"
    try:
        shim_bin.mkdir(parents=True, exist_ok=True)
        if _real_or_none(shim_target) != entry_real:
            if shim_target.exists() or shim_target.is_symlink():
                shim_target.unlink()
            shim_target.symlink_to(entry_real)
        child_env["PATH"] = f"{shim_bin}{os.pathsep}{raw_path}" if raw_path else str(shim_bin)
    except OSError:
        pass
    return child_env


def main(argv: Sequence[str] | None = None, env: Mapping[str, str] | None = None) -> int:
    active_env = os.environ if env is None else env
    args = list(sys.argv[1:] if argv is None else argv)

    try:
        depth = int(active_env.get("PDD_PYTHON_WRAPPER_DEPTH", "0"))
    except ValueError:
        depth = 0
    if depth >= MAX_WRAPPER_DEPTH:
        sys.stderr.write("pdd wrapper detected recursive self-invocation; check your PATH.\n")
        return 1

    node_bin = active_env.get("PDD_NODE_BIN", "").strip() or shutil.which("node", path=active_env.get("PATH"))
    if not node_bin or not Path(node_bin).is_file():
        sys.stderr.write(
            f"pdd requires Node.js >=22.16.0 on PATH to run {PACKAGE_NAME} {__version__}. "
            "Install Node.js from https://nodejs.org and run pdd again.\n"
        )
        return 127

    entry_mjs, detail = resolve_cli_entry(__version__, active_env)
    if entry_mjs is None:
        npx_bin = active_env.get("PDD_NPX_BIN", "").strip() or shutil.which("npx", path=active_env.get("PATH"))
        if npx_bin and active_env.get("PDD_CLI_OFFLINE") != "1":
            child_env = dict(active_env)
            child_env["PDD_PYTHON_WRAPPER_DEPTH"] = str(depth + 1)
            proc = subprocess.run(
                [npx_bin, "--yes", "--package", f"{PACKAGE_NAME}@{__version__}", "pdd", *args],
                env=child_env,
            )
            return proc.returncode
        msg = f"Unable to locate or install {PACKAGE_NAME}@{__version__}."
        if detail:
            msg = f"{msg}\n{detail}"
        sys.stderr.write(f"{msg}\n")
        return 1

    child_env = _prepare_child_env(entry_mjs, active_env, depth)
    cmd = [node_bin, str(entry_mjs), *args]
    if argv is None and env is None and os.name == "posix" and active_env.get("PDD_CLI_NO_EXEC") != "1":
        os.execve(node_bin, cmd, child_env)

    proc = subprocess.run(cmd, env=child_env)
    return proc.returncode
