from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
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


def _find_installed_on_path(
    version: str,
    env: Mapping[str, str],
    self_path: str | None,
    is_windows: bool | None = None,
) -> Path | None:
    raw_path = env.get("PATH", "")
    if not raw_path:
        return None
    win_mode = (os.name == "nt") if is_windows is None else is_windows
    exe_names = ("pdd.cmd", "pdd") if win_mode else ("pdd",)
    for folder in raw_path.split(os.pathsep):
        if not folder:
            continue
        folder_path = Path(folder)
        for name in exe_names:
            candidate = folder_path / name
            if not candidate.is_file():
                continue
            resolved_str = _real_or_none(candidate)
            if not resolved_str or (self_path and resolved_str == self_path):
                continue
            resolved = Path(resolved_str)
            if resolved.name == "pdd.mjs" and _read_pkg_version(resolved) == version:
                return resolved
            if win_mode and name.lower() == "pdd.cmd":
                for win_entry in (
                    folder_path / "node_modules" / "@promptdriven" / "pdd" / "bin" / "pdd.mjs",
                    folder_path.parent / "node_modules" / "@promptdriven" / "pdd" / "bin" / "pdd.mjs",
                ):
                    if win_entry.is_file() and _read_pkg_version(win_entry) == version:
                        return win_entry.resolve()
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


def _is_own_python_wrapper(candidate: Path, self_real: str | None) -> bool:
    cand_real = _real_or_none(candidate)
    if self_real and cand_real == self_real:
        return True
    try:
        st = candidate.stat()
        if st.st_size > 65536:
            return False
        with candidate.open("rb") as fh:
            head = fh.read(4096)
    except OSError:
        return False
    if not head.startswith(b"#!"):
        return False
    text = head.decode("utf-8", errors="ignore")
    return bool(re.search(r"\bpdd_cli\b", text))


def _set_symlink(link_path: Path, target: str | Path) -> None:
    target_str = str(target)
    try:
        if link_path.is_symlink() and os.readlink(link_path) == target_str:
            return
    except OSError:
        pass
    if link_path.exists() or link_path.is_symlink():
        link_path.unlink()
    link_path.symlink_to(target_str)


def _sync_mirrored_shim(folder: Path, entry_real: str, cache_root: Path) -> Path:
    folder_abs = Path(os.path.abspath(folder))
    digest = hashlib.sha256(f"{folder_abs}\0{entry_real}".encode("utf-8")).hexdigest()[:12]
    shim_root = cache_root / "pdd-cli" / "shims" / digest
    shim_bin = shim_root / "bin"
    shim_bin.mkdir(parents=True, exist_ok=True)

    _set_symlink(shim_bin / "pdd", entry_real)

    present = {"pdd"}
    try:
        with os.scandir(folder_abs) as it:
            for item in it:
                if item.name == "pdd":
                    continue
                present.add(item.name)
                try:
                    _set_symlink(shim_bin / item.name, folder_abs / item.name)
                except OSError:
                    pass
    except OSError:
        pass

    try:
        with os.scandir(shim_bin) as it:
            for existing in it:
                if existing.name not in present:
                    try:
                        Path(existing.path).unlink()
                    except OSError:
                        pass
    except OSError:
        pass

    pyvenv_cfg = folder_abs.parent / "pyvenv.cfg"
    if pyvenv_cfg.exists():
        try:
            _set_symlink(shim_root / "pyvenv.cfg", pyvenv_cfg.resolve())
        except OSError:
            pass
    return shim_bin


def _ensure_standalone_shim(entry_real: str, cache_root: Path) -> Path:
    digest = hashlib.sha256(f"standalone\0{entry_real}".encode("utf-8")).hexdigest()[:12]
    shim_bin = cache_root / "pdd-cli" / "shims" / digest / "bin"
    shim_bin.mkdir(parents=True, exist_ok=True)
    _set_symlink(shim_bin / "pdd", entry_real)
    return shim_bin


def _prepare_child_env(
    entry_mjs: Path,
    env: Mapping[str, str],
    depth: int,
    argv0: str | None = None,
) -> dict[str, str]:
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

    eff_argv0 = argv0 or sys.argv[0]
    self_real: str | None = None
    if eff_argv0 and Path(eff_argv0).name.lower() in ("pdd", "pdd.cmd", "pdd.exe"):
        self_real = _real_or_none(eff_argv0)

    cache_root = _cache_root(child_env)
    raw_path = child_env.get("PATH", "")
    parts = [p for p in raw_path.split(os.pathsep)] if raw_path else []
    has_alpha_on_path = False

    try:
        for idx, folder in enumerate(parts):
            if not folder:
                continue
            candidate = Path(folder) / "pdd"
            if not (candidate.is_file() and os.access(candidate, os.X_OK)):
                continue
            if _real_or_none(candidate) == entry_real:
                has_alpha_on_path = True
            elif _is_own_python_wrapper(candidate, self_real):
                parts[idx] = str(_sync_mirrored_shim(Path(folder), entry_real, cache_root))
                has_alpha_on_path = True

        if not has_alpha_on_path:
            parts.append(str(_ensure_standalone_shim(entry_real, cache_root)))
        child_env["PATH"] = os.pathsep.join(parts)
    except OSError:
        pass
    return child_env


def _run_interruptible(cmd: Sequence[str], env: Mapping[str, str]) -> int:
    try:
        proc = subprocess.run(cmd, env=dict(env))
    except KeyboardInterrupt:
        return 130
    if proc.returncode < 0:
        return 128 + (-proc.returncode)
    return proc.returncode


def main(
    argv: Sequence[str] | None = None,
    env: Mapping[str, str] | None = None,
    argv0: str | None = None,
) -> int:
    active_env = os.environ if env is None else env
    args = list(sys.argv[1:] if argv is None else argv)
    effective_argv0 = sys.argv[0] if argv0 is None else argv0

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

    entry_mjs, detail = resolve_cli_entry(__version__, active_env, argv0=effective_argv0)
    if entry_mjs is None:
        npx_bin = active_env.get("PDD_NPX_BIN", "").strip() or shutil.which("npx", path=active_env.get("PATH"))
        if npx_bin and active_env.get("PDD_CLI_OFFLINE") != "1":
            child_env = dict(active_env)
            child_env["PDD_PYTHON_WRAPPER_DEPTH"] = str(depth + 1)
            return _run_interruptible(
                [npx_bin, "--yes", "--package", f"{PACKAGE_NAME}@{__version__}", "pdd", *args],
                child_env,
            )
        msg = f"Unable to locate or install {PACKAGE_NAME}@{__version__}."
        if detail:
            msg = f"{msg}\n{detail}"
        sys.stderr.write(f"{msg}\n")
        return 1

    child_env = _prepare_child_env(entry_mjs, active_env, depth, argv0=effective_argv0)
    cmd = [node_bin, str(entry_mjs), *args]
    if argv is None and env is None and os.name == "posix" and active_env.get("PDD_CLI_NO_EXEC") != "1":
        os.execve(node_bin, cmd, child_env)

    return _run_interruptible(cmd, child_env)
