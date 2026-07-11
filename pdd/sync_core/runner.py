"""Trusted validator adapters and pass-only normalized evidence outcomes."""
# pylint: disable=too-many-lines,too-many-boolean-expressions,too-many-locals

from __future__ import annotations

import hashlib
import ast
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path, PurePosixPath

from .trust import (
    AttestationBinding,
    AttestationEnvelope,
    AttestationIssuer,
    AttestationRequest,
)
from .isolation import SECRET_ENV_MARKERS, untrusted_child_environment
from .git_io import read_git_blob
from .types import (
    EvidenceOutcome,
    ObligationEvidence,
    UnitId,
    VerificationObligation,
    VerificationProfile,
)
from .supervisor import run_supervised


TRUSTED_RUNNER_VERSION = "pdd-trusted-runner-v2"
PYTEST_CONFIG_PATHS = (
    PurePosixPath("pytest.ini"),
    PurePosixPath("pyproject.toml"),
    PurePosixPath("tox.ini"),
    PurePosixPath("setup.cfg"),
)
PYTEST_PROTECTED_FLAGS = (
    "--strict-config", "--strict-markers", "-ra", "-p", "no:cacheprovider"
)
_CHECKER_PYTEST_PROBE = Path(__file__).with_name("pytest_probe.py").resolve()
JEST_CONFIG_PATHS = (
    PurePosixPath("jest.config.json"),
    PurePosixPath("package.json"),
)
JEST_DYNAMIC_CONFIG_NAMES = (
    "jest.config.js", "jest.config.cjs", "jest.config.mjs", "jest.config.ts"
)
JEST_LOCAL_SCALAR_CONFIG_KEYS = (
    "dependencyExtractor",
    "globalSetup",
    "globalTeardown",
    "prettierPath",
    "resolver",
    "runner",
    "snapshotResolver",
    "testSequencer",
    "testEnvironment",
    "testResultsProcessor",
    "testRunner",
)
JEST_LOCAL_ARRAY_CONFIG_KEYS = (
    "reporters",
    "setupFiles",
    "setupFilesAfterEnv",
    "snapshotSerializers",
    "watchPlugins",
)
_JAVASCRIPT_SUFFIXES = (
    ".js",
    ".cjs",
    ".mjs",
    ".ts",
    ".cts",
    ".mts",
    ".tsx",
    ".jsx",
    ".json",
)
VITEST_CONFIG_PATHS = (
    PurePosixPath("vitest.config.json"),
    PurePosixPath("package.json"),
)
VITEST_DYNAMIC_CONFIG_NAMES = (
    "vitest.config.js",
    "vitest.config.cjs",
    "vitest.config.mjs",
    "vitest.config.ts",
    "vitest.config.cts",
    "vitest.config.mts",
)
PLAYWRIGHT_CONFIG_NAMES = (
    "playwright.config.js", "playwright.config.cjs", "playwright.config.mjs",
    "playwright.config.ts", "playwright.config.cts", "playwright.config.mts",
)


@dataclass(frozen=True)
class RunnerConfig:
    """Protected execution limits for trusted validation adapters."""

    timeout_seconds: int = 300
    jest_command: tuple[str, ...] | None = None
    vitest_command: tuple[str, ...] | None = None
    playwright_command: tuple[str, ...] | None = None


@dataclass(frozen=True)
class RunnerExecution:
    """Normalized outcome and command identity for one obligation."""

    obligation_id: str
    outcome: EvidenceOutcome
    command_digest: str
    detail: str


@dataclass(frozen=True)
class RunBinding:
    """Snapshot and Git closure supplied to all profile obligations."""

    snapshot_digest: str
    base_sha: str
    head_sha: str


@dataclass(frozen=True)
class AttestationIssue:
    """Trusted signer and unique issuance fields for one profile run."""

    signer: AttestationIssuer
    attestation_id: str
    nonce: str
    issued_at: datetime


def _pytest_plugin_modules(node: ast.AST) -> tuple[set[str], bool]:
    """Return statically declared pytest plugin modules and dynamic status."""
    modules: set[str] = set()
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        modules.add(node.value)
        return modules, False
    if isinstance(node, (ast.List, ast.Tuple)):
        for item in node.elts:
            if not isinstance(item, ast.Constant) or not isinstance(item.value, str):
                return modules, True
            modules.add(item.value)
        return modules, False
    return modules, True


def _pytest_plugin_declaration_targets(node: ast.AST) -> tuple[ast.AST, ...]:
    """Return assignment targets that may declare pytest plugins."""
    if isinstance(node, ast.Assign):
        return tuple(node.targets)
    if isinstance(node, ast.AnnAssign):
        return (node.target,)
    return ()


def _declares_pytest_plugins(targets: tuple[ast.AST, ...]) -> bool:
    """Return whether assignment targets include the pytest_plugins sentinel."""
    return any(
        isinstance(target, ast.Name) and target.id == "pytest_plugins"
        for target in targets
    )


def _local_module_paths(
    root: Path,
    ref: str,
    source_path: PurePosixPath,
    source: bytes,
    *,
    code_under_test_paths: frozenset[PurePosixPath] = frozenset(),
) -> tuple[set[PurePosixPath], bool]:
    # pylint: disable=too-many-locals,too-many-branches
    """Resolve repository-local Python imports without executing candidate code."""
    try:
        tree = ast.parse(source)
    except (SyntaxError, UnicodeDecodeError):
        return set(), False
    modules: set[str] = set()
    dynamic_pytest_plugins = False
    importlib_names = {"importlib"}
    loader_names = {"__import__"}
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            modules.update(alias.name for alias in node.names)
            importlib_names.update(
                alias.asname or alias.name
                for alias in node.names
                if alias.name == "importlib"
            )
        elif isinstance(node, ast.ImportFrom):
            prefix = "." * node.level
            module = prefix + (node.module or "")
            if node.module:
                modules.add(module)
            for alias in node.names:
                if alias.name == "*":
                    continue
                separator = "" if not module or module.endswith(".") else "."
                modules.add(f"{module}{separator}{alias.name}")
                if node.module == "importlib" and alias.name == "import_module":
                    loader_names.add(alias.asname or alias.name)
        elif _declares_pytest_plugins(_pytest_plugin_declaration_targets(node)):
            declared, dynamic = _pytest_plugin_modules(node.value)
            modules.update(declared)
            dynamic_pytest_plugins = dynamic_pytest_plugins or dynamic
        elif isinstance(node, ast.Call) and (
            isinstance(node.func, ast.Name) and node.func.id in loader_names
            or isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id in importlib_names
            and node.func.attr == "import_module"
        ):
            dynamic_pytest_plugins = True
        elif isinstance(node, ast.Call) and (
            isinstance(node.func, ast.Name)
            and node.func.id in {"getattr", "exec", "eval", "compile", "run_path", "run_module"}
            or isinstance(node.func, ast.Attribute)
            and node.func.attr in {
                "spec_from_file_location", "load_module", "exec_module",
                "run_path", "run_module",
            }
        ):
            dynamic_pytest_plugins = True
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            value = node.value
            if isinstance(value, ast.Name) and value.id == "__import__":
                dynamic_pytest_plugins = True
    resolved: set[PurePosixPath] = set()
    for module in modules:
        level = len(module) - len(module.lstrip("."))
        name = module.lstrip(".")
        base = source_path.parent
        for _ in range(max(level - 1, 0)):
            base = base.parent
        module_path = PurePosixPath(*name.split(".")) if name else PurePosixPath()
        candidates = (
            base / module_path.with_suffix(".py"),
            base / module_path / "__init__.py",
            module_path.with_suffix(".py"),
            module_path / "__init__.py",
        )
        resolved.update(
            path
            for path in candidates
            if read_git_blob(root, ref, path) is not None
            and path not in code_under_test_paths
        )
    for path in tuple(resolved):
        parent = path.parent
        while parent != PurePosixPath("."):
            initializer = parent / "__init__.py"
            if (
                read_git_blob(root, ref, initializer) is not None
                and initializer not in code_under_test_paths
            ):
                resolved.add(initializer)
            parent = parent.parent
    return resolved, dynamic_pytest_plugins


def _pytest_support_closure(
    root: Path,
    ref: str,
    test_paths: tuple[PurePosixPath, ...],
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
) -> tuple[tuple[PurePosixPath, bytes], ...]:
    """Return config, conftest, and transitive local-import blobs for pytest."""
    config_paths = _pytest_config_paths(root, ref, test_paths)
    return _transitive_support_blobs(
        root,
        ref,
        pending=tuple(test_paths) + tuple(config_paths),
        included=config_paths,
        test_artifacts=test_paths,
        code_under_test_paths=frozenset(code_under_test_paths),
    )


def _pytest_config_paths(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...]
) -> set[PurePosixPath]:
    """Return protected pytest config and governing conftest paths."""
    paths = {
        path for path in PYTEST_CONFIG_PATHS
        if read_git_blob(root, ref, path) is not None
    }
    for test_path in test_paths:
        parent = test_path.parent
        while parent != PurePosixPath("."):
            candidate = parent / "conftest.py"
            if read_git_blob(root, ref, candidate) is not None:
                paths.add(candidate)
            parent = parent.parent
        root_conftest = PurePosixPath("conftest.py")
        if read_git_blob(root, ref, root_conftest) is not None:
            paths.add(root_conftest)
    return paths


def _transitive_support_blobs(
    root: Path,
    ref: str,
    *,
    pending: tuple[PurePosixPath, ...],
    included: set[PurePosixPath],
    test_artifacts: tuple[PurePosixPath, ...] = (),
    code_under_test_paths: frozenset[PurePosixPath] = frozenset(),
) -> tuple[tuple[PurePosixPath, bytes], ...]:
    # pylint: disable=too-many-arguments
    """Resolve local Python imports from protected runner support paths."""
    paths = set(included)
    remaining = list(pending)
    del test_artifacts
    visited: set[PurePosixPath] = set()
    while remaining:
        path = remaining.pop()
        if path in visited:
            continue
        visited.add(path)
        source = read_git_blob(root, ref, path)
        if source is None or path.suffix != ".py":
            continue
        discovered, _dynamic = _local_module_paths(
            root,
            ref,
            path,
            source,
            code_under_test_paths=code_under_test_paths,
        )
        discovered -= visited
        paths.update(discovered)
        remaining.extend(discovered)
    blobs = ((path, read_git_blob(root, ref, path)) for path in sorted(paths))
    return tuple((path, blob) for path, blob in blobs if blob is not None)


def pytest_validator_config_digest(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...]
) -> str:
    """Hash the actual pytest config/conftest closure declared by a profile."""
    config_paths = _pytest_config_paths(root, ref, test_paths)
    closure = _transitive_support_blobs(
        root,
        ref,
        pending=tuple(config_paths),
        included=config_paths,
    )
    digest = hashlib.sha256()
    for path, content in closure:
        digest.update(path.as_posix().encode() + b"\0" + content + b"\0")
    return digest.hexdigest()


def _has_dynamic_pytest_plugins(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...],
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
) -> bool:
    """Fail closed when pytest plugin declarations cannot be statically bound."""
    config_paths = _pytest_config_paths(root, ref, test_paths)
    remaining = list(tuple(test_paths) + tuple(config_paths))
    visited: set[PurePosixPath] = set()
    while remaining:
        path = remaining.pop()
        if path in visited:
            continue
        visited.add(path)
        source = read_git_blob(root, ref, path)
        if source is None or path.suffix != ".py":
            continue
        discovered, dynamic = _local_module_paths(
            root,
            ref,
            path,
            source,
            code_under_test_paths=frozenset(code_under_test_paths),
        )
        if dynamic:
            return True
        remaining.extend(discovered - visited)
    return False


def _has_external_pytest_plugins(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...],
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
) -> bool:
    """Return whether a literal plugin declaration lacks protected repo bytes."""
    remaining = list(tuple(test_paths) + tuple(_pytest_config_paths(root, ref, test_paths)))
    visited: set[PurePosixPath] = set()
    while remaining:
        path = remaining.pop()
        if path in visited:
            continue
        visited.add(path)
        source = read_git_blob(root, ref, path)
        if source is None or path.suffix != ".py":
            continue
        try:
            tree = ast.parse(source)
        except (SyntaxError, UnicodeDecodeError):
            continue
        for node in ast.walk(tree):
            if not _declares_pytest_plugins(_pytest_plugin_declaration_targets(node)):
                continue
            modules, dynamic = _pytest_plugin_modules(node.value)
            if dynamic:
                continue
            for module in modules:
                module_path = PurePosixPath(*module.split("."))
                candidates = (
                    module_path.with_suffix(".py"),
                    module_path / "__init__.py",
                )
                if not any(read_git_blob(root, ref, item) is not None for item in candidates):
                    return True
        discovered, _dynamic = _local_module_paths(
            root, ref, path, source,
            code_under_test_paths=frozenset(code_under_test_paths),
        )
        remaining.extend(discovered - visited)
    return False


def _jest_config(root: Path, ref: str) -> tuple[PurePosixPath, dict[str, object]]:
    """Load the only supported, static Jest configuration forms."""
    for name in JEST_DYNAMIC_CONFIG_NAMES:
        if read_git_blob(root, ref, PurePosixPath(name)) is not None:
            raise ValueError("dynamic Jest configuration is not supported")
    config_path = PurePosixPath("jest.config.json")
    content = read_git_blob(root, ref, config_path)
    if content is None:
        config_path = PurePosixPath("package.json")
        content = read_git_blob(root, ref, config_path)
    if content is None:
        raise ValueError("no static Jest configuration is present")
    try:
        parsed = json.loads(content.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError("Jest configuration must be valid JSON") from exc
    if config_path.name == "package.json":
        parsed = parsed.get("jest") if isinstance(parsed, dict) else None
    if not isinstance(parsed, dict):
        raise ValueError("Jest configuration must be a JSON object")
    return config_path, parsed


def _jest_local_path(value: str) -> PurePosixPath | None:
    """Normalize a static config path without accepting package references."""
    value = value.replace("<rootDir>/", "")
    if value.startswith("<") or value.startswith("/") or not value:
        return None
    path = PurePosixPath(value)
    if ".." in path.parts:
        return None
    return path


def _jest_config_references(config: object) -> set[PurePosixPath]:
    """Find local executable support named by static Jest config keys."""
    if not isinstance(config, dict):
        return set()
    references: set[PurePosixPath] = set()
    for key in JEST_LOCAL_ARRAY_CONFIG_KEYS:
        value = config.get(key, [])
        if not isinstance(value, list):
            raise ValueError(f"Jest {key} must be an array")
        for item in value:
            target = item[0] if isinstance(item, list) and item else item
            if not isinstance(target, str):
                raise ValueError(f"Jest {key} entry must be a static local path")
            path = _jest_local_path(target)
            if path is None:
                raise ValueError(f"Jest {key} plugin is not bound by this adapter")
            references.add(path)
    for key in JEST_LOCAL_SCALAR_CONFIG_KEYS:
        value = config.get(key)
        if value is None:
            continue
        if not isinstance(value, str):
            raise ValueError(f"Jest {key} must be a string")
        path = _jest_local_path(value)
        if path is None:
            raise ValueError(f"Jest {key} is not bound by this adapter")
        references.add(path)
    transforms = config.get("transform", {})
    if not isinstance(transforms, dict):
        raise ValueError("Jest transform must be an object")
    for value in transforms.values():
        target = value[0] if isinstance(value, list) and value else value
        if not isinstance(target, str):
            raise ValueError("Jest transform entry must be a static path")
        path = _jest_local_path(target)
        if path is None:
            raise ValueError("Jest transform is not bound by this adapter")
        references.add(path)
    projects = config.get("projects", [])
    if not isinstance(projects, list):
        raise ValueError("Jest projects must be an array")
    for project in projects:
        if isinstance(project, dict):
            references.update(_jest_config_references(project))
        elif isinstance(project, str):
            path = _jest_local_path(project)
            if path is None:
                raise ValueError("Jest project is not bound by this adapter")
            references.add(path)
        else:
            raise ValueError("Jest project must be a static local config")
    module_name_mapper = config.get("moduleNameMapper", {})
    if not isinstance(module_name_mapper, dict):
        raise ValueError("Jest moduleNameMapper must be an object")
    for value in module_name_mapper.values():
        targets = value if isinstance(value, list) else [value]
        for target in targets:
            if not isinstance(target, str):
                raise ValueError("Jest moduleNameMapper entry must be a static path")
            path = _jest_local_path(target)
            if path is None:
                raise ValueError("Jest moduleNameMapper target is not bound by this adapter")
            parts = tuple(part for part in path.parts if not re.search(r"\$[0-9&]", part))
            if parts:
                references.add(PurePosixPath(*parts))
    module_directories = config.get("moduleDirectories", [])
    if not isinstance(module_directories, list):
        raise ValueError("Jest moduleDirectories must be an array")
    if module_directories:
        raise ValueError("Jest moduleDirectories is not bound by this adapter")
    return references


def _local_javascript_imports(
    root: Path, ref: str, source_path: PurePosixPath, source: bytes
) -> set[PurePosixPath]:
    """Resolve literal relative JS imports without executing candidate modules."""
    try:
        text = source.decode("utf-8")
    except UnicodeDecodeError:
        return set()
    imports = re.findall(
        r"(?:from\s+|import\s*\(|import\s+|require\s*\()['\"](\.{1,2}/[^'\"]+)['\"]",
        text,
    )
    resolved: set[PurePosixPath] = set()
    for item in imports:
        candidate = _normalize_repo_relative_path(
            source_path.parent / PurePosixPath(item)
        )
        if candidate is None:
            continue
        candidates = list(_javascript_path_candidates(candidate))
        resolved.update(
            path for path in candidates if read_git_blob(root, ref, path) is not None
        )
    return resolved


def _bare_javascript_imports(source: bytes) -> set[str]:
    """Return bare JS package imports that are not repository-relative paths."""
    try:
        text = source.decode("utf-8")
    except UnicodeDecodeError:
        return set()
    imports = re.findall(
        r"(?:from\s+|import\s*\(|import\s+|require\s*\()['\"]([^'\"]+)['\"]",
        text,
    )
    return {
        item
        for item in imports
        if not item.startswith((".", "/", "node:", "data:", "file:"))
    }


def _unbound_playwright_bare_imports(source: bytes) -> set[str]:
    """Return bare imports that could resolve through candidate dependencies."""
    return {
        item
        for item in _bare_javascript_imports(source)
        if item != "@playwright/test"
    }


def _normalize_repo_relative_path(path: PurePosixPath) -> PurePosixPath | None:
    """Collapse dot segments and reject paths that escape the repository."""
    parts: list[str] = []
    for part in path.parts:
        if part in {"", "."}:
            continue
        if part == "..":
            if not parts:
                return None
            parts.pop()
            continue
        parts.append(part)
    return PurePosixPath(*parts) if parts else PurePosixPath(".")


def _javascript_path_candidates(path: PurePosixPath) -> tuple[PurePosixPath, ...]:
    """Return file and directory-index candidates for a JS import target."""
    candidates = [path]
    if not path.suffix:
        candidates.extend(path.with_suffix(suffix) for suffix in _JAVASCRIPT_SUFFIXES)
        candidates.extend(path / f"index{suffix}" for suffix in _JAVASCRIPT_SUFFIXES)
    return tuple(candidates)


def _read_javascript_support_blob(
    root: Path, ref: str, path: PurePosixPath
) -> tuple[PurePosixPath, bytes] | tuple[PurePosixPath, None]:
    """Read a JS support path after applying file and index candidates."""
    normalized = _normalize_repo_relative_path(path)
    if normalized is None:
        return path, None
    for candidate in _javascript_path_candidates(normalized):
        source = read_git_blob(root, ref, candidate)
        if source is not None:
            return candidate, source
    return normalized, None


def _jest_support_closure(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...]
) -> tuple[tuple[PurePosixPath, bytes], ...]:
    """Return static config and transitive local Jest support modules."""
    config_path, config = _jest_config(root, ref)
    paths = {config_path}
    pending = list(test_paths) + list(_jest_config_references(config))
    visited: set[PurePosixPath] = set()
    while pending:
        path = pending.pop()
        if path in visited:
            continue
        visited.add(path)
        path, source = _read_javascript_support_blob(root, ref, path)
        if source is None:
            raise ValueError(f"Jest support path is missing: {path.as_posix()}")
        paths.add(path)
        if path.suffix == ".json":
            try:
                nested_config = json.loads(source.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise ValueError(f"Jest project config is invalid: {path.as_posix()}") from exc
            if path.name == "package.json" and isinstance(nested_config, dict):
                nested_config = nested_config.get("jest", {})
            pending.extend(_jest_config_references(nested_config) - visited)
        pending.extend(_local_javascript_imports(root, ref, path, source) - visited)
    return tuple(
        (path, read_git_blob(root, ref, path))
        for path in sorted(paths)
        if read_git_blob(root, ref, path) is not None
    )


def jest_validator_config_digest(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...]
) -> str:
    """Hash static Jest config and executable local support closure."""
    digest = hashlib.sha256()
    for path, content in _jest_support_closure(root, ref, test_paths):
        digest.update(path.as_posix().encode() + b"\0" + content + b"\0")
    return digest.hexdigest()


def _vitest_config(root: Path, ref: str) -> tuple[PurePosixPath, dict[str, object]]:
    """Load the only supported, static Vitest configuration forms."""
    for name in VITEST_DYNAMIC_CONFIG_NAMES:
        if read_git_blob(root, ref, PurePosixPath(name)) is not None:
            raise ValueError("dynamic Vitest configuration is not supported")
    config_path = VITEST_CONFIG_PATHS[0]
    content = read_git_blob(root, ref, config_path)
    if content is None:
        config_path = VITEST_CONFIG_PATHS[1]
        content = read_git_blob(root, ref, config_path)
    if content is None:
        raise ValueError("no static Vitest configuration is present")
    try:
        parsed = json.loads(content.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError("Vitest configuration must be valid JSON") from exc
    if config_path.name == "package.json":
        parsed = parsed.get("vitest") if isinstance(parsed, dict) else None
    if not isinstance(parsed, dict):
        raise ValueError("Vitest configuration must be a JSON object")
    return config_path, parsed


def _vitest_config_references(config: object) -> set[PurePosixPath]:
    """Find static local Vitest setup and transform support modules."""
    if not isinstance(config, dict):
        raise ValueError("Vitest configuration must be a JSON object")
    for key in ("workspace", "projects", "plugins", "globalSetup"):
        if config.get(key):
            raise ValueError(f"Vitest {key} is not bound by this adapter")
    resolve = config.get("resolve", {})
    if resolve and not isinstance(resolve, dict):
        raise ValueError("Vitest resolve must be an object")
    if isinstance(resolve, dict) and resolve.get("alias"):
        raise ValueError("Vitest resolve.alias is not bound by this adapter")
    test_config = config.get("test", {})
    if not isinstance(test_config, dict):
        raise ValueError("Vitest test configuration must be an object")
    for key in ("workspace", "projects", "plugins", "globalSetup"):
        if test_config.get(key):
            raise ValueError(f"Vitest {key} is not bound by this adapter")
    if test_config.get("alias"):
        raise ValueError("Vitest test.alias is not bound by this adapter")
    for key in ("testNamePattern", "shard", "watch", "related", "changed"):
        if test_config.get(key):
            raise ValueError(f"Vitest {key} is not allowed by this adapter")
    references: set[PurePosixPath] = set()
    setup = test_config.get("setupFiles", [])
    if isinstance(setup, str):
        setup = [setup]
    if not isinstance(setup, list):
        raise ValueError("Vitest setupFiles must be an array")
    for value in setup:
        if not isinstance(value, str):
            raise ValueError("Vitest setupFiles entry must be a static local path")
        path = _jest_local_path(value)
        if path is None:
            raise ValueError("Vitest setup plugin is not bound by this adapter")
        references.add(path)
    transforms = config.get("transform", {})
    if not isinstance(transforms, dict):
        raise ValueError("Vitest transform must be an object")
    for value in transforms.values():
        if not isinstance(value, str):
            raise ValueError("Vitest transform entry must be a static local path")
        path = _jest_local_path(value)
        if path is None:
            raise ValueError("Vitest transform is not bound by this adapter")
        references.add(path)
    return references


def _vitest_support_closure(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...]
) -> tuple[tuple[PurePosixPath, bytes], ...]:
    """Return static config and transitive local Vitest support modules."""
    config_path, config = _vitest_config(root, ref)
    paths = {config_path}
    pending = list(test_paths) + list(_vitest_config_references(config))
    visited: set[PurePosixPath] = set()
    while pending:
        path = pending.pop()
        if path in visited:
            continue
        visited.add(path)
        path, source = _read_javascript_support_blob(root, ref, path)
        if source is None:
            raise ValueError(f"Vitest support path is missing: {path.as_posix()}")
        paths.add(path)
        pending.extend(_local_javascript_imports(root, ref, path, source) - visited)
    return tuple(
        (path, read_git_blob(root, ref, path))
        for path in sorted(paths)
        if read_git_blob(root, ref, path) is not None
    )


def vitest_validator_config_digest(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...]
) -> str:
    """Hash static Vitest config and executable local support closure."""
    digest = hashlib.sha256()
    for path, content in _vitest_support_closure(root, ref, test_paths):
        digest.update(path.as_posix().encode() + b"\0" + content + b"\0")
    return digest.hexdigest()


def _playwright_config(root: Path, ref: str) -> tuple[PurePosixPath, bytes]:
    """Return the single protected Playwright configuration source."""
    found = [
        PurePosixPath(name) for name in PLAYWRIGHT_CONFIG_NAMES
        if read_git_blob(root, ref, PurePosixPath(name)) is not None
    ]
    if len(found) != 1:
        raise ValueError("exactly one static Playwright configuration is required")
    content = read_git_blob(root, ref, found[0])
    assert content is not None
    return found[0], content


def _playwright_static_config(path: PurePosixPath, source: bytes) -> set[PurePosixPath]:
    """Reject dynamic controls and return literal local config imports."""
    try:
        text = source.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError("Playwright configuration must be UTF-8") from exc
    if re.search(r"\b(process|require|import\s*\(|await|function|=>|\beval\b)\b", text):
        raise ValueError("dynamic Playwright configuration is not supported")
    sensitive_execution_keys = (
        "grep",
        "grepInvert",
        "shard",
        "retries",
        "workers",
        "repeatEach",
    )
    quoted_or_bare = (
        r"(?:\b(?:{keys})\b|['\"](?:{keys})['\"])\s*:"
    )
    if re.search(
        quoted_or_bare.format(keys="|".join(sensitive_execution_keys)),
        text,
    ):
        raise ValueError("Playwright execution filters or retries are not allowed")
    if re.search(r"\b(?:const|let|var)\s+(globalSetup|globalTeardown|reporter|webServer)\b", text):
        raise ValueError("indirect Playwright executable controls are not bound by this adapter")
    if re.search(quoted_or_bare.format(keys="webServer"), text):
        raise ValueError("Playwright webServer is not bound by this adapter")
    if re.search(r"['\"](?:globalSetup|globalTeardown|reporter)['\"]\s*:", text):
        raise ValueError("quoted Playwright executable controls are not bound by this adapter")
    if re.search(r"\b(?:globalSetup|globalTeardown|reporter)\s*:\s*(?!['\"])", text):
        raise ValueError("indirect Playwright executable controls are not bound by this adapter")
    # Parse direct relative imports here; the closure resolver checks each blob.
    references: set[PurePosixPath] = set()
    for item in re.findall(r"(?:from\s+|import\s+)['\"](\.{1,2}/[^'\"]+)['\"]", text):
        reference = _normalize_repo_relative_path(path.parent / PurePosixPath(item))
        if reference is None:
            raise ValueError("Playwright config import escapes the repository")
        references.add(reference)
    for key in ("globalSetup", "globalTeardown", "reporter"):
        for value in re.findall(rf"\b{key}\s*:\s*['\"]([^'\"]+)['\"]", text):
            local = _jest_local_path(value)
            if local is None:
                raise ValueError(f"Playwright {key} is not a static local path")
            references.add(local)
    return references


def _playwright_support_closure(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...]
) -> tuple[tuple[PurePosixPath, bytes], ...]:
    """Bind config, local support, and test imports without executing them."""
    config_path, config_source = _playwright_config(root, ref)
    paths = {config_path}
    pending = list(_playwright_static_config(config_path, config_source)) + list(test_paths)
    visited: set[PurePosixPath] = set()
    while pending:
        path = pending.pop()
        if path in visited:
            continue
        visited.add(path)
        path, source = _read_javascript_support_blob(root, ref, path)
        if source is None:
            raise ValueError(f"Playwright local support path is missing: {path.as_posix()}")
        paths.add(path)
        if path.suffix in _JAVASCRIPT_SUFFIXES:
            pending.extend(_local_javascript_imports(root, ref, path, source) - visited)
            unbound_bare = _unbound_playwright_bare_imports(source)
            if unbound_bare:
                raise ValueError(
                    "Playwright bare package imports are not bound by this adapter: "
                    + ", ".join(sorted(unbound_bare))
                )
            try:
                text = source.decode("utf-8")
            except UnicodeDecodeError as exc:
                raise ValueError(f"Playwright source is not UTF-8: {path.as_posix()}") from exc
            if re.search(r"\b(?:test|describe)\.(?:only|skip|fixme|slow)\s*\(", text):
                raise ValueError("Playwright focused, skipped, fixme, or slow tests are ambiguous")
    return tuple(
        (path, read_git_blob(root, ref, path)) for path in sorted(paths)
        if read_git_blob(root, ref, path) is not None
    )


def playwright_validator_config_digest(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...]
) -> str:
    """Hash Playwright config and every bound local executable dependency."""
    digest = hashlib.sha256()
    for path, content in _playwright_support_closure(root, ref, test_paths):
        digest.update(path.as_posix().encode() + b"\0" + content + b"\0")
    return digest.hexdigest()


def _support_digest(
    root: Path, ref: str, profile: VerificationProfile
) -> tuple[str, tuple[PurePosixPath, ...]]:
    tests = tuple(
        path
        for obligation in profile.obligations
        if obligation.validator_id == "pytest"
        for path in obligation.artifact_paths
    )
    product = tuple(
        path for obligation in profile.obligations
        for path in obligation.code_under_test_paths
    )
    closure = _pytest_support_closure(root, ref, tests, product)
    digest = hashlib.sha256()
    for path, content in closure:
        digest.update(path.as_posix().encode() + b"\0" + content + b"\0")
    return digest.hexdigest(), tuple(path for path, _content in closure)


def _jest_support_digest(
    root: Path, ref: str, profile: VerificationProfile
) -> tuple[str, tuple[PurePosixPath, ...]]:
    """Hash the protected static Jest support closure for a profile."""
    tests = tuple(
        path
        for obligation in profile.obligations
        if obligation.validator_id == "jest"
        for path in obligation.artifact_paths
    )
    try:
        closure = _jest_support_closure(root, ref, tests)
    except ValueError:
        return "invalid-jest-closure", ()
    digest = hashlib.sha256()
    for path, content in closure:
        digest.update(path.as_posix().encode() + b"\0" + content + b"\0")
    return digest.hexdigest(), tuple(path for path, _content in closure)


def _vitest_support_digest(
    root: Path, ref: str, profile: VerificationProfile
) -> tuple[str, tuple[PurePosixPath, ...]]:
    """Hash the protected static Vitest support closure for a profile."""
    tests = tuple(
        path
        for obligation in profile.obligations
        if obligation.validator_id == "vitest"
        for path in obligation.artifact_paths
    )
    try:
        closure = _vitest_support_closure(root, ref, tests)
    except ValueError:
        return "invalid-vitest-closure", ()
    digest = hashlib.sha256()
    for path, content in closure:
        digest.update(path.as_posix().encode() + b"\0" + content + b"\0")
    return digest.hexdigest(), tuple(path for path, _content in closure)


def _playwright_support_digest(
    root: Path, ref: str, profile: VerificationProfile
) -> tuple[str, tuple[PurePosixPath, ...]]:
    """Hash the protected Playwright configuration and source closure."""
    tests = tuple(
        path for obligation in profile.obligations
        if obligation.validator_id == "playwright"
        for path in obligation.artifact_paths
    )
    try:
        closure = _playwright_support_closure(root, ref, tests)
    except ValueError:
        return "invalid-playwright-closure", ()
    digest = hashlib.sha256()
    for path, content in closure:
        digest.update(path.as_posix().encode() + b"\0" + content + b"\0")
    return digest.hexdigest(), tuple(path for path, _content in closure)


def _config_loads_plugin(root: Path, ref: str) -> bool:
    """Reject repository-configured plugins until profiles bind plugin identities."""
    for path in PYTEST_CONFIG_PATHS:
        content = read_git_blob(root, ref, path)
        if content is None:
            continue
        try:
            text = content.decode("utf-8")
        except UnicodeDecodeError:
            return True
        try:
            tokens = shlex.split(text.replace("=", " = "), comments=True)
        except ValueError:
            return True
        for index, token in enumerate(tokens):
            if token == "-p" and index + 1 < len(tokens):
                return True
            if token.startswith("-p=") or (token.startswith("-p") and len(token) > 2):
                return True
    return False


def _managed_subprocess(
    command: list[str], *, cwd: Path, timeout: int, env: dict[str, str],
    writable_roots: tuple[Path, ...],
) -> tuple[subprocess.CompletedProcess[str], bool]:
    """Run an untrusted command in a networkless sandbox and reap its group."""
    return run_supervised(command, cwd=cwd, timeout=timeout, env=env,
                          writable_roots=writable_roots)


def runner_identity_digest(
    profile: VerificationProfile, *, root: Path | None = None, ref: str = "HEAD",
    config: RunnerConfig = RunnerConfig(),
) -> str:
    """Bind evidence to protected adapters, configs, and exact artifact scopes."""
    payload = {
        "tool_version": TRUSTED_RUNNER_VERSION,
        "pytest_command": [
            sys.executable,
            "-m",
            "pytest",
            "-q",
            *PYTEST_PROTECTED_FLAGS,
            "<protected-node-id>",
            "--junitxml=<trusted-temp-path>",
        ],
        "pytest_collection_command": [
            sys.executable,
            "-m",
            "pytest",
            "--collect-only",
            "-q",
            "--strict-config",
            "--strict-markers",
            "-p",
            "<checker-owned-pytest-probe>",
            "<test-path>",
        ],
        "pytest_environment": {"PYTEST_DISABLE_PLUGIN_AUTOLOAD": "1"},
        "vitest_command": [
            "<node>",
            "<local-vitest-binary>",
            "run",
            "<protected-test-path>",
            "--config=<protected-config-path>",
            "--reporter=json",
            "--outputFile=<trusted-temp-path>",
        ],
        "vitest_environment": {"NODE_ENV": "test"},
        "playwright_command": ["<node>", "<local-playwright-cli>", "test", "<protected-test-path>", "--config=<protected-config-path>", "--reporter=json"],
        "playwright_environment": {"NODE_ENV": "test"},
        "obligations": [
            {
                "id": item.obligation_id,
                "kind": item.kind,
                "validator": item.validator_id,
                "config": item.validator_config_digest,
                "paths": [path.as_posix() for path in item.artifact_paths],
            }
            for item in profile.obligations
        ],
    }
    if root is not None:
        payload["support_closure_digest"] = hashlib.sha256(
            (
                _support_digest(root, ref, profile)[0]
                + _jest_support_digest(root, ref, profile)[0]
                + _vitest_support_digest(root, ref, profile)[0]
                + _playwright_support_digest(root, ref, profile)[0]
            ).encode()
        ).hexdigest()
        payload["validator_command_digest"] = _validator_command_identity_digest(
            root, config
        )
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def _path_is_relative_to(path: Path, parent: Path) -> bool:
    """Return whether path is inside parent across supported Python versions."""
    try:
        path.relative_to(parent)
    except ValueError:
        return False
    return True


def _file_identity(path: Path) -> str:
    """Return a stable identity digest for an executable validator file."""
    try:
        data = path.read_bytes()
    except OSError:
        data = b"<unreadable>"
    return hashlib.sha256(str(path).encode() + b"\0" + data).hexdigest()


def _directory_identity(path: Path) -> str:
    """Return a stable digest for files under a protected dependency directory."""
    digest = hashlib.sha256()
    if not path.is_dir():
        digest.update(str(path).encode() + b"\0<missing>")
        return digest.hexdigest()
    for item in sorted(child for child in path.rglob("*") if child.is_file()):
        try:
            data = item.read_bytes()
        except OSError:
            data = b"<unreadable>"
        digest.update(item.relative_to(path).as_posix().encode() + b"\0" + data + b"\0")
    return digest.hexdigest()


def _command_part_identity(root: Path, part: str) -> str:
    """Return literal argv text or a digest for an explicit path operand."""
    path = Path(part).expanduser()
    if not path.is_absolute() and "/" not in part:
        return part
    resolved = (path if path.is_absolute() else root / path).resolve()
    return _file_identity(resolved) if resolved.exists() else part


def _is_script_like_operand(value: str) -> bool:
    """Return true for argv operands that are likely executable script paths."""
    return Path(value).suffix in _JAVASCRIPT_SUFFIXES + (".py",)


def _external_node_modules_root(
    root: Path, command: tuple[str, ...] | None
) -> Path | None:
    """Derive a non-candidate node_modules root from explicit validator argv."""
    if command is None:
        return None
    candidate_root = root.resolve()
    for part in command:
        path = Path(part).expanduser()
        if not path.is_absolute():
            continue
        resolved = path.resolve()
        if _path_is_relative_to(resolved, candidate_root):
            continue
        parts = resolved.parts
        if "node_modules" not in parts:
            continue
        index = parts.index("node_modules")
        node_modules = Path(*parts[: index + 1])
        if node_modules.is_dir() and not _path_is_relative_to(
            node_modules.resolve(), candidate_root
        ):
            return node_modules
    return None


def _validator_command_identity_digest(root: Path, config: RunnerConfig) -> str:
    """Bind explicitly supplied validator commands to signed runner evidence."""
    payload: dict[str, object] = {}
    if config.jest_command is not None:
        payload["jest"] = [
            _command_part_identity(root, part) for part in config.jest_command
        ]
    if config.vitest_command is not None:
        payload["vitest"] = [
            _command_part_identity(root, part) for part in config.vitest_command
        ]
    if config.playwright_command is not None:
        payload["playwright"] = [
            _command_part_identity(root, part) for part in config.playwright_command
        ]
        node_modules = _external_node_modules_root(root, config.playwright_command)
        if node_modules is not None:
            payload["playwright_dependency_environment"] = {
                "node_modules": str(node_modules),
                "node_modules_sha256": _directory_identity(node_modules),
            }
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def _changed_paths(
    root: Path,
    base_sha: str,
    head_sha: str,
    paths: tuple[PurePosixPath, ...],
) -> set[str]:
    if not paths:
        return set()
    changed = set()
    revisions = [(base_sha, head_sha), (head_sha,)]
    for revision in revisions:
        result = subprocess.run(
            [
                "git",
                "diff",
                "--name-only",
                *revision,
                "--",
                *(path.as_posix() for path in paths),
            ],
            cwd=root,
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode != 0:
            return {path.as_posix() for path in paths}
        changed.update(line for line in result.stdout.splitlines() if line)
    return changed


def _junit_outcome(
    path: Path, returncode: int, output: str, minimum_tests: int
) -> tuple[EvidenceOutcome, str]:
    try:
        root = ET.parse(path).getroot()
    except (ET.ParseError, OSError) as exc:
        return EvidenceOutcome.COLLECTION_ERROR, f"cannot parse JUnit result: {exc}"
    suites = [root] if root.tag == "testsuite" else list(root.iter("testsuite"))
    totals = {
        key: sum(int(suite.attrib.get(key, "0")) for suite in suites)
        for key in ("tests", "failures", "errors", "skipped")
    }
    if totals["tests"] == 0:
        outcome, detail = EvidenceOutcome.NOT_COLLECTED, "zero tests collected"
    elif totals["tests"] < minimum_tests:
        outcome, detail = EvidenceOutcome.NOT_COLLECTED, (
            f"executed {totals['tests']} of at least {minimum_tests} declared tests"
        )
    elif " deselected" in output:
        outcome, detail = (
            EvidenceOutcome.NOT_COLLECTED,
            "pytest deselected declared tests",
        )
    elif "XPASS" in output:
        outcome, detail = EvidenceOutcome.XFAIL, "pytest reported an unexpected pass"
    elif totals["errors"]:
        outcome, detail = EvidenceOutcome.ERROR, f"{totals['errors']} test errors"
    elif totals["failures"] or returncode:
        outcome, detail = EvidenceOutcome.FAIL, f"{totals['failures']} test failures"
    elif totals["skipped"]:
        outcome, detail = (
            EvidenceOutcome.SKIP,
            f"{totals['skipped']} tests skipped or xfailed",
        )
    else:
        outcome, detail = EvidenceOutcome.PASS, f"{totals['tests']} tests passed"
    return outcome, detail


def _pytest_environment(home: Path) -> dict[str, str]:
    """Return the protected credential-free pytest process environment."""
    return untrusted_child_environment(
        home=home,
        extra={"PYTEST_DISABLE_PLUGIN_AUTOLOAD": "1", "PYTHONNOUSERSITE": "1"},
        drop={"PYTEST_ADDOPTS", "PYTHONPATH"},
    )


def _trusted_probe_plugin(directory: Path) -> tuple[str, Path]:
    """Create a unique plugin shim that loads the checker-owned probe by path."""
    plugin_name = "pdd_checker_pytest_probe"
    plugin = directory / f"{plugin_name}.py"
    plugin.write_text(
        "\n".join(
            (
                "import importlib.util",
                "_SPEC = importlib.util.spec_from_file_location(",
                f"    {plugin_name!r}, {json.dumps(str(_CHECKER_PYTEST_PROBE))}",
                ")",
                "if _SPEC is None or _SPEC.loader is None:",
                "    raise ImportError('checker pytest probe is unavailable')",
                "_MODULE = importlib.util.module_from_spec(_SPEC)",
                "_SPEC.loader.exec_module(_MODULE)",
                "pytest_collection_modifyitems = _MODULE.pytest_collection_modifyitems",
                "",
            )
        ),
        encoding="utf-8",
    )
    return plugin_name, directory


def _checker_probe_digest() -> str:
    """Return the digest of the checker-owned collection probe bytes."""
    return hashlib.sha256(_CHECKER_PYTEST_PROBE.read_bytes()).hexdigest()


def _trusted_collection_runner(
    directory: Path,
    root: Path,
    pytest_args: list[str],
) -> Path:
    """Create a checker-owned pytest entrypoint that imports the probe by path."""
    runner = directory / "run_collection.py"
    runner.write_text(
        "\n".join(
            (
                "import importlib.util",
                "import os",
                "import sys",
                "",
                f"_ROOT = {json.dumps(str(root))}",
                f"_PROBE = {json.dumps(str(_CHECKER_PYTEST_PROBE))}",
                f"_ARGS = {json.dumps(pytest_args)}",
                "",
                "os.chdir(_ROOT)",
                "_SPEC = importlib.util.spec_from_file_location(",
                "    '_pdd_checker_pytest_probe_abs', _PROBE",
                ")",
                "if _SPEC is None or _SPEC.loader is None:",
                "    raise ImportError('checker pytest probe is unavailable')",
                "_MODULE = importlib.util.module_from_spec(_SPEC)",
                "sys.modules['_pdd_checker_pytest_probe_abs'] = _MODULE",
                "_SPEC.loader.exec_module(_MODULE)",
                "",
                "import pytest",
                "if _ROOT not in sys.path:",
                "    sys.path.insert(0, _ROOT)",
                "raise SystemExit(pytest.main(_ARGS, plugins=[_MODULE]))",
                "",
            )
        ),
        encoding="utf-8",
    )
    return runner


def _jest_environment(home: Path) -> dict[str, str]:
    """Return a credential-free, non-ambient environment for Jest."""
    return {
        key: value
        for key, value in os.environ.items()
        if not any(marker in key.upper() for marker in SECRET_ENV_MARKERS)
        and not key.startswith(("JEST_", "NODE_", "npm_config_", "NPM_CONFIG_"))
        and key not in {"HOME", "XDG_CONFIG_HOME", "XDG_CACHE_HOME"}
    } | {
        "HOME": str(home),
        "XDG_CONFIG_HOME": str(home / "config"),
        "XDG_CACHE_HOME": str(home / "cache"),
        "NODE_ENV": "test",
    }


def _jest_command(config: RunnerConfig) -> tuple[str, ...] | None:
    """Return an explicit local Jest argv prefix; never invoke an npm script."""
    if config.jest_command is not None:
        return config.jest_command
    return None


def _command_uses_candidate_checkout(root: Path, command: tuple[str, ...]) -> bool:
    """Return true when any explicit command path is inside the candidate repo."""
    candidate_root = root.resolve()
    for part in command:
        path = Path(part).expanduser()
        if not path.is_absolute() and "/" not in part:
            continue
        resolved = path.resolve() if path.is_absolute() else (root / path).resolve()
        if _path_is_relative_to(resolved, candidate_root):
            return True
    return False


def _protected_command_error(root: Path, command: tuple[str, ...]) -> str | None:
    """Return a fail-closed reason for unprotected explicit validator argv."""
    if not command:
        return "explicit validator command is empty"
    candidate_root = root.resolve()
    path_operands: list[Path] = []
    executable = Path(command[0]).expanduser()
    if not executable.is_absolute():
        return "explicit validator command executable must be an absolute path"
    path_operands.append(executable)
    expect_module_operand = False
    for part in command[1:]:
        if expect_module_operand:
            if "/" not in part:
                return (
                    "pathless validator module operand is not trusted; use an "
                    "absolute external path or protected module launcher"
                )
            expect_module_operand = False
        if part == "-m":
            expect_module_operand = True
            continue
        if part.startswith("-"):
            continue
        path = Path(part).expanduser()
        if not path.is_absolute() and "/" not in part:
            if _is_script_like_operand(part):
                return (
                    "pathless validator script operand is not trusted; use an "
                    "absolute external path"
                )
            continue
        path_operands.append(path if path.is_absolute() else root / path)
    for operand in path_operands:
        resolved = operand.resolve()
        if _path_is_relative_to(resolved, candidate_root):
            return "explicit validator command inside the candidate checkout is not trusted"
    return None


_JEST_REPORTER = """class PddTrustedReporter {
  constructor() { this.tests = []; }
  onTestResult(test, result) {
    for (const assertion of result.testResults || []) {
      const names = [...(assertion.ancestorTitles || []), assertion.title].join(' > ');
      this.tests.push({identity: require('path').relative(process.cwd(), test.path) + '::' + names, status: assertion.status});
    }
  }
  onRunComplete() { require('fs').writeFileSync(process.env.PDD_TRUSTED_JEST_OUTPUT, JSON.stringify({tests: this.tests})); }
}
module.exports = PddTrustedReporter;
"""


def _jest_result(
    output: Path, returncode: int, expected: tuple[str, ...] | None
) -> tuple[EvidenceOutcome, str, tuple[str, ...]]:
    """Validate trusted reporter data and normalize every non-pass state."""
    try:
        payload = json.loads(output.read_text(encoding="utf-8"))
        tests = payload["tests"]
        if not isinstance(tests, list) or not all(
            isinstance(item, dict)
            and isinstance(item.get("identity"), str)
            and isinstance(item.get("status"), str)
            for item in tests
        ):
            raise ValueError("malformed Jest reporter payload")
    except (OSError, ValueError, json.JSONDecodeError, KeyError):
        return EvidenceOutcome.COLLECTION_ERROR, "trusted Jest reporter produced malformed JSON", ()
    identities = tuple(sorted(item["identity"] for item in tests))
    if not identities:
        return EvidenceOutcome.NOT_COLLECTED, "zero protected Jest test identities collected", ()
    if len(set(identities)) != len(identities):
        return EvidenceOutcome.COLLECTION_ERROR, "Jest reporter emitted duplicate test identities", ()
    if expected is not None and identities != expected:
        return EvidenceOutcome.QUARANTINED, "checked-head Jest identities differ from protected base", identities
    statuses = {item["status"] for item in tests}
    if statuses - {"passed", "failed", "pending", "todo", "skipped", "disabled"}:
        return EvidenceOutcome.COLLECTION_ERROR, "Jest reporter emitted an unsupported status", identities
    if returncode or "failed" in statuses:
        return EvidenceOutcome.FAIL, "Jest reported failed protected tests", identities
    if statuses - {"passed"}:
        return EvidenceOutcome.SKIP, "Jest reported skipped or todo protected tests", identities
    return EvidenceOutcome.PASS, f"{len(identities)} protected Jest tests passed", identities


def _run_jest(
    root: Path, paths: tuple[PurePosixPath, ...], timeout_seconds: int,
    config: RunnerConfig, expected: tuple[str, ...] | None = None,
) -> tuple[RunnerExecution, tuple[str, ...]]:
    """Run exact protected Jest paths using a temporary trusted reporter."""
    command_prefix = _jest_command(config)
    if command_prefix is None:
        if (root / "node_modules" / "jest" / "bin" / "jest.js").is_file():
            return RunnerExecution("jest", EvidenceOutcome.ERROR, "jest-untrusted", "candidate node_modules Jest runner is not trusted"), ()
        return RunnerExecution("jest", EvidenceOutcome.ERROR, "jest-unavailable", "no local Jest binary is available"), ()
    command_error = _protected_command_error(root, command_prefix)
    if command_error is not None:
        return RunnerExecution(
            "jest", EvidenceOutcome.ERROR, "jest-untrusted", command_error
        ), ()
    try:
        config_path, _config_data = _jest_config(root, "HEAD")
    except ValueError as exc:
        return RunnerExecution("jest", EvidenceOutcome.ERROR, "jest-config", str(exc)), ()
    with tempfile.TemporaryDirectory(prefix="pdd-trusted-jest-") as directory:
        temporary = Path(directory)
        reporter = temporary / "reporter.cjs"
        output = temporary / "results.json"
        reporter.write_text(_JEST_REPORTER, encoding="utf-8")
        command = [*command_prefix, *(path.as_posix() for path in paths), "--runInBand", f"--config={root / config_path}", f"--reporters={reporter}"]
        digest = hashlib.sha256(json.dumps(command, separators=(",", ":")).encode()).hexdigest()
        try:
            result = subprocess.run(command, cwd=root, capture_output=True, text=True, check=False, timeout=timeout_seconds, env=_jest_environment(temporary) | {"PDD_TRUSTED_JEST_OUTPUT": str(output)})
        except subprocess.TimeoutExpired:
            return RunnerExecution("jest", EvidenceOutcome.TIMEOUT, digest, "Jest execution timed out"), ()
        outcome, detail, identities = _jest_result(output, result.returncode, expected)
        return RunnerExecution("jest", outcome, digest, detail), identities


def _vitest_command(config: RunnerConfig) -> tuple[str, ...] | None:
    """Return an explicit local Vitest argv prefix; never invoke an npm script."""
    if config.vitest_command is not None:
        return config.vitest_command
    return None


def _vitest_environment(home: Path) -> dict[str, str]:
    """Return a credential-free, non-ambient environment for Vitest."""
    return {
        key: value
        for key, value in os.environ.items()
        if not any(marker in key.upper() for marker in SECRET_ENV_MARKERS)
        and not key.startswith(("VITEST_", "NODE_", "npm_config_", "NPM_CONFIG_"))
        and key not in {"HOME", "XDG_CONFIG_HOME", "XDG_CACHE_HOME"}
    } | {
        "HOME": str(home),
        "XDG_CONFIG_HOME": str(home / "config"),
        "XDG_CACHE_HOME": str(home / "cache"),
        "NODE_ENV": "test",
    }


def _vitest_result(
    root: Path, output: Path, returncode: int, expected: tuple[str, ...] | None
) -> tuple[EvidenceOutcome, str, tuple[str, ...]]:
    """Validate Vitest JSON output and normalize every non-pass state."""
    try:
        payload = json.loads(output.read_text(encoding="utf-8"))
        tests = payload.get("tests")
        if tests is None:
            tests = [
                {
                    "identity": (
                        Path(item["name"]).resolve().relative_to(root.resolve()).as_posix()
                        + "::"
                        + assertion.get("fullName", assertion["title"])
                    ),
                    "status": assertion["status"],
                }
                for item in payload["testResults"]
                for assertion in item["assertionResults"]
            ]
        if not isinstance(tests, list) or not all(
            isinstance(item, dict)
            and isinstance(item.get("identity"), str)
            and isinstance(item.get("status"), str)
            for item in tests
        ):
            raise ValueError("malformed Vitest reporter payload")
    except (OSError, ValueError, json.JSONDecodeError, KeyError):
        return EvidenceOutcome.COLLECTION_ERROR, "Vitest reporter produced malformed JSON", ()
    identities = tuple(sorted(item["identity"] for item in tests))
    if not identities:
        return EvidenceOutcome.NOT_COLLECTED, "zero protected Vitest test identities collected", ()
    if len(set(identities)) != len(identities):
        return EvidenceOutcome.COLLECTION_ERROR, "Vitest reporter emitted duplicate test identities", ()
    if expected is not None and identities != expected:
        return EvidenceOutcome.QUARANTINED, "checked-head Vitest identities differ from protected base", identities
    statuses = {item["status"] for item in tests}
    if statuses - {"passed", "failed", "pending", "todo", "skipped", "disabled"}:
        return EvidenceOutcome.COLLECTION_ERROR, "Vitest reporter emitted an unsupported status", identities
    if returncode or "failed" in statuses:
        return EvidenceOutcome.FAIL, "Vitest reported failed protected tests", identities
    if statuses - {"passed"}:
        return EvidenceOutcome.SKIP, "Vitest reported skipped or todo protected tests", identities
    return EvidenceOutcome.PASS, f"{len(identities)} protected Vitest tests passed", identities


def _run_vitest(
    root: Path,
    paths: tuple[PurePosixPath, ...],
    timeout_seconds: int,
    config: RunnerConfig,
    expected: tuple[str, ...] | None = None,
    command_root: Path | None = None,
) -> tuple[RunnerExecution, tuple[str, ...]]:
    """Run exact protected Vitest paths with the built-in JSON reporter."""
    tool_root = command_root or root
    command_prefix = _vitest_command(config)
    if command_prefix is None:
        if (tool_root / "node_modules" / "vitest" / "vitest.mjs").is_file():
            return RunnerExecution("vitest", EvidenceOutcome.ERROR, "vitest-untrusted", "candidate node_modules Vitest runner is not trusted"), ()
        return RunnerExecution("vitest", EvidenceOutcome.ERROR, "vitest-unavailable", "no local Vitest binary is available"), ()
    command_error = _protected_command_error(root, command_prefix)
    if command_error is not None:
        return RunnerExecution(
            "vitest", EvidenceOutcome.ERROR, "vitest-untrusted", command_error
        ), ()
    try:
        config_path, _config_data = _vitest_config(root, "HEAD")
    except ValueError as exc:
        return RunnerExecution("vitest", EvidenceOutcome.ERROR, "vitest-config", str(exc)), ()
    with tempfile.TemporaryDirectory(prefix="pdd-trusted-vitest-") as directory:
        temporary = Path(directory)
        output = temporary / "results.json"
        command = [
            *command_prefix,
            "run",
            *(path.as_posix() for path in paths),
            f"--config={root / config_path}",
            "--reporter=json",
            f"--outputFile={output}",
        ]
        digest = hashlib.sha256(json.dumps(command, separators=(",", ":")).encode()).hexdigest()
        try:
            result = subprocess.run(
                command,
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
                timeout=timeout_seconds,
                env=_vitest_environment(temporary)
                | {"PDD_TRUSTED_VITEST_OUTPUT": str(output)},
            )
        except subprocess.TimeoutExpired:
            return RunnerExecution("vitest", EvidenceOutcome.TIMEOUT, digest, "Vitest execution timed out"), ()
        outcome, detail, identities = _vitest_result(root, output, result.returncode, expected)
        return RunnerExecution("vitest", outcome, digest, detail), identities


def _playwright_command(config: RunnerConfig) -> tuple[str, ...] | None:
    """Return the checked-in local Playwright CLI, never an npm script."""
    if config.playwright_command is not None:
        return config.playwright_command
    return None


def _playwright_candidate_toolchain(root: Path) -> bool:
    """Return whether candidate checkout infrastructure would affect Playwright."""
    node_modules = root / "node_modules"
    return (
        (node_modules / "@playwright" / "test").exists()
        or (node_modules / "playwright-core" / ".local-browsers").exists()
    )


def _playwright_environment(
    home: Path, node_modules: Path | None
) -> dict[str, str]:
    """Return an isolated credential-free environment for Playwright."""
    environment = {
        key: value for key, value in os.environ.items()
        if not any(marker in key.upper() for marker in SECRET_ENV_MARKERS)
        and not key.startswith(("PLAYWRIGHT_", "NODE_", "npm_config_", "NPM_CONFIG_"))
        and key not in {"HOME", "XDG_CONFIG_HOME", "XDG_CACHE_HOME"}
    } | {
        "HOME": str(home), "XDG_CONFIG_HOME": str(home / "config"),
        "XDG_CACHE_HOME": str(home / "cache"), "NODE_ENV": "test",
    }
    if node_modules is not None and node_modules.is_dir():
        environment["NODE_PATH"] = str(node_modules)
        local_browsers = node_modules / "playwright-core" / ".local-browsers"
        if local_browsers.is_dir():
            environment["PLAYWRIGHT_BROWSERS_PATH"] = "0"
    return environment


def _playwright_result(
    root: Path, output: str, returncode: int, expected: tuple[str, ...] | None,
    collection: bool = False,
) -> tuple[EvidenceOutcome, str, tuple[str, ...]]:
    """Normalize JSON reporter output to project, file, title-path identities."""
    try:
        payload = json.loads(output)
        tests = payload.get("tests")
        if tests is None:
            tests = []
            def visit(suite: object, parents: tuple[str, ...] = ()) -> None:
                if not isinstance(suite, dict):
                    raise ValueError("malformed Playwright suite")
                title = suite.get("title", "")
                next_parents = parents + ((title,) if isinstance(title, str) and title else ())
                for spec in suite.get("specs", []):
                    if not isinstance(spec, dict):
                        raise ValueError("malformed Playwright spec")
                    spec_file = Path(spec["file"])
                    if not spec_file.is_absolute():
                        spec_file = Path(os.path.abspath(root / spec_file))
                    filename = spec_file.resolve().relative_to(root.resolve()).as_posix()
                    title_path = " > ".join(next_parents + (spec["title"],))
                    for item in spec.get("tests", []):
                        result = (item.get("results") or [{}])[-1]
                        tests.append({
                            "identity": f"{item['projectName']}::{filename}::{title_path}",
                            "status": result.get("status", "passed" if collection else "skipped"),
                        })
                for child in suite.get("suites", []):
                    visit(child, next_parents)
            for suite in payload.get("suites", []):
                visit(suite)
        if not isinstance(tests, list) or not all(
            isinstance(item, dict) and isinstance(item.get("identity"), str)
            and isinstance(item.get("status"), str) for item in tests
        ):
            raise ValueError("malformed Playwright reporter payload")
    except (KeyError, TypeError, ValueError, json.JSONDecodeError):
        return EvidenceOutcome.COLLECTION_ERROR, "Playwright JSON reporter produced malformed JSON", ()
    identities = tuple(sorted(item["identity"] for item in tests))
    if not identities:
        return EvidenceOutcome.NOT_COLLECTED, "zero protected Playwright test identities collected", ()
    if len(set(identities)) != len(identities):
        return EvidenceOutcome.COLLECTION_ERROR, "Playwright reporter emitted duplicate test identities", ()
    if expected is not None and identities != expected:
        return EvidenceOutcome.QUARANTINED, "checked-head Playwright identities differ from protected base", identities
    if collection:
        if returncode:
            return EvidenceOutcome.COLLECTION_ERROR, "Playwright collection failed", identities
        return EvidenceOutcome.PASS, f"{len(identities)} protected Playwright tests collected", identities
    statuses = {item["status"] for item in tests}
    if statuses - {"passed", "failed", "skipped", "timedOut", "interrupted"}:
        return EvidenceOutcome.COLLECTION_ERROR, "Playwright reporter emitted an unsupported status", identities
    if "timedOut" in statuses:
        return EvidenceOutcome.TIMEOUT, "Playwright reported a timed out protected test", identities
    if returncode or "failed" in statuses or "interrupted" in statuses:
        return EvidenceOutcome.FAIL, "Playwright reported failed protected tests", identities
    if statuses - {"passed"}:
        return EvidenceOutcome.SKIP, "Playwright reported skipped protected tests", identities
    return EvidenceOutcome.PASS, f"{len(identities)} protected Playwright tests passed", identities


def _run_playwright(
    root: Path, paths: tuple[PurePosixPath, ...], timeout_seconds: int,
    config: RunnerConfig, expected: tuple[str, ...] | None = None,
    command_root: Path | None = None, collection: bool = False,
) -> tuple[RunnerExecution, tuple[str, ...]]:
    """Execute exact paths through Playwright's JSON reporter without filters."""
    tool_root = command_root or root
    if _playwright_candidate_toolchain(tool_root):
        return RunnerExecution("playwright", EvidenceOutcome.ERROR, "playwright-untrusted", "candidate node_modules Playwright toolchain is not trusted"), ()
    prefix = _playwright_command(config)
    if prefix is None:
        return RunnerExecution("playwright", EvidenceOutcome.ERROR, "playwright-unavailable", "no local Playwright CLI is available"), ()
    command_error = _protected_command_error(root, prefix)
    if command_error is not None:
        return RunnerExecution(
            "playwright", EvidenceOutcome.ERROR, "playwright-untrusted", command_error
        ), ()
    node_modules = _external_node_modules_root(root, prefix)
    try:
        config_path, _source = _playwright_config(root, "HEAD")
    except ValueError as exc:
        return RunnerExecution("playwright", EvidenceOutcome.ERROR, "playwright-config", str(exc)), ()
    command = [*prefix, "test", *(path.as_posix() for path in paths), f"--config={root / config_path}", "--reporter=json"]
    if collection:
        command.append("--list")
    digest = hashlib.sha256(json.dumps(command, separators=(",", ":")).encode()).hexdigest()
    with tempfile.TemporaryDirectory(prefix="pdd-trusted-playwright-") as directory:
        try:
            result = subprocess.run(
                command,
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
                timeout=timeout_seconds,
                env=_playwright_environment(
                    Path(directory),
                    node_modules,
                ),
            )
        except subprocess.TimeoutExpired:
            return RunnerExecution("playwright", EvidenceOutcome.TIMEOUT, digest, "Playwright execution timed out"), ()
    outcome, detail, identities = _playwright_result(
        root, result.stdout, result.returncode, expected, collection
    )
    return RunnerExecution("playwright", outcome, digest, detail), identities


def _run_test_node(
    root: Path,
    node_id: str,
    timeout_seconds: int,
) -> RunnerExecution:
    command = [
        sys.executable,
        "-m",
        "pytest",
        "-q",
        *PYTEST_PROTECTED_FLAGS,
        node_id,
    ]
    command_digest = hashlib.sha256(
        json.dumps(command, separators=(",", ":")).encode()
    ).hexdigest()
    with tempfile.TemporaryDirectory(prefix="pdd-trusted-runner-") as directory:
        temporary = Path(directory)
        home = temporary / "home"
        home.mkdir(mode=0o700)
        junit = temporary / "junit.xml"
        result, surviving = _managed_subprocess(
            [*command, f"--junitxml={junit}"], cwd=root,
            timeout=timeout_seconds, env=_pytest_environment(home),
            writable_roots=(temporary,),
        )
        if result.returncode == 124:
            return RunnerExecution(
                node_id,
                EvidenceOutcome.TIMEOUT,
                command_digest,
                "test execution timed out",
            )
        if surviving:
            return RunnerExecution(
                node_id, EvidenceOutcome.ERROR, command_digest,
                "validator left a surviving process-group descendant",
            )
        outcome, detail = _junit_outcome(
            junit,
            result.returncode,
            result.stdout + "\n" + result.stderr,
            1,
        )
        return RunnerExecution(node_id, outcome, command_digest, detail)


def _collect_node_ids(
    root: Path,
    path: PurePosixPath,
    timeout_seconds: int,
) -> tuple[RunnerExecution, tuple[str, ...]]:
    # pylint: disable=too-many-locals
    """Collect exact pytest node IDs through the protected adapter."""
    with tempfile.TemporaryDirectory(prefix="pdd-trusted-collection-") as directory:
        temporary = Path(directory)
        home = temporary / "home"
        home.mkdir(mode=0o700)
        collection_output = temporary / "node-ids.json"
        pytest_args = [
            "--collect-only",
            "-q",
            "--strict-config",
            "--strict-markers",
            "-p",
            "no:cacheprovider",
            path.as_posix(),
        ]
        runner = _trusted_collection_runner(temporary, root, pytest_args)
        command = [sys.executable, str(runner)]
        digest = hashlib.sha256(
            json.dumps(
                {
                    "argv": [sys.executable, "pdd-trusted-collection-runner"],
                    "pytest_args": pytest_args,
                    "probe_path": str(_CHECKER_PYTEST_PROBE),
                    "probe_sha256": _checker_probe_digest(),
                },
                separators=(",", ":"),
                sort_keys=True,
            ).encode()
        ).hexdigest()
        result, surviving = _managed_subprocess(
            command, cwd=temporary, timeout=timeout_seconds,
            env=_pytest_environment(home) | {
                "PDD_TRUSTED_COLLECTION_OUTPUT": str(collection_output),
            }, writable_roots=(temporary,),
        )
        if result.returncode == 124:
            return (
                RunnerExecution(
                    path.as_posix(),
                    EvidenceOutcome.TIMEOUT,
                    digest,
                    "test collection timed out",
                ),
                (),
            )
        if surviving:
            return (
                RunnerExecution(
                    path.as_posix(), EvidenceOutcome.COLLECTION_ERROR, digest,
                    "collection left a surviving process-group descendant",
                ), (),
            )
        try:
            payload = json.loads(collection_output.read_text(encoding="utf-8"))
            if not isinstance(payload, list) or not all(
                isinstance(item, str) for item in payload
            ):
                raise ValueError("node ID payload is malformed")
            node_ids = tuple(sorted(payload))
        except (OSError, ValueError, json.JSONDecodeError):
            return (
                RunnerExecution(
                    path.as_posix(),
                    EvidenceOutcome.COLLECTION_ERROR,
                    digest,
                    "trusted collection probe produced no valid node IDs: "
                    + (result.stderr or result.stdout)[-500:],
                ),
                (),
            )
        if not node_ids and result.returncode in {0, 5}:
            outcome = EvidenceOutcome.NOT_COLLECTED
            detail = "zero protected node IDs collected"
        elif result.returncode != 0:
            outcome = EvidenceOutcome.COLLECTION_ERROR
            detail = "protected sandbox rejected pytest collection"
        else:
            outcome = EvidenceOutcome.PASS
            detail = f"{len(node_ids)} protected node IDs collected"
        return RunnerExecution(path.as_posix(), outcome, digest, detail), node_ids


def _collect_at_base(
    root: Path,
    base_sha: str,
    paths: tuple[PurePosixPath, ...],
    timeout_seconds: int,
) -> tuple[tuple[RunnerExecution, ...], tuple[str, ...]]:
    """Collect node IDs from a fresh exact protected-base clone."""
    with tempfile.TemporaryDirectory(prefix="pdd-runner-protected-base-") as directory:
        clone = Path(directory) / "repository"
        clone_result = subprocess.run(
            ["git", "clone", "-q", "--no-local", "--no-checkout", str(root), str(clone)],
            capture_output=True,
            text=True,
            check=False,
        )
        if clone_result.returncode != 0:
            error = RunnerExecution(
                "protected-base-collection",
                EvidenceOutcome.COLLECTION_ERROR,
                hashlib.sha256(base_sha.encode()).hexdigest(),
                "cannot create protected-base runner clone",
            )
            return (error,), ()
        checkout = subprocess.run(
            ["git", "checkout", "-q", "--detach", base_sha],
            cwd=clone,
            capture_output=True,
            check=False,
        )
        if checkout.returncode != 0:
            error = RunnerExecution(
                "protected-base-collection",
                EvidenceOutcome.COLLECTION_ERROR,
                hashlib.sha256(base_sha.encode()).hexdigest(),
                "cannot checkout protected base for collection",
            )
            return (error,), ()
        collected = tuple(
            _collect_node_ids(clone, path, timeout_seconds) for path in paths
        )
        return (
            tuple(item[0] for item in collected),
            tuple(node_id for item in collected for node_id in item[1]),
        )


def _dirty_pytest_support(root: Path) -> set[str]:
    """Return live paths capable of changing pytest outside the Git closure."""
    result = subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        return {"<unreadable-git-status>"}
    dirty: set[str] = set()
    for field in result.stdout.decode(errors="surrogateescape").split("\0"):
        path = field[3:] if len(field) >= 4 else ""
        relpath = PurePosixPath(path)
        if (
            relpath.name == "conftest.py"
            or relpath in PYTEST_CONFIG_PATHS
            or (relpath.suffix == ".py" and "tests" in relpath.parts)
        ):
            dirty.add(path)
    return dirty


def _dirty_tracked_closure(root: Path) -> set[str]:
    """Return every tracked path whose exact-head bytes changed during validation."""
    result = subprocess.run(
        ["git", "diff", "--name-only", "HEAD", "--"],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        return {"<unreadable-tracked-closure>"}
    return {line for line in result.stdout.splitlines() if line}


def _dirty_jest_support(root: Path) -> set[str]:
    """Return uncommitted ambient files commonly executable by Jest config."""
    result = subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"],
        cwd=root, capture_output=True, check=False,
    )
    if result.returncode != 0:
        return {"<unreadable-git-status>"}
    dirty: set[str] = set()
    for field in result.stdout.decode(errors="surrogateescape").split("\0"):
        path = field[3:] if len(field) >= 4 else ""
        relpath = PurePosixPath(path)
        if (
            relpath.name.startswith("jest.config.")
            or relpath.name == "package.json"
            or relpath.name.startswith(("setup.", "transform.", "reporter.", "resolver."))
        ):
            dirty.add(path)
    return dirty


def _dirty_vitest_support(root: Path) -> set[str]:
    """Return dirty executable modules that can change a Vitest run."""
    result = subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        return {"<unreadable-git-status>"}
    dirty: set[str] = set()
    for field in result.stdout.decode(errors="surrogateescape").split("\0"):
        path = field[3:] if len(field) >= 4 else ""
        relpath = PurePosixPath(path)
        if (
            relpath.name.startswith(("vitest.config.", "vite.config."))
            or relpath.name == "package.json"
            or relpath.suffix in {".js", ".cjs", ".mjs", ".ts", ".cts", ".mts", ".tsx", ".jsx"}
        ):
            dirty.add(path)
    return dirty


def _dirty_playwright_support(root: Path) -> set[str]:
    """Reject ambient local JS, config, and support that Playwright could load."""
    result = subprocess.run(["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"], cwd=root, capture_output=True, check=False)
    if result.returncode != 0:
        return {"<unreadable-git-status>"}
    dirty: set[str] = set()
    for field in result.stdout.decode(errors="surrogateescape").split("\0"):
        path = field[3:] if len(field) >= 4 else ""
        relpath = PurePosixPath(path)
        if relpath.name.startswith("playwright.config.") or relpath.suffix in _JAVASCRIPT_SUFFIXES:
            dirty.add(path)
    return dirty


def _combine(
    obligation: VerificationObligation,
    executions: tuple[RunnerExecution, ...],
) -> RunnerExecution:
    order = (
        EvidenceOutcome.TIMEOUT,
        EvidenceOutcome.COLLECTION_ERROR,
        EvidenceOutcome.ERROR,
        EvidenceOutcome.FAIL,
        EvidenceOutcome.SKIP,
        EvidenceOutcome.XFAIL,
        EvidenceOutcome.NOT_COLLECTED,
        EvidenceOutcome.PASS,
    )
    outcomes = {execution.outcome for execution in executions}
    outcome = next(item for item in order if item in outcomes)
    digest = hashlib.sha256(
        "".join(item.command_digest for item in executions).encode()
    ).hexdigest()
    detail = "; ".join(item.detail for item in executions)
    return RunnerExecution(obligation.obligation_id, outcome, digest, detail)


def _obligation_preflight(
    root: Path,
    obligation: VerificationObligation,
    base_sha: str,
    head_sha: str,
) -> RunnerExecution | None:
    # pylint: disable=too-many-return-statements
    """Return a normalized fail-closed result before executing pytest."""
    if obligation.kind.casefold() != "test" or obligation.validator_id not in {"pytest", "jest", "vitest", "playwright"}:
        return RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.ERROR,
            obligation.validator_config_digest,
            "no trusted runner adapter is registered",
        )
    if not obligation.artifact_paths:
        return RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.NOT_COLLECTED,
            obligation.validator_config_digest,
            "test obligation declares no artifact paths",
        )
    digest_function = {
        "pytest": pytest_validator_config_digest,
        "jest": jest_validator_config_digest,
        "vitest": vitest_validator_config_digest,
        "playwright": playwright_validator_config_digest,
    }[obligation.validator_id]
    try:
        expected_config_digests = {
            digest_function(root, ref, obligation.artifact_paths)
            for ref in (base_sha, head_sha)
        }
    except ValueError as exc:
        return RunnerExecution(obligation.obligation_id, EvidenceOutcome.ERROR, obligation.validator_config_digest, str(exc))
    if expected_config_digests != {obligation.validator_config_digest}:
        if obligation.validator_id == "pytest":
            support_paths = tuple(
                path
                for path, _content in _pytest_support_closure(
                    root,
                    head_sha,
                    obligation.artifact_paths,
                    obligation.code_under_test_paths,
                )
            )
            changed_support = _changed_paths(root, base_sha, head_sha, support_paths)
            direct_config = {
                path.as_posix()
                for path in _pytest_config_paths(
                    root, head_sha, obligation.artifact_paths
                )
            }
            plugin_support = sorted(set(changed_support) - direct_config)
            if plugin_support:
                return RunnerExecution(
                    obligation.obligation_id,
                    EvidenceOutcome.QUARANTINED,
                    obligation.validator_config_digest,
                    "candidate-modified pytest support cannot solely certify itself: "
                    + ", ".join(plugin_support),
                )
        return RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.ERROR,
            obligation.validator_config_digest,
            "declared validator config digest does not match protected closure",
        )
    if obligation.validator_id == "pytest" and (
        _has_dynamic_pytest_plugins(
            root,
            base_sha,
            obligation.artifact_paths,
            obligation.code_under_test_paths,
        )
        or _has_dynamic_pytest_plugins(
            root,
            head_sha,
            obligation.artifact_paths,
            obligation.code_under_test_paths,
        )
    ):
        return RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.ERROR,
            obligation.validator_config_digest,
            "dynamic pytest_plugins declarations are not bound by this adapter",
        )
    if obligation.validator_id == "pytest" and (
        _has_external_pytest_plugins(
            root, base_sha, obligation.artifact_paths, obligation.code_under_test_paths
        )
        or _has_external_pytest_plugins(
            root, head_sha, obligation.artifact_paths, obligation.code_under_test_paths
        )
    ):
        return RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.ERROR,
            obligation.validator_config_digest,
            "external pytest_plugins declarations are not bound by this adapter",
        )
    if obligation.validator_id == "pytest" and (
        _config_loads_plugin(root, base_sha)
        or _config_loads_plugin(root, head_sha)
    ):
        return RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.ERROR,
            obligation.validator_config_digest,
            "repository-configured pytest plugins are not bound by this adapter",
        )
    return None


def _collect_jest_at_base(
    root: Path, base_sha: str, paths: tuple[PurePosixPath, ...], config: RunnerConfig
) -> tuple[RunnerExecution, tuple[str, ...]]:
    """Run protected-base Jest with the trusted reporter to establish identities."""
    with tempfile.TemporaryDirectory(prefix="pdd-jest-protected-base-") as directory:
        clone = Path(directory) / "repository"
        cloned = subprocess.run(["git", "clone", "-q", "--no-local", "--no-checkout", str(root), str(clone)], capture_output=True, text=True, check=False)
        checked_out = cloned.returncode == 0 and subprocess.run(["git", "checkout", "-q", "--detach", base_sha], cwd=clone, capture_output=True, check=False).returncode == 0
        if not checked_out:
            return RunnerExecution("protected-base-collection", EvidenceOutcome.COLLECTION_ERROR, hashlib.sha256(base_sha.encode()).hexdigest(), "cannot create protected-base Jest clone"), ()
        return _run_jest(clone, paths, config.timeout_seconds, config)


def _collect_vitest_at_base(
    root: Path, base_sha: str, paths: tuple[PurePosixPath, ...], config: RunnerConfig
) -> tuple[RunnerExecution, tuple[str, ...]]:
    """Run protected-base Vitest to establish independently derived identities."""
    with tempfile.TemporaryDirectory(prefix="pdd-vitest-protected-base-") as directory:
        clone = Path(directory) / "repository"
        cloned = subprocess.run(
            ["git", "clone", "-q", "--no-local", "--no-checkout", str(root), str(clone)],
            capture_output=True,
            text=True,
            check=False,
        )
        checked_out = cloned.returncode == 0 and subprocess.run(
            ["git", "checkout", "-q", "--detach", base_sha],
            cwd=clone,
            capture_output=True,
            check=False,
        ).returncode == 0
        if not checked_out:
            return RunnerExecution("protected-base-collection", EvidenceOutcome.COLLECTION_ERROR, hashlib.sha256(base_sha.encode()).hexdigest(), "cannot create protected-base Vitest clone"), ()
        return _run_vitest(
            clone,
            paths,
            config.timeout_seconds,
            config,
            command_root=root,
        )


def _collect_playwright_at_base(
    root: Path, base_sha: str, paths: tuple[PurePosixPath, ...], config: RunnerConfig
) -> tuple[RunnerExecution, tuple[str, ...]]:
    """Execute the protected base to derive Playwright project/file/title IDs."""
    with tempfile.TemporaryDirectory(prefix="pdd-playwright-protected-base-") as directory:
        clone = Path(directory) / "repository"
        cloned = subprocess.run(["git", "clone", "-q", "--no-local", "--no-checkout", str(root), str(clone)], capture_output=True, text=True, check=False)
        checked_out = cloned.returncode == 0 and subprocess.run(["git", "checkout", "-q", "--detach", base_sha], cwd=clone, capture_output=True, check=False).returncode == 0
        if not checked_out:
            return RunnerExecution("protected-base-collection", EvidenceOutcome.COLLECTION_ERROR, hashlib.sha256(base_sha.encode()).hexdigest(), "cannot create protected-base Playwright clone"), ()
        return _run_playwright(
            clone, paths, config.timeout_seconds, config, command_root=root,
            collection=True,
        )


def _protected_node_ids(
    root: Path,
    obligation: VerificationObligation,
    base_sha: str,
    timeout_seconds: int,
) -> tuple[
    RunnerExecution | None,
    tuple[RunnerExecution, ...],
    tuple[str, ...],
]:
    """Compare protected-base and checked-head pre-hook collection identities."""
    base_executions, base_node_ids = _collect_at_base(
        root, base_sha, obligation.artifact_paths, timeout_seconds
    )
    head_collected = tuple(
        _collect_node_ids(root, path, timeout_seconds)
        for path in obligation.artifact_paths
    )
    head_executions = tuple(item[0] for item in head_collected)
    head_node_ids = tuple(node_id for item in head_collected for node_id in item[1])
    collection_executions = base_executions + head_executions
    if any(item.outcome is not EvidenceOutcome.PASS for item in collection_executions):
        return _combine(obligation, collection_executions), (), ()
    if base_node_ids != head_node_ids:
        mismatch = RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.QUARANTINED,
            hashlib.sha256("".join(base_node_ids + head_node_ids).encode()).hexdigest(),
            "checked-head pytest node IDs differ from protected base",
        )
        return mismatch, (), ()
    return None, collection_executions, head_node_ids


def _run_obligation_in_tree(
    root: Path,
    obligation: VerificationObligation,
    *,
    base_sha: str,
    head_sha: str,
    config: RunnerConfig,
) -> RunnerExecution:
    # pylint: disable=too-many-locals
    """Run one protected obligation with changed-test self-certification guards."""
    preflight = _obligation_preflight(root, obligation, base_sha, head_sha)
    if preflight is not None:
        return preflight
    if obligation.validator_id == "jest":
        profile = VerificationProfile(
            UnitId("runner-closure", PurePosixPath("closure.prompt"), "javascript"),
            (obligation,), obligation.requirement_ids, "closure",
        )
        _digest, support_paths = _jest_support_digest(root, head_sha, profile)
        protected_paths = tuple(sorted(set(obligation.artifact_paths) | set(support_paths)))
        changed = _changed_paths(root, base_sha, head_sha, protected_paths)
        changed.update(_dirty_jest_support(root))
        if changed:
            return RunnerExecution(
                obligation.obligation_id, EvidenceOutcome.QUARANTINED,
                obligation.validator_config_digest,
                "candidate-modified Jest support cannot solely certify itself: "
                + ", ".join(sorted(changed)),
            )
        base_execution, base_ids = _collect_jest_at_base(root, base_sha, obligation.artifact_paths, config)
        if base_execution.outcome is not EvidenceOutcome.PASS:
            return RunnerExecution(obligation.obligation_id, base_execution.outcome, base_execution.command_digest, base_execution.detail)
        head_execution, _head_ids = _run_jest(root, obligation.artifact_paths, config.timeout_seconds, config, base_ids)
        return RunnerExecution(obligation.obligation_id, head_execution.outcome, head_execution.command_digest, head_execution.detail)
    if obligation.validator_id == "vitest":
        profile = VerificationProfile(
            UnitId("runner-closure", PurePosixPath("closure.prompt"), "typescript"),
            (obligation,),
            obligation.requirement_ids,
            "closure",
        )
        _digest, support_paths = _vitest_support_digest(root, head_sha, profile)
        protected_paths = tuple(
            sorted(set(obligation.artifact_paths) | set(support_paths))
        )
        changed = _changed_paths(root, base_sha, head_sha, protected_paths)
        changed.update(_dirty_vitest_support(root))
        if changed:
            return RunnerExecution(
                obligation.obligation_id,
                EvidenceOutcome.QUARANTINED,
                obligation.validator_config_digest,
                "candidate-modified Vitest support cannot solely certify itself: "
                + ", ".join(sorted(changed)),
            )
        base_execution, base_ids = _collect_vitest_at_base(
            root, base_sha, obligation.artifact_paths, config
        )
        if base_execution.outcome is not EvidenceOutcome.PASS:
            return RunnerExecution(
                obligation.obligation_id,
                base_execution.outcome,
                base_execution.command_digest,
                base_execution.detail,
            )
        head_execution, _head_ids = _run_vitest(
            root,
            obligation.artifact_paths,
            config.timeout_seconds,
            config,
            base_ids,
        )
        return RunnerExecution(
            obligation.obligation_id,
            head_execution.outcome,
            head_execution.command_digest,
            head_execution.detail,
        )
    if obligation.validator_id == "playwright":
        profile = VerificationProfile(
            UnitId("runner-closure", PurePosixPath("closure.prompt"), "typescript"),
            (obligation,), obligation.requirement_ids, "closure",
        )
        _digest, support_paths = _playwright_support_digest(root, head_sha, profile)
        protected_paths = tuple(sorted(set(obligation.artifact_paths) | set(support_paths)))
        changed = _changed_paths(root, base_sha, head_sha, protected_paths)
        changed.update(_dirty_playwright_support(root))
        if changed:
            return RunnerExecution(obligation.obligation_id, EvidenceOutcome.QUARANTINED,
                obligation.validator_config_digest,
                "candidate-modified Playwright support cannot solely certify itself: " + ", ".join(sorted(changed)))
        base_execution, base_ids = _collect_playwright_at_base(root, base_sha, obligation.artifact_paths, config)
        if base_execution.outcome is not EvidenceOutcome.PASS:
            return RunnerExecution(obligation.obligation_id, base_execution.outcome, base_execution.command_digest, base_execution.detail)
        head_collection, _head_ids = _run_playwright(
            root, obligation.artifact_paths, config.timeout_seconds, config,
            base_ids, collection=True,
        )
        if head_collection.outcome is not EvidenceOutcome.PASS:
            return RunnerExecution(obligation.obligation_id, head_collection.outcome, head_collection.command_digest, head_collection.detail)
        head_execution, _head_ids = _run_playwright(
            root, obligation.artifact_paths, config.timeout_seconds, config, base_ids
        )
        return RunnerExecution(obligation.obligation_id, head_execution.outcome, head_execution.command_digest, head_execution.detail)
    profile = VerificationProfile(
        UnitId("runner-closure", PurePosixPath("closure.prompt"), "python"),
        (obligation,),
        obligation.requirement_ids,
        "closure",
    )
    _digest, support_paths = _support_digest(root, head_sha, profile)
    protected_paths = tuple(sorted(set(obligation.artifact_paths) | set(support_paths)))
    changed = _changed_paths(root, base_sha, head_sha, protected_paths)
    changed.update(_dirty_pytest_support(root))
    if changed:
        return RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.QUARANTINED,
            obligation.validator_config_digest,
            "candidate-modified test cannot solely certify itself: "
            + ", ".join(sorted(changed)),
        )
    collection_error, collection_executions, head_node_ids = _protected_node_ids(
        root, obligation, base_sha, config.timeout_seconds
    )
    if collection_error is not None:
        return collection_error
    executions = tuple(
        _run_test_node(root, node_id, config.timeout_seconds)
        for node_id in head_node_ids
    )
    mutated = _dirty_pytest_support(root) | _dirty_tracked_closure(root)
    if mutated:
        return RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.ERROR,
            obligation.validator_config_digest,
            "protected runner closure was modified: " + ", ".join(sorted(mutated)),
        )
    return _combine(obligation, collection_executions + executions)


def run_obligation(
    root: Path,
    obligation: VerificationObligation,
    *,
    base_sha: str,
    head_sha: str,
    config: RunnerConfig,
) -> RunnerExecution:
    """Run an obligation in an ephemeral exact-head execution tree."""
    status = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=all"], cwd=root,
        capture_output=True, text=True, check=False,
    )
    dirty_all = tuple(line[3:] for line in status.stdout.splitlines() if len(line) >= 4)
    if status.returncode != 0 or dirty_all:
        return RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.QUARANTINED,
            obligation.validator_config_digest,
            "dirty checkout cannot receive committed-head evidence: "
            + ", ".join(dirty_all),
        )
    dirty = {
        "jest": _dirty_jest_support,
        "vitest": _dirty_vitest_support,
    }.get(obligation.validator_id, _dirty_pytest_support)(root)
    if dirty:
        return RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.QUARANTINED,
            obligation.validator_config_digest,
            "candidate-modified test cannot solely certify itself: "
            + ", ".join(sorted(dirty)),
        )
    if obligation.validator_id == "jest" and config.jest_command is not None:
        command_error = _protected_command_error(root, config.jest_command)
        if command_error is not None:
            return RunnerExecution(
                obligation.obligation_id,
                EvidenceOutcome.ERROR,
                obligation.validator_config_digest,
                command_error,
            )
    if obligation.validator_id == "vitest":
        if config.vitest_command is None and (
            root / "node_modules" / "vitest" / "vitest.mjs"
        ).is_file():
            return RunnerExecution(
                obligation.obligation_id,
                EvidenceOutcome.ERROR,
                obligation.validator_config_digest,
                "candidate node_modules Vitest runner is not trusted",
            )
        if config.vitest_command is not None:
            command_error = _protected_command_error(root, config.vitest_command)
            if command_error is not None:
                return RunnerExecution(
                    obligation.obligation_id,
                    EvidenceOutcome.ERROR,
                    obligation.validator_config_digest,
                    command_error,
                )
    with tempfile.TemporaryDirectory(prefix="pdd-runner-exact-head-") as directory:
        clone = Path(directory) / "repository"
        cloned = subprocess.run(
            ["git", "clone", "-q", "--no-local", "--no-checkout", str(root), str(clone)],
            capture_output=True,
            check=False,
        )
        checked = subprocess.run(
            ["git", "checkout", "-q", "--detach", head_sha],
            cwd=clone,
            capture_output=True,
            check=False,
        ) if cloned.returncode == 0 else None
        if checked is None or checked.returncode != 0:
            return RunnerExecution(
                obligation.obligation_id,
                EvidenceOutcome.ERROR,
                obligation.validator_config_digest,
                "cannot materialize exact-head protected runner tree",
            )
        return _run_obligation_in_tree(
            clone,
            obligation,
            base_sha=base_sha,
            head_sha=head_sha,
            config=config,
        )


def run_profile(
    root: Path,
    profile: VerificationProfile,
    binding: RunBinding,
    issuance: AttestationIssue,
    config: RunnerConfig = RunnerConfig(),
) -> tuple[AttestationEnvelope, tuple[RunnerExecution, ...]]:
    """Execute every obligation and issue one complete signed attestation."""
    executions = tuple(
        run_obligation(
            root,
            obligation,
            base_sha=binding.base_sha,
            head_sha=binding.head_sha,
            config=config,
        )
        for obligation in profile.obligations
    )
    runner_digest = runner_identity_digest(profile, root=root, ref=binding.head_sha, config=config)
    binding = AttestationBinding(
        profile.unit_id,
        binding.snapshot_digest,
        profile.profile_digest,
        runner_digest,
        TRUSTED_RUNNER_VERSION,
        binding.base_sha,
        binding.head_sha,
    )
    results = tuple(
        ObligationEvidence(item.obligation_id, item.outcome) for item in executions
    )
    envelope = issuance.signer.issue(
        AttestationRequest(
            issuance.attestation_id,
            binding,
            results,
            issuance.nonce,
            issuance.issued_at,
        )
    )
    return envelope, executions
