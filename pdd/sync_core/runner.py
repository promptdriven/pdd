"""Trusted validator adapters and pass-only normalized evidence outcomes."""
# pylint: disable=too-many-lines,too-many-boolean-expressions,too-many-locals
# pylint: disable=too-many-arguments

from __future__ import annotations

import hashlib
import ast
import configparser
import concurrent.futures
import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import tomllib
import xml.etree.ElementTree as ET
import importlib.metadata
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path, PurePosixPath

import pytest

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
from .supervisor import released_runtime_closure_paths, run_supervised


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
_runtime_digest_cache: dict[
    str, tuple[tuple[tuple[str, Path], ...], tuple[tuple[str, str, int, int], ...], str]
] = {}
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


@dataclass(frozen=True)
class RunnerConfig:
    """Protected execution limits for trusted validation adapters."""

    timeout_seconds: int = 300
    jest_command: tuple[str, ...] | None = None


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
    if isinstance(node, (ast.AugAssign, ast.NamedExpr)):
        return (node.target,)
    if isinstance(node, ast.Delete):
        return tuple(node.targets)
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
    # pylint: disable=too-many-locals,too-many-branches,too-many-statements
    """Resolve repository-local Python imports without executing candidate code."""
    try:
        tree = ast.parse(source)
    except (SyntaxError, UnicodeDecodeError):
        return set(), False
    modules: set[str] = set()
    dynamic_pytest_plugins = False
    importlib_names = {"importlib"}
    loader_names = {"__import__"}
    plugin_aliases = {"pytest_plugins"}
    for candidate in ast.walk(tree):
        if (
            isinstance(candidate, (ast.Assign, ast.AnnAssign, ast.NamedExpr))
            and isinstance(candidate.value, ast.Name)
            and candidate.value.id in plugin_aliases
        ):
            plugin_aliases.update(
                target.id for target in _pytest_plugin_declaration_targets(candidate)
                if isinstance(target, ast.Name)
            )
    pytest_plugins_declared = False
    for node in ast.walk(tree):
        targets = _pytest_plugin_declaration_targets(node)
        def rooted_in_plugin(target: ast.AST) -> bool:
            while isinstance(target, (ast.Subscript, ast.Attribute)):
                target = target.value
            return isinstance(target, ast.Name) and target.id in plugin_aliases
        if isinstance(node, (ast.AugAssign, ast.NamedExpr, ast.Delete)) and any(
            rooted_in_plugin(target) for target in targets
        ):
            dynamic_pytest_plugins = True
        elif isinstance(node, (ast.Assign, ast.AnnAssign)) and any(
            isinstance(target, (ast.Subscript, ast.Attribute))
            and rooted_in_plugin(target) for target in targets
        ):
            dynamic_pytest_plugins = True
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
            pytest_plugins_declared = True
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
            and node.func.id in {"exec", "eval", "compile", "run_path", "run_module"}
            or isinstance(node.func, ast.Attribute)
            and node.func.attr in {
                "spec_from_file_location", "load_module", "exec_module",
                "run_path", "run_module",
            }
            or isinstance(node.func, ast.Name) and node.func.id == "getattr"
            and len(node.args) >= 2
            and isinstance(node.args[0], ast.Name)
            and node.args[0].id in importlib_names
            and isinstance(node.args[1], ast.Constant)
            and node.args[1].value == "import_module"
        ):
            dynamic_pytest_plugins = True
        elif isinstance(node, ast.Call) and (
            pytest_plugins_declared
            or isinstance(node.func, ast.Name) and node.func.id == "setattr"
        ):
            if (
                isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Name)
                and node.func.value.id in plugin_aliases
            ) or (
                isinstance(node.func, ast.Name)
                and node.func.id in {"globals", "locals", "exec", "eval"}
            ) or (
                isinstance(node.func, ast.Name) and node.func.id == "setattr"
                and any(
                    isinstance(arg, ast.Constant) and arg.value == "pytest_plugins"
                    for arg in node.args
                )
            ):
                dynamic_pytest_plugins = True
        elif isinstance(node, (ast.Assign, ast.AnnAssign)) and any(
            isinstance(target, ast.Subscript)
            and isinstance(target.value, ast.Call)
            and isinstance(target.value.func, ast.Name)
            and target.value.func.id in {"globals", "locals"}
            and isinstance(target.slice, ast.Constant)
            and target.slice.value == "pytest_plugins"
            for target in _pytest_plugin_declaration_targets(node)
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
    fail_on_dynamic: bool = False,
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
        discovered, dynamic = _local_module_paths(
            root,
            ref,
            path,
            source,
            code_under_test_paths=code_under_test_paths,
        )
        if dynamic and fail_on_dynamic:
            raise ValueError(f"unresolved dynamic product dependency: {path}")
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
    product_closure = _transitive_support_blobs(
        root, ref, pending=product, included=set(product), fail_on_dynamic=True
    )
    if product:
        # Product code can read every committed artifact in its exact-head
        # checkout, not only importable Python source.
        repository_artifacts = tuple(
            (path, blob)
            for path in _git_paths(root, ref)
            if (blob := read_git_blob(root, ref, path)) is not None
        )
        product_closure = tuple(sorted(set(product_closure + repository_artifacts)))
    closure = tuple(sorted(set(closure + product_closure)))
    digest = hashlib.sha256()
    for path, content in closure:
        digest.update(path.as_posix().encode() + b"\0" + content + b"\0")
    return digest.hexdigest(), tuple(
        path for path, _content in closure if path not in set(product)
    )


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


def _config_loads_plugin(root: Path, ref: str) -> bool:
    """Reject repository-configured plugins until profiles bind plugin identities."""
    for path in PYTEST_CONFIG_PATHS:
        content = read_git_blob(root, ref, path)
        if content is None:
            continue
        try:
            text = content.decode("utf-8")
            if path.name == "pyproject.toml":
                pytest_options = tomllib.loads(text).get("tool", {}).get("pytest", {}).get(
                    "ini_options", {}
                )
                values = [pytest_options.get("addopts", "")]
            else:
                parser = configparser.ConfigParser(interpolation=None)
                parser.read_string(text)
                section = "pytest" if path.name in {"pytest.ini", ".pytest.ini"} else "tool:pytest"
                values = [parser.get(section, "addopts", fallback="")]
        except (UnicodeDecodeError, ValueError, configparser.Error, AttributeError):
            return True
        for value in values:
            if isinstance(value, list):
                value = " ".join(str(item) for item in value)
            if not isinstance(value, str):
                return True
            try:
                tokens = shlex.split(value, comments=True)
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
    writable_roots: tuple[Path, ...], writable_files: tuple[Path, ...] = (),
    readable_roots: tuple[Path, ...] = (),
) -> tuple[subprocess.CompletedProcess[str], bool]:
    """Run an untrusted command in a networkless sandbox and reap its group."""
    return run_supervised(command, cwd=cwd, timeout=timeout, env=env,
                          writable_roots=writable_roots, writable_files=writable_files,
                          readable_roots=readable_roots)


def runner_identity_digest(
    profile: VerificationProfile, *, root: Path | None = None, ref: str = "HEAD",
    config: RunnerConfig = RunnerConfig(),
) -> str:
    """Bind evidence to protected adapters, configs, and exact artifact scopes."""
    payload = {
        "tool_version": TRUSTED_RUNNER_VERSION,
        "python_runtime": _measured_python_runtime(),
        "released_runtime_digest": _released_runtime_closure_digest(),
        "checker_artifact_digest": _checker_artifact_digest(),
        "pytest_command": [
            "<measured-python-runtime>",
            "-P",
            "<trusted-worker-imports-pytest-before-candidate-root>",
            "import pytest",
            "pytest.main",
            "-q",
            *PYTEST_PROTECTED_FLAGS,
            "<protected-node-id>",
            "--junitxml=<trusted-temp-path>",
        ],
        "pytest_collection_command": [
            "<measured-python-runtime>",
            "-P",
            "<trusted-worker-imports-pytest-before-candidate-root>",
            "import pytest",
            "pytest.main",
            "--collect-only",
            "-q",
            "--strict-config",
            "--strict-markers",
            "-p",
            "<checker-owned-pytest-probe>",
            "<test-path>",
        ],
        "pytest_environment": {"PYTEST_DISABLE_PLUGIN_AUTOLOAD": "1"},
        "obligations": [
            {
                "id": item.obligation_id,
                "kind": item.kind,
                "validator": item.validator_id,
                "config": item.validator_config_digest,
                "paths": [path.as_posix() for path in item.artifact_paths],
                "code_under_test_paths": [
                    path.as_posix() for path in sorted(item.code_under_test_paths)
                ],
            }
            for item in profile.obligations
        ],
    }
    if root is not None:
        payload["support_closure_digest"] = hashlib.sha256(
            (_support_digest(root, ref, profile)[0] + _jest_support_digest(root, ref, profile)[0]).encode()
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


def _validator_command_identity_digest(root: Path, config: RunnerConfig) -> str:
    """Bind explicitly supplied validator commands to signed runner evidence."""
    payload: dict[str, object] = {}
    if config.jest_command is not None:
        payload["jest"] = [
            _file_identity(Path(part).resolve())
            if (Path(part).is_absolute() or "/" in part)
            and Path(part).expanduser().exists()
            else part
            for part in config.jest_command
        ]
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def _measured_python_runtime() -> dict[str, str]:
    """Return stable runtime properties without installation-specific paths."""
    return {
        "implementation": platform.python_implementation(),
        "version": platform.python_version(),
        "abi": getattr(sys.implementation, "cache_tag", ""),
        "platform": sys.platform,
        "machine": platform.machine(),
    }


def _checker_artifact_digest() -> str:
    """Hash checker modules and locked runtime dependency bytes by logical name."""
    digest = hashlib.sha256()
    from . import isolation, supervisor  # pylint: disable=import-outside-toplevel

    modules = {
        "pdd/sync_core/runner.py": Path(__file__),
        "pdd/sync_core/pytest_probe.py": _CHECKER_PYTEST_PROBE,
        "pdd/sync_core/supervisor.py": Path(supervisor.__file__),
        "pdd/sync_core/isolation.py": Path(isolation.__file__),
        "pytest/__init__.py": Path(pytest.__file__),
    }
    for name, path in sorted(modules.items()):
        digest.update(name.encode() + b"\0" + path.read_bytes() + b"\0")
    for distribution_name in ("pytest", "pluggy", "iniconfig", "packaging"):
        distribution = importlib.metadata.distribution(distribution_name)
        digest.update(distribution_name.encode() + b"\0")
        files = distribution.files or ()
        for member in sorted(files, key=str):
            path = Path(distribution.locate_file(member))
            if path.is_file() and not path.is_symlink():
                digest.update(str(member).encode() + b"\0" + path.read_bytes() + b"\0")
    return digest.hexdigest()


def _released_runtime_closure_paths() -> tuple[tuple[str, Path], ...]:
    """Return the complete, logically named runtime exposed to protected pytest."""
    paths = list(released_runtime_closure_paths())
    paths.extend((
        ("checker/pdd/sync_core/runner.py", Path(__file__)),
        ("checker/pdd/sync_core/pytest_probe.py", _CHECKER_PYTEST_PROBE),
    ))
    return tuple(sorted(paths, key=lambda item: item[0]))


_default_runtime_closure_paths = _released_runtime_closure_paths


def _runtime_manifest(
    entries: tuple[tuple[str, Path], ...]
) -> tuple[tuple[str, str, int, int], ...]:
    """Return byte-change-sensitive metadata without rereading runtime bytes."""
    return tuple(
        (name, str(path), path.stat().st_mtime_ns, path.stat().st_size)
        for name, path in entries
    )


def _hash_runtime_entry(entry: tuple[str, Path]) -> tuple[str, bytes] | None:
    """Hash one measured runtime file without loading it wholly into memory."""
    name, path = entry
    if not path.is_file():
        raise RuntimeError(f"released runtime entry is not a regular file: {name}")
    file_digest = hashlib.sha256()
    try:
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                file_digest.update(chunk)
    except PermissionError:
        if sys.platform.startswith("linux"):
            raise RuntimeError(f"released runtime entry is unreadable: {name}") from None
        # macOS cannot execute the protected sandbox; do not make reporting
        # unusable merely because a host-only outer helper is protected.
        return None
    return name, file_digest.digest()


def _released_runtime_closure_digest() -> str:
    """Hash the released runtime by logical name, never installation prefix."""
    default_paths = _released_runtime_closure_paths is _default_runtime_closure_paths
    cached = _runtime_digest_cache.get("default")
    if default_paths and cached is not None:
        entries, cached_manifest, cached_digest = cached
        if _runtime_manifest(entries) == cached_manifest:
            return cached_digest
    entries = _released_runtime_closure_paths()
    manifest = _runtime_manifest(entries)
    worker_count = min(32, (os.cpu_count() or 1) + 4)
    with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as executor:
        hashed_entries = tuple(executor.map(_hash_runtime_entry, entries))
    digest = hashlib.sha256()
    for hashed_entry in hashed_entries:
        if hashed_entry is not None:
            name, content_digest = hashed_entry
            digest.update(name.encode("utf-8") + b"\0" + content_digest + b"\0")
    result = digest.hexdigest()
    if default_paths:
        _runtime_digest_cache["default"] = entries, manifest, result
    return result


def _git_paths(root: Path, ref: str) -> tuple[PurePosixPath, ...]:
    """Return every committed regular path at an exact ref."""
    result = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", ref], cwd=root,
        capture_output=True, text=True, check=True,
    )
    return tuple(
        PurePosixPath(value) for value in result.stdout.splitlines()
    )


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
    """Create a worker that cannot see an authoritative result channel."""
    worker = directory / "collection_worker.py"
    worker.write_text(
        "\n".join(
            (
                "import os, sys",
                "",
                f"_ROOT = {json.dumps(str(root))}",
                f"_CONTROLLER = {json.dumps(str(directory))}",
                "",
                "os.chdir(_ROOT)",
                "sys.path.insert(0, _CONTROLLER)",
                "import pytest",
                "import pdd_checker_pytest_probe",
                "sys.path.insert(0, _ROOT)",
                "_STATUS = pytest.main(" + json.dumps(pytest_args) + ")",
                "sys.stdout.flush(); sys.stderr.flush()",
                "os._exit(_STATUS if _STATUS in (0, 5) else 125)",
                "",
            )
        ),
        encoding="utf-8",
    )
    return worker


def _trusted_execution_runner(
    directory: Path, root: Path, pytest_args: list[str]
) -> Path:
    """Create a worker whose raw pytest status is normalized outside the sandbox."""
    worker = directory / "execution_worker.py"
    worker.write_text(
        "\n".join((
            "import os, sys",
            f"_CONTROLLER = {json.dumps(str(directory))}",
            f"os.chdir({json.dumps(str(root))})",
            "sys.path.insert(0, _CONTROLLER)",
            "import pytest",
            f"sys.path.insert(0, {json.dumps(str(root))})",
            "_STATUS = pytest.main(" + json.dumps(pytest_args) + ")",
            "sys.stdout.flush(); sys.stderr.flush()",
            "os._exit(_STATUS if 0 <= _STATUS <= 5 else 125)", "",
        )), encoding="utf-8",
    )
    return worker


def _pytest_exit_outcome(returncode: int, output: str) -> tuple[EvidenceOutcome, str]:
    """Normalize the worker's whitelisted pytest status outside candidate control."""
    if returncode == 0:
        return EvidenceOutcome.PASS, "protected pytest completed without failures"
    if returncode == 1:
        return EvidenceOutcome.FAIL, "protected pytest reported test failures"
    if returncode == 5:
        return EvidenceOutcome.NOT_COLLECTED, "protected pytest collected no tests"
    return EvidenceOutcome.ERROR, "protected pytest failed: " + output[-500:]


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
    if _command_uses_candidate_checkout(root, command_prefix):
        return RunnerExecution("jest", EvidenceOutcome.ERROR, "jest-untrusted", "explicit Jest command inside the candidate checkout is not trusted"), ()
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


def _run_test_node(
    root: Path,
    node_id: str,
    timeout_seconds: int,
) -> RunnerExecution:
    pytest_args = [
        "-q",
        *PYTEST_PROTECTED_FLAGS,
        node_id,
    ]
    command = [
        sys.executable,
        "-P",
        "pdd-trusted-execution-runner",
        "import-trusted-pytest",
        "pytest.main",
        *pytest_args,
    ]
    command_digest = hashlib.sha256(
        json.dumps(command, separators=(",", ":")).encode()
    ).hexdigest()
    with tempfile.TemporaryDirectory(prefix="pdd-trusted-runner-") as directory:
        temporary = Path(directory)
        controllers = temporary / f"controller-{os.urandom(16).hex()}"
        controllers.mkdir(mode=0o700)
        home = temporary / "scratch" / "home"
        home.mkdir(mode=0o700, parents=True)
        junit = controllers / f"result-{os.urandom(16).hex()}.xml"
        junit.touch(mode=0o600)
        worker = _trusted_execution_runner(
            controllers, root, [*pytest_args, f"--junitxml={junit}"]
        )
        result, surviving = _managed_subprocess(
            [sys.executable, "-P", str(worker)], cwd=controllers,
            timeout=timeout_seconds, env=_pytest_environment(home),
            writable_roots=(home.parent,),
            writable_files=(junit,), readable_roots=(root,),
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
        output = result.stdout + "\n" + result.stderr
        outcome, detail = _junit_outcome(junit, result.returncode, output, 1)
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
        controllers = temporary / f"controller-{os.urandom(16).hex()}"
        controllers.mkdir(mode=0o700)
        home = temporary / "scratch" / "home"
        home.mkdir(mode=0o700, parents=True)
        pytest_args = [
            "--collect-only",
            "-q",
            "--strict-config",
            "--strict-markers",
            "-p",
            "no:cacheprovider",
            path.as_posix(),
        ]
        plugin_name, _plugin_directory = _trusted_probe_plugin(controllers)
        pytest_args.extend(("-p", plugin_name))
        worker = _trusted_collection_runner(controllers, root, pytest_args)
        command = [sys.executable, "-P", str(worker)]
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
            command, cwd=controllers, timeout=timeout_seconds,
            env=_pytest_environment(home), writable_roots=(home.parent,),
            readable_roots=(root, _CHECKER_PYTEST_PROBE),
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
        node_ids = ()
        for line in result.stdout.splitlines():
            if line.startswith("PDD_PROTECTED_NODE_IDS="):
                try:
                    values = json.loads(line.partition("=")[2])
                    node_ids = tuple(sorted(item for item in values if isinstance(item, str)))
                except json.JSONDecodeError:
                    pass
        if not node_ids and result.returncode == 0:
            return (
                RunnerExecution(
                    path.as_posix(),
                    EvidenceOutcome.COLLECTION_ERROR,
                    digest,
                    "protected collection produced no valid node IDs: "
                    + (result.stderr or result.stdout)[-500:],
                ),
                (),
            )
        if not node_ids and result.returncode in {0, 5}:
            outcome = EvidenceOutcome.NOT_COLLECTED
            detail = "zero protected node IDs collected"
        elif result.returncode != 0:
            outcome = EvidenceOutcome.COLLECTION_ERROR
            diagnostic = (result.stderr or result.stdout).strip()[-1000:]
            detail = "protected sandbox rejected pytest collection"
            if diagnostic:
                detail += f": {diagnostic}"
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
    if obligation.kind.casefold() != "test" or obligation.validator_id not in {"pytest", "jest"}:
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
    digest_function = pytest_validator_config_digest if obligation.validator_id == "pytest" else jest_validator_config_digest
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
    dirty = _dirty_pytest_support(root)
    if dirty:
        return RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.QUARANTINED,
            obligation.validator_config_digest,
            "candidate-modified test cannot solely certify itself: "
            + ", ".join(sorted(dirty)),
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
