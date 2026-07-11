"""Trusted validator adapters and pass-only normalized evidence outcomes."""
# pylint: disable=too-many-lines,too-many-boolean-expressions,too-many-locals
# pylint: disable=too-many-branches,too-many-statements,too-many-return-statements
# pylint: disable=too-many-arguments,too-many-positional-arguments,line-too-long

from __future__ import annotations

import ast
import configparser
import concurrent.futures
import hashlib
import importlib.metadata
import json
import os
import platform
import re
import select
import shlex
import stat
import subprocess
import sys
import tempfile
import threading
import tomllib
import xml.etree.ElementTree as ET
from dataclasses import dataclass, replace
from datetime import datetime
from pathlib import Path, PurePosixPath

import pytest

from .trust import (
    AttestationBinding,
    AttestationEnvelope,
    AttestationIssuer,
    AttestationRequest,
)
from .isolation import untrusted_child_environment
from .git_io import read_git_blob, read_git_regular_blob
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
    str,
    tuple[
        tuple[tuple[str, Path], ...],
        tuple[tuple[str, str, int, int, int], ...],
        str,
    ],
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
VITEST_TOOLCHAIN_ROLES = {
    "launcher", "entrypoint", "dependencies", "native_runtime", "lockfile"
}
VITEST_GRAMMAR_VERSIONS = {
    "tree-sitter": "0.25.2",
    "tree-sitter-javascript": "0.25.0",
    "tree-sitter-typescript": "0.23.2",
}
VITEST_CACHE_NAMES = {".vite", ".vite-temp"}
VITEST_RESULT_MAX_BYTES = 16 * 1024 * 1024


@dataclass(frozen=True)
class VitestToolchainMember:
    """Captured no-follow identity for one typed toolchain member."""

    role: str
    relative_path: PurePosixPath
    kind: str
    mode: int
    content_digest: str | None = None
    link_target: str | None = None


@dataclass(frozen=True)
# pylint: disable=too-many-instance-attributes
class VitestToolchainDescriptor:
    """Validated immutable identity and typed external Vitest role closure."""

    manifest: Path
    launcher: Path
    entrypoint: Path
    dependencies: Path
    native_runtime: tuple[Path, ...]
    lockfile: Path
    identity: str
    dependencies_identity: str
    members: tuple[VitestToolchainMember, ...]


@dataclass(frozen=True)
class VitestPhaseToolchain:
    """Copied executable Vitest launcher and package closure for one phase."""

    launcher: Path
    entrypoint: Path
    lockfile: Path
    native_runtime: tuple[Path, ...]
    readable_roots: tuple[Path, ...]
    readable_bindings: tuple[tuple[Path, Path], ...]
    dependencies: Path
    controller: Path
    descriptor: VitestToolchainDescriptor


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
    vitest_toolchain_manifest: Path | None = None
    vitest_toolchain_identity: str | None = None
    adapter_identities: tuple[tuple[str, str], ...] = ()
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
    # pylint: disable=too-many-branches,too-many-statements
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


def _javascript_syntax_mask(text: str) -> str:
    """Blank JS comments and string bodies while preserving quote boundaries."""
    masked = list(text)
    index = 0
    while index < len(text):
        if text.startswith("//", index):
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
            masked[index:end] = " " * (end - index)
            index = end
            continue
        if text.startswith("/*", index):
            end = text.find("*/", index + 2)
            end = len(text) if end < 0 else end + 2
            masked[index:end] = " " * (end - index)
            index = end
            continue
        if text[index] in {'"', "'", "`"}:
            quote = text[index]
            index += 1
            while index < len(text):
                if text[index] == "\\":
                    masked[index] = " "
                    if index + 1 < len(text):
                        masked[index + 1] = " "
                    index += 2
                    continue
                if text[index] == quote:
                    break
                masked[index] = " "
                index += 1
            index += 1
            continue
        index += 1
    return "".join(masked)


def _local_javascript_imports(
    root: Path, ref: str, source_path: PurePosixPath, source: bytes
) -> set[PurePosixPath]:
    """Resolve literal local JS imports and reject unresolved dynamic loads."""
    try:
        text = source.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError(
            f"Jest support module is not UTF-8: {source_path.as_posix()}"
        ) from exc
    mask = _javascript_syntax_mask(text)
    dynamic_load = re.search(
        r"(?<![.\w$])(?:require|import)\s*\(\s*(?!['\"])", mask
    )
    if dynamic_load is not None:
        raise ValueError(
            "dynamic local require/import is not bound by the Jest adapter: "
            + source_path.as_posix()
        )
    import_pattern = re.compile(
        r"(?:from\s+|import\s*\(|import\s+|require\s*\()['\"]([^'\"]+)['\"]"
    )
    imports = [
        match.group(1)
        for match in import_pattern.finditer(text)
        if not mask[match.start()].isspace()
    ]
    resolved: set[PurePosixPath] = set()
    for item in imports:
        resolved.update(_resolve_javascript_specifier(root, ref, source_path, item))
    return resolved


def _nearest_package_scope(
    root: Path, ref: str, source_path: PurePosixPath,
) -> tuple[PurePosixPath, bytes] | None:
    """Return the nearest committed package manifest enclosing a source file."""
    directory = source_path.parent
    while True:
        manifest = directory / "package.json"
        raw = read_git_regular_blob(root, ref, manifest)
        if raw is not None:
            return directory, raw
        if directory == PurePosixPath("."):
            return None
        directory = directory.parent


def _package_mapping_target(
    root: Path, ref: str, source_path: PurePosixPath, specifier: str
) -> PurePosixPath | None:
    """Resolve an exact mapping relative to the source file's package scope."""
    scoped_manifest = _nearest_package_scope(root, ref, source_path)
    raw = scoped_manifest[1] if scoped_manifest is not None else None
    if raw is None:
        if specifier.startswith("#"):
            raise ValueError(f"package import mapping is missing: {specifier}")
        return None
    scope = scoped_manifest[0]
    try:
        package = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError("package.json mapping source is invalid") from exc
    if not isinstance(package, dict):
        raise ValueError("package.json mapping source must be an object")
    name = package.get("name")
    key = None
    mappings = None
    if specifier.startswith("#"):
        key, mappings = specifier, package.get("imports", {})
    elif isinstance(name, str) and (specifier == name or specifier.startswith(name + "/")):
        key = "." if specifier == name else "./" + specifier[len(name) + 1:]
        mappings = package.get("exports", {})
    else:
        return None
    if isinstance(mappings, str) and key == ".":
        target = mappings
    elif isinstance(mappings, dict) and key in mappings:
        target = mappings[key]
    else:
        raise ValueError(f"package mapping is missing: {specifier}")
    if isinstance(target, dict):
        raise ValueError(f"package mapping conditions are not supported: {specifier}")
    if not isinstance(target, str) or not target.startswith("./") or "*" in target:
        raise ValueError(f"package mapping is not one static local file: {specifier}")
    candidate = _normalize_repo_relative_path(scope / PurePosixPath(target))
    if candidate is None or candidate == PurePosixPath("."):
        raise ValueError(f"package mapping escapes repository: {specifier}")
    if read_git_regular_blob(root, ref, candidate) is None:
        raise ValueError(f"package mapping target is missing: {specifier}")
    return candidate


def _resolve_javascript_specifier(
    root: Path, ref: str, source_path: PurePosixPath, specifier: str
) -> set[PurePosixPath]:
    """Resolve only literal repository paths and deterministic package mappings."""
    if specifier.startswith(("./", "../")):
        candidate = _normalize_repo_relative_path(source_path.parent / PurePosixPath(specifier))
        if candidate is None:
            raise ValueError(f"JavaScript import escapes repository: {specifier}")
        return {
            path for path in _javascript_path_candidates(candidate)
            if read_git_regular_blob(root, ref, path) is not None
        }
    mapped = _package_mapping_target(root, ref, source_path, specifier)
    return {mapped} if mapped is not None else set()


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
        source = read_git_regular_blob(root, ref, candidate)
        if source is not None:
            return candidate, source
    return normalized, None


def _jest_support_closure(
    root: Path,
    ref: str,
    test_paths: tuple[PurePosixPath, ...],
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
) -> tuple[tuple[PurePosixPath, bytes], ...]:
    """Return static config and transitive local Jest support modules."""
    config_path, config = _jest_config(root, ref)
    paths = {config_path}
    pending = list(test_paths) + list(_jest_config_references(config))
    product_paths = set(code_under_test_paths)
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
        scoped_manifest = _nearest_package_scope(root, ref, path)
        if scoped_manifest is not None:
            paths.add(scoped_manifest[0] / "package.json")
        if path.suffix == ".json":
            try:
                nested_config = json.loads(source.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise ValueError(f"Jest project config is invalid: {path.as_posix()}") from exc
            if path.name == "package.json" and isinstance(nested_config, dict):
                nested_config = nested_config.get("jest", {})
            pending.extend(_jest_config_references(nested_config) - visited)
        imports = _local_javascript_imports(root, ref, path, source)
        pending.extend(imports - visited - product_paths)
    return tuple(
        (path, read_git_blob(root, ref, path))
        for path in sorted(paths)
        if read_git_blob(root, ref, path) is not None
    )


def jest_validator_config_digest(
    root: Path,
    ref: str,
    test_paths: tuple[PurePosixPath, ...],
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
) -> str:
    """Hash static Jest config and executable local support closure."""
    digest = hashlib.sha256()
    for path, content in _jest_support_closure(
        root, ref, test_paths, code_under_test_paths
    ):
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
    for key in (
        "workspace", "projects", "plugins", "globalSetup", "snapshotEnvironment",
        "snapshotSerializers", "snapshotResolver", "runner", "pool", "environment",
        "reporters", "coverage",
    ):
        if test_config.get(key):
            raise ValueError(f"Vitest {key} is not bound by this adapter")
    if test_config.get("alias"):
        raise ValueError("Vitest test.alias is not bound by this adapter")
    for key in (
        "testNamePattern", "shard", "watch", "related", "changed", "retry",
        "retries", "repeat", "sequence", "update", "updateSnapshot",
    ):
        if key in test_config:
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


def _vitest_parser(language_name: str):
    """Return a parser backed only by the exact wheel-provisioned grammars."""
    try:
        for distribution, expected in VITEST_GRAMMAR_VERSIONS.items():
            actual = importlib.metadata.version(distribution)
            if actual != expected:
                raise ValueError(
                    f"{distribution} grammar version {actual!r} != {expected!r}"
                )
        from tree_sitter import Language, Parser  # pylint: disable=import-outside-toplevel
        from tree_sitter_javascript import (  # pylint: disable=import-outside-toplevel
            language as javascript_language,
        )
        from tree_sitter_typescript import (  # pylint: disable=import-outside-toplevel
            language_tsx,
            language_typescript,
        )

        grammar = {
            "javascript": javascript_language,
            "typescript": language_typescript,
            "tsx": language_tsx,
        }[language_name]
        return Parser(Language(grammar()))
    except (
        ImportError,
        KeyError,
        OSError,
        TypeError,
        ValueError,
        importlib.metadata.PackageNotFoundError,
    ) as exc:
        raise ValueError("Vitest JavaScript parser is unavailable") from exc


def _vitest_ast_imports(
    root: Path, ref: str, source_path: PurePosixPath, source: bytes
) -> set[PurePosixPath]:
    # pylint: disable=too-many-locals,too-many-nested-blocks
    """Resolve static loaders through a positive lexical capability model."""
    language_name = (
        "tsx" if source_path.suffix == ".tsx"
        else "typescript" if source_path.suffix in {".ts", ".cts", ".mts"}
        else "javascript"
    )
    tree = _vitest_parser(language_name).parse(source)
    if tree.root_node.has_error:
        raise ValueError(f"Vitest support source is not valid JavaScript/TypeScript: {source_path}")
    nodes = []
    pending = [tree.root_node]
    while pending:
        node = pending.pop()
        nodes.append(node)
        pending.extend(node.named_children)

    def node_text(node) -> bytes:
        return source[node.start_byte:node.end_byte]

    def static_string(node) -> str | None:
        raw = node_text(node)
        if node.type == "template_string" and b"${" not in raw:
            return raw[1:-1].decode("utf-8")
        if node.type == "string":
            try:
                value = ast.literal_eval(raw.decode("utf-8"))
            except (SyntaxError, ValueError) as exc:
                raise ValueError("Vitest module loader string is invalid") from exc
            return value if isinstance(value, str) else None
        return None

    def call_parts(node):
        function = node.child_by_field_name("function")
        arguments = node.child_by_field_name("arguments")
        return function, tuple(arguments.named_children if arguments else ())

    values: list[str] = []
    loader_aliases = {"require"}
    factory_aliases: set[str] = set()
    module_namespace_aliases: set[str] = set()
    allowed_capability_nodes: set[tuple[int, int]] = set()
    recognized_factory_calls: set[tuple[int, int]] = set()
    uninitialized_bindings: dict[str, object] = {}

    def allow(node) -> None:
        allowed_capability_nodes.add((node.start_byte, node.end_byte))

    def identifier_name(node) -> str | None:
        if node is None or node.type != "identifier":
            return None
        return node_text(node).decode("utf-8")

    def descendants(parent, node_type: str):
        return (
            child for child in nodes
            if child.type == node_type
            and parent.start_byte <= child.start_byte < parent.end_byte
        )

    def is_assignment_value(node) -> bool:
        parent = node.parent
        while parent is not None and parent.type == "parenthesized_expression":
            node, parent = parent, parent.parent
        if parent is None:
            return False
        field = (
            "value" if parent.type == "variable_declarator"
            else "right" if parent.type == "assignment_expression"
            else None
        )
        return field is not None and parent.child_by_field_name(field) == node

    forbidden_identifiers = {b"eval", b"Function", b"Reflect"}
    forbidden_properties = {
        b"_load", b"require", b"mainModule",
        b"getBuiltinModule", b"binding", b"dlopen", b"constructor",
        b"__proto__", b"apply", b"call", b"bind", b"eval", b"Function",
    }
    for node in nodes:
        raw = node_text(node)
        if node.type == "identifier" and b"\\" in raw:
            raise ValueError("Vitest escaped loader capability is not bound")
        if node.type == "identifier" and raw in forbidden_identifiers:
            raise ValueError("Vitest ambient loader capability is not bound")
        if (
            node.type == "identifier"
            and raw in {b"globalThis", b"global"}
            and (
                is_assignment_value(node)
                or node.parent is not None
                and node.parent.type == "subscript_expression"
            )
        ):
            raise ValueError("Vitest global capability alias is not bound")
        if node.type in {"property_identifier", "shorthand_property_identifier"}:
            if raw in forbidden_properties:
                raise ValueError("Vitest reflective loader capability is not bound")
        if node.type == "subscript_expression" and (
            is_assignment_value(node)
            or node.parent is not None
            and node.parent.type == "call_expression"
            and node.parent.child_by_field_name("function") == node
        ):
            raise ValueError("Vitest computed callable capability is not bound")
        if (
            node.type == "identifier"
            and raw == b"process"
            and is_assignment_value(node)
        ):
            raise ValueError("Vitest process capability alias is not bound")

    for node in nodes:
        if node.type != "import_statement":
            continue
        target = node.child_by_field_name("source")
        if target is None:
            continue
        value = static_string(target)
        if value in {"module", "node:module"}:
            for identifier in descendants(node, "identifier"):
                parent = identifier.parent
                if parent is not None and parent.type in {
                    "import_clause", "namespace_import"
                }:
                    module_namespace_aliases.add(
                        node_text(identifier).decode("utf-8")
                    )
                    allow(identifier)
            for specifier in descendants(node, "import_specifier"):
                name = specifier.child_by_field_name("name")
                identifiers = [
                    child for child in specifier.named_children
                    if child.type == "identifier"
                ]
                if name is not None and node_text(name) == b"createRequire":
                    alias = identifiers[-1]
                    factory_aliases.add(node_text(alias).decode("utf-8"))
                    for identifier in identifiers:
                        allow(identifier)

    assignments = sorted(
        (node for node in nodes if node.type in {
            "variable_declarator", "assignment_expression"
        }),
        key=lambda item: (item.start_byte, -item.end_byte),
    )
    for node in assignments:
        left = node.child_by_field_name(
            "name" if node.type == "variable_declarator" else "left"
        )
        right = node.child_by_field_name(
            "value" if node.type == "variable_declarator" else "right"
        )
        if left is None:
            continue
        left_name = identifier_name(left)
        if right is None:
            if left_name is not None and node.type == "variable_declarator":
                uninitialized_bindings[left_name] = left
            continue
        right_raw = node_text(right)
        right_name = identifier_name(right)
        if left_name is not None and right_name in loader_aliases:
            if left_name in loader_aliases:
                raise ValueError("Vitest loader capability is reassigned or shadowed")
            loader_aliases.add(left_name)
            allow(left)
            allow(right)
            prior = uninitialized_bindings.pop(left_name, None)
            if prior is not None:
                allow(prior)
            continue
        if left.type == "object_pattern" and right.type == "call_expression":
            function, arguments = call_parts(right)
            module_name = static_string(arguments[0]) if len(arguments) == 1 else None
            if (
                function is not None
                and node_text(function) == b"require"
                and module_name in {"module", "node:module"}
            ):
                recognized = False
                for pattern in left.named_children:
                    if pattern.type == "pair_pattern":
                        children = pattern.named_children
                        value_node = pattern.child_by_field_name("value")
                        if (
                            children
                            and node_text(children[0]) == b"createRequire"
                            and value_node is not None
                            and value_node.type == "identifier"
                        ):
                            factory_aliases.add(node_text(value_node).decode("utf-8"))
                            allow(value_node)
                            allow(children[0])
                            recognized = True
                    elif (
                        pattern.type == "shorthand_property_identifier_pattern"
                        and node_text(pattern) == b"createRequire"
                    ):
                        factory_aliases.add("createRequire")
                        allow(pattern)
                        recognized = True
                if recognized:
                    allow(function)
                    continue
        if right.type == "call_expression":
            function, arguments = call_parts(right)
            function_name = identifier_name(function)
            module_name = static_string(arguments[0]) if len(arguments) == 1 else None
            if (
                left_name is not None
                and function_name in loader_aliases
                and module_name in {"module", "node:module"}
            ):
                module_namespace_aliases.add(left_name)
                allow(left)
                allow(function)
                continue
            if left_name is not None and function_name in factory_aliases:
                if len(arguments) != 1 or node_text(arguments[0]) != b"import.meta.url":
                    raise ValueError("Vitest createRequire alias operand is dynamic")
                if left_name in loader_aliases:
                    raise ValueError("Vitest loader capability is reassigned or shadowed")
                loader_aliases.add(left_name)
                allow(left)
                allow(function)
                recognized_factory_calls.add((right.start_byte, right.end_byte))
                continue
            if (
                function_name in loader_aliases
                and len(arguments) == 1
                and static_string(arguments[0]) is not None
            ):
                continue
        del right_raw

    for node in nodes:
        node_raw = node_text(node)
        if (
            node_raw == b"_load"
            and node.type not in {"string", "comment", "template_string"}
        ):
            raise ValueError("Vitest internal module loader is not bound")
        if node.type == "member_expression":
            property_node = node.child_by_field_name("property")
            property_text = node_text(property_node) if property_node is not None else b""
            if property_text in {b"_load", b"require", b"createRequire"}:
                raise ValueError("Vitest internal module loader is not bound")
        if node.type == "subscript_expression" and any(
            marker in node_raw
            for marker in (
                b"require", b"createRequire", b"_load", b"glob",
                b"module", b"Module",
            )
        ):
            raise ValueError("Vitest computed module loader is not bound")
        target = None
        if node.type in {"import_statement", "export_statement"}:
            target = node.child_by_field_name("source")
        elif node.type == "call_expression":
            function, arguments = call_parts(node)
            function_text = node_text(function) if function is not None else b""
            if function is not None and function.type == "member_expression":
                property_node = function.child_by_field_name("property")
                property_text = (
                    node_text(property_node)
                    if property_node is not None else b""
                )
                local_operand = any(
                    (value := static_string(argument)) is not None
                    and value.startswith(("./", "../"))
                    for argument in arguments
                )
                carries_provenance = property_text in {b"apply", b"call", b"bind"} and any(
                    re.search(
                        rb"\b" + re.escape(name.encode()) + rb"\b",
                        function_text
                        + b" "
                        + b" ".join(node_text(item) for item in arguments),
                    )
                    for name in loader_aliases | factory_aliases | {"createRequire"}
                )
                if (
                    property_text in {
                        b"require", b"createRequire", b"glob", b"globEager",
                        b"load", b"_load",
                    }
                    or local_operand
                    or carries_provenance
                ):
                    raise ValueError("Vitest alternate module loader is not bound")
            function_name = identifier_name(function)
            if function_name in factory_aliases:
                if (node.start_byte, node.end_byte) not in recognized_factory_calls:
                    raise ValueError("Vitest createRequire alias provenance is ambiguous")
                continue
            if function is not None and (
                function_text == b"import" or function_name in loader_aliases
            ):
                if len(arguments) != 1:
                    raise ValueError("Vitest dynamic module loader is unsupported")
                target = arguments[0]
                allow(function)
            elif function is not None and function.type == "identifier":
                local_operand = any(
                    (value := static_string(argument)) is not None
                    and value.startswith(("./", "../"))
                    for argument in arguments
                )
                if local_operand:
                    raise ValueError("Vitest loader alias provenance is unknown")
        if target is None:
            continue
        value = static_string(target)
        if value is None:
            raise ValueError("Vitest dynamic module loader is unsupported")
        if value.startswith(("./", "../", "#")) or _package_mapping_target(
            root, ref, source_path, value
        ) is not None:
            values.append(value)
    capability_names = (
        loader_aliases | factory_aliases | module_namespace_aliases
        | {"require", "createRequire"}
    )
    for node in nodes:
        if node.type != "identifier":
            continue
        if identifier_name(node) == "module":
            parent = node.parent
            if parent is not None and parent.type == "member_expression":
                obj = parent.child_by_field_name("object")
                prop = parent.child_by_field_name("property")
                if obj == node and prop is not None and node_text(prop) == b"exports":
                    continue
            raise ValueError("Vitest module capability provenance is ambiguous")
        if identifier_name(node) not in capability_names:
            continue
        if (node.start_byte, node.end_byte) not in allowed_capability_nodes:
            raise ValueError("Vitest loader capability provenance is ambiguous")
    resolved: set[PurePosixPath] = set()
    for value in values:
        matches = list(_resolve_javascript_specifier(root, ref, source_path, value))
        if not matches:
            raise ValueError(f"Vitest static module is missing: {value}")
        resolved.update(matches)
    return resolved


def _vitest_support_closure(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...],
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
) -> tuple[tuple[PurePosixPath, bytes], ...]:
    """Return static config and transitive local Vitest support modules."""
    config_path, config = _vitest_config(root, ref)
    products = set(code_under_test_paths)
    paths = {config_path}
    if read_git_blob(root, ref, PurePosixPath("package.json")) is not None:
        paths.add(PurePosixPath("package.json"))
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
        source = read_git_regular_blob(root, ref, path)
        if source is None:
            raise ValueError(f"Vitest support path is missing: {path.as_posix()}")
        if path in products:
            continue
        paths.add(path)
        scoped_manifest = _nearest_package_scope(root, ref, path)
        if scoped_manifest is not None:
            paths.add(scoped_manifest[0] / "package.json")
        if path.suffix != ".json":
            pending.extend(_vitest_ast_imports(root, ref, path, source) - visited)
    return tuple(
        (path, read_git_regular_blob(root, ref, path))
        for path in sorted(paths)
        if read_git_blob(root, ref, path) is not None
    )


def vitest_validator_config_digest(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...],
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
) -> str:
    """Hash static Vitest config and executable local support closure."""
    digest = hashlib.sha256()
    for path, content in _vitest_support_closure(
        root, ref, test_paths, code_under_test_paths
    ):
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
    # pylint: disable=too-many-branches
    """Reject dynamic controls and return literal local config imports."""
    try:
        text = source.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError("Playwright configuration must be UTF-8") from exc
    # Playwright config is executable code.  Only accept the deliberately small,
    # directly inspectable object-literal subset; syntactic indirection makes a
    # security decision based on token matching unsound.
    if re.search(r"/\*|//|\.\.\.|\[[^\]]+\]\s*:", text):
        raise ValueError("Playwright configuration must use direct declarative keys")
    if re.search(
        r"\b(?:storageState|projects|dependencies|snapshotPathTemplate|executablePath)\b",
        text,
    ):
        raise ValueError("Playwright configuration references unsupported runtime resources")
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
    # pylint: disable=too-many-locals
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
            if re.search(r"\bimport\s*\(\s*(?!['\"])", text) or re.search(
                r"\b(?:const|let|var)\s+\w+\s*=\s*require\b", text
            ):
                raise ValueError("dynamic or aliased Playwright module loading is not supported")
            if re.search(
                r"(?:from\s+|import\s*\(|require\s*\()\s*['\"](?:node:)?fs(?:/[^'\"]*)?['\"]",
                text,
            ):
                raise ValueError("Playwright runtime file access is not bound by this adapter")
            if "toHaveScreenshot" in text:
                snapshot_prefix = PurePosixPath(f"{path.as_posix()}-snapshots")
                listed = subprocess.run(
                    ["git", "ls-tree", "-r", "--name-only", ref, "--", snapshot_prefix.as_posix()],
                    cwd=root, capture_output=True, text=True, check=True,
                )
                for name in listed.stdout.splitlines():
                    snapshot_path = PurePosixPath(name)
                    snapshot = read_git_blob(root, ref, snapshot_path)
                    if snapshot is not None:
                        paths.add(snapshot_path)
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
    product = tuple(
        path
        for obligation in profile.obligations
        if obligation.validator_id == "jest"
        for path in obligation.code_under_test_paths
    )
    try:
        closure = _jest_support_closure(root, ref, tests, product)
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
    products = tuple(
        path for obligation in profile.obligations
        if obligation.validator_id == "vitest"
        for path in obligation.code_under_test_paths
    )
    try:
        closure = _vitest_support_closure(root, ref, tests, products)
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
                "code_under_test_paths": [
                    path.as_posix() for path in sorted(item.code_under_test_paths)
                ],
            }
            for item in profile.obligations
        ],
    }
    if root is not None:
        support_closure_digest = _support_digest(root, ref, profile)[0]
        jest_support_digest = _jest_support_digest(root, ref, profile)[0]
        payload["support_closure_digest"] = hashlib.sha256(
            (
                support_closure_digest
                + jest_support_digest
                + _vitest_support_digest(root, ref, profile)[0]
                + _playwright_support_digest(root, ref, profile)[0]
            ).encode()
        ).hexdigest()
        adapter_identities = config.adapter_identities or _capture_adapter_identities(
            root, config
        )[0]
        payload["validator_command_digest"] = hashlib.sha256(json.dumps(
            adapter_identities, separators=(",", ":")
        ).encode()).hexdigest()
        payload["adapter_identities"] = list(adapter_identities)
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
        return _validator_tree_identity(path)
    except (OSError, ValueError):
        data = b"<unreadable>"
    return hashlib.sha256(str(path).encode() + b"\0" + data).hexdigest()


def _update_validator_path_identity(
    digest: "hashlib._Hash", path: Path, logical: str, active: set[Path]
) -> None:
    """Hash one path without traversing a symlink as a directory entry."""
    metadata = path.lstat()
    mode = metadata.st_mode & 0o7777
    digest.update(logical.encode() + b"\0" + str(mode).encode() + b"\0")
    if path.is_symlink():
        target_text = os.readlink(path)
        digest.update(b"symlink\0" + target_text.encode() + b"\0")
        target = path.resolve(strict=True)
        if target in active:
            raise ValueError(f"validator toolchain symlink cycle: {path}")
        _update_validator_path_identity(
            digest, target, logical + "->target", active | {target}
        )
        return
    if path.is_file():
        digest.update(b"file\0")
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
        digest.update(b"\0")
        return
    if path.is_dir():
        digest.update(b"directory\0")
        with os.scandir(path) as entries:
            children = sorted(entries, key=lambda item: item.name)
        for child in children:
            if child.name in VITEST_CACHE_NAMES:
                continue
            _update_validator_path_identity(
                digest,
                Path(child.path),
                f"{logical}/{child.name}" if logical else child.name,
                active,
            )
        return
    raise ValueError(f"validator toolchain role is not a file or directory: {path}")


def _validator_tree_identity(root: Path) -> str:
    """Hash modes, links, targets, and bytes with cache exclusion and no link walk."""
    digest = hashlib.sha256()
    canonical = root.absolute()
    _update_validator_path_identity(digest, canonical, "", {canonical})
    return digest.hexdigest()


def _member_content_digest(path: Path) -> str:
    """Hash one regular member without following a replacement symlink."""
    digest = hashlib.sha256()
    descriptor = os.open(
        path,
        os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0),
    )
    try:
        with os.fdopen(descriptor, "rb", closefd=False) as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
    finally:
        os.close(descriptor)
    return digest.hexdigest()


def _capture_vitest_member(
    path: Path, role: str, relative_path: PurePosixPath,
) -> VitestToolchainMember:
    """Capture exact lstat type, mode, link spelling, and regular bytes."""
    metadata = path.lstat()
    mode = stat.S_IMODE(metadata.st_mode)
    if stat.S_ISLNK(metadata.st_mode):
        return VitestToolchainMember(
            role, relative_path, "symlink", mode,
            link_target=os.readlink(path),
        )
    if stat.S_ISREG(metadata.st_mode):
        return VitestToolchainMember(
            role, relative_path, "file", mode,
            content_digest=_member_content_digest(path),
        )
    if stat.S_ISDIR(metadata.st_mode):
        return VitestToolchainMember(role, relative_path, "directory", mode)
    raise ValueError(f"Vitest toolchain member has unsupported type: {path}")


def _capture_vitest_tree(
    root: Path, role: str, *, validate_links: bool = True,
) -> tuple[VitestToolchainMember, ...]:
    """Capture a complete cache-excluding tree without traversing links."""
    captured = [_capture_vitest_member(root, role, PurePosixPath("."))]
    pending = [root]
    while pending:
        directory = pending.pop()
        with os.scandir(directory) as entries:
            children = sorted(entries, key=lambda item: item.name)
        for child in children:
            if child.name in VITEST_CACHE_NAMES:
                continue
            path = Path(child.path)
            relative = PurePosixPath(path.relative_to(root).as_posix())
            member = _capture_vitest_member(path, role, relative)
            captured.append(member)
            if member.kind == "directory":
                pending.append(path)
            elif member.kind == "symlink" and validate_links:
                target = path.resolve(strict=True)
                if not _path_is_relative_to(target, root.resolve()):
                    raise ValueError(
                        f"Vitest dependency symlink escapes captured closure: {relative}"
                    )
    return tuple(sorted(captured, key=lambda item: item.relative_path.as_posix()))


def _vitest_members_identity(
    members: tuple[VitestToolchainMember, ...],
) -> str:
    """Hash an immutable typed member manifest, not live staged bytes."""
    payload = [
        {
            "role": member.role,
            "path": member.relative_path.as_posix(),
            "kind": member.kind,
            "mode": member.mode,
            "digest": member.content_digest,
            "target": member.link_target,
        }
        for member in members
    ]
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def _descriptor_vitest_members(
    launcher: Path,
    entrypoint: Path,
    dependencies: Path,
    native_runtime: tuple[Path, ...],
    lockfile: Path,
) -> tuple[VitestToolchainMember, ...]:
    """Capture every typed role and the complete dependency membership."""
    members = list(_capture_vitest_tree(dependencies, "dependencies"))
    members.extend((
        _capture_vitest_member(launcher, "launcher", PurePosixPath(".")),
        _capture_vitest_member(entrypoint, "entrypoint", PurePosixPath(".")),
        _capture_vitest_member(lockfile, "lockfile", PurePosixPath(".")),
    ))
    members.extend(
        _capture_vitest_member(path, "native_runtime", PurePosixPath(str(index)))
        for index, path in enumerate(native_runtime)
    )
    return tuple(sorted(
        members,
        key=lambda item: (item.role, item.relative_path.as_posix()),
    ))


def _manifest_regular_path(value: object, role: str) -> Path:
    """Return one canonical non-symlink regular manifest role path."""
    if not isinstance(value, str) or not Path(value).is_absolute():
        raise ValueError(f"Vitest toolchain role {role} must be an absolute path")
    path = Path(value)
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"Vitest toolchain role {role} must be a regular file")
    return path.resolve(strict=True)


def _load_vitest_toolchain_descriptor(
    root: Path, config: RunnerConfig
) -> VitestToolchainDescriptor:
    """Parse, type-check, command-match, and identity one Vitest descriptor."""
    command = config.vitest_command
    manifest = config.vitest_toolchain_manifest
    if command is None:
        raise ValueError("Vitest command and toolchain manifest are required together")
    command_error = _vitest_command_error(root, command)
    if command_error is not None:
        raise ValueError(command_error)
    if manifest is None:
        raise ValueError("Vitest command and toolchain manifest are required together")
    manifest = manifest.expanduser()
    if manifest.is_symlink() or not manifest.is_file():
        raise ValueError("Vitest toolchain manifest must be a regular file")
    if _path_is_relative_to(manifest.resolve(), root.resolve()):
        raise ValueError("Vitest toolchain manifest must be external to candidate checkout")
    try:
        payload = json.loads(manifest.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ValueError("Vitest toolchain manifest is invalid") from exc
    if not isinstance(payload, dict) or set(payload) != {"version", "roles"}:
        raise ValueError("Vitest toolchain manifest must declare version and typed roles")
    roles = payload.get("roles")
    if payload.get("version") != 1 or not isinstance(roles, dict):
        raise ValueError("Vitest toolchain manifest roles schema is invalid")
    if set(roles) != VITEST_TOOLCHAIN_ROLES:
        raise ValueError("Vitest toolchain manifest roles are incomplete")
    launcher = _manifest_regular_path(roles["launcher"], "launcher")
    entrypoint = _manifest_regular_path(roles["entrypoint"], "entrypoint")
    lockfile = _manifest_regular_path(roles["lockfile"], "lockfile")
    dependency_value = roles["dependencies"]
    if not isinstance(dependency_value, str) or not Path(dependency_value).is_absolute():
        raise ValueError("Vitest toolchain dependencies must be an absolute directory")
    dependency_path = Path(dependency_value)
    if dependency_path.is_symlink() or not dependency_path.is_dir():
        raise ValueError("Vitest toolchain dependencies must be a directory")
    dependencies = dependency_path.resolve(strict=True)
    try:
        entrypoint.relative_to(dependencies)
    except ValueError as exc:
        raise ValueError("Vitest entrypoint must be inside dependencies role") from exc
    native_values = roles["native_runtime"]
    if not isinstance(native_values, list) or not native_values:
        raise ValueError("Vitest native_runtime role must be a non-empty path array")
    native_runtime = tuple(
        _manifest_regular_path(value, "native_runtime") for value in native_values
    )
    command_paths = tuple(Path(part).expanduser().resolve(strict=True) for part in command)
    if command_paths[0] != launcher:
        raise ValueError("Vitest launcher role does not match command launcher")
    if command_paths[1] != entrypoint:
        raise ValueError("Vitest entrypoint role does not match command entrypoint")
    if not os.access(launcher, os.X_OK):
        raise ValueError("Vitest toolchain launcher is not executable")
    for role_path in (launcher, entrypoint, dependencies, *native_runtime, lockfile):
        if _path_is_relative_to(role_path, root.resolve()):
            raise ValueError("Vitest toolchain roles must be external to candidate checkout")
    members = _descriptor_vitest_members(
        launcher, entrypoint, dependencies, native_runtime, lockfile
    )
    dependency_members = tuple(
        member for member in members if member.role == "dependencies"
    )
    dependencies_identity = _vitest_members_identity(dependency_members)
    identity = hashlib.sha256(json.dumps({
        "members": _vitest_members_identity(members),
        "launch_policy": {
            "linux_wasm_trap_handler_disabled": sys.platform.startswith("linux"),
        },
    }, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    if config.vitest_toolchain_identity not in {None, identity}:
        raise ValueError("Vitest toolchain changed across protocol execution")
    return VitestToolchainDescriptor(
        manifest.resolve(), launcher, entrypoint, dependencies, native_runtime,
        lockfile, identity, dependencies_identity, members,
    )


def _copy_vitest_dependencies(source: Path, destination: Path) -> None:
    """Copy a package closure without following links or copying caches."""
    source_mode = stat.S_IMODE(source.lstat().st_mode)
    destination.mkdir(mode=source_mode)

    def copy_directory(source_fd: int, destination_fd: int) -> None:
        for name in sorted(os.listdir(source_fd)):
            if name in VITEST_CACHE_NAMES:
                continue
            metadata = os.stat(name, dir_fd=source_fd, follow_symlinks=False)
            mode = stat.S_IMODE(metadata.st_mode)
            if stat.S_ISDIR(metadata.st_mode):
                child_source = os.open(
                    name,
                    os.O_RDONLY | os.O_DIRECTORY | getattr(os, "O_NOFOLLOW", 0),
                    dir_fd=source_fd,
                )
                try:
                    os.mkdir(name, mode=mode, dir_fd=destination_fd)
                    child_destination = os.open(
                        name, os.O_RDONLY | os.O_DIRECTORY, dir_fd=destination_fd
                    )
                    try:
                        copy_directory(child_source, child_destination)
                        os.fchmod(child_destination, mode)
                    finally:
                        os.close(child_destination)
                finally:
                    os.close(child_source)
            elif stat.S_ISLNK(metadata.st_mode):
                os.symlink(
                    os.readlink(name, dir_fd=source_fd),
                    name,
                    dir_fd=destination_fd,
                )
            elif stat.S_ISREG(metadata.st_mode):
                child_source = os.open(
                    name,
                    os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0),
                    dir_fd=source_fd,
                )
                try:
                    child_destination = os.open(
                        name,
                        os.O_WRONLY | os.O_CREAT | os.O_EXCL,
                        mode,
                        dir_fd=destination_fd,
                    )
                    try:
                        while chunk := os.read(child_source, 1024 * 1024):
                            os.write(child_destination, chunk)
                        os.fchmod(child_destination, mode)
                    finally:
                        os.close(child_destination)
                finally:
                    os.close(child_source)
            else:
                raise ValueError(
                    f"Vitest toolchain member has unsupported type: {name}"
                )

    source_fd = os.open(
        source,
        os.O_RDONLY | os.O_DIRECTORY | getattr(os, "O_NOFOLLOW", 0),
    )
    try:
        destination_fd = os.open(destination, os.O_RDONLY | os.O_DIRECTORY)
        try:
            copy_directory(source_fd, destination_fd)
            os.fchmod(destination_fd, source_mode)
        finally:
            os.close(destination_fd)
    finally:
        os.close(source_fd)


def _vitest_role_members(
    descriptor: VitestToolchainDescriptor, role: str,
) -> tuple[VitestToolchainMember, ...]:
    """Return the captured immutable members for one typed role."""
    return tuple(member for member in descriptor.members if member.role == role)


def _assert_vitest_members(
    actual: tuple[VitestToolchainMember, ...],
    expected: tuple[VitestToolchainMember, ...],
    context: str,
) -> None:
    """Fail when current bytes, modes, types, links, or membership differ."""
    if actual != expected:
        raise ValueError(f"Vitest {context} member identity mismatch")


def _verify_vitest_descriptor_source(
    descriptor: VitestToolchainDescriptor,
) -> None:
    """Verify live source roles against the previously captured descriptor."""
    current = _descriptor_vitest_members(
        descriptor.launcher,
        descriptor.entrypoint,
        descriptor.dependencies,
        descriptor.native_runtime,
        descriptor.lockfile,
    )
    _assert_vitest_members(current, descriptor.members, "source")


def _copy_vitest_regular(source: Path, destination: Path, mode: int) -> None:
    """Copy one regular descriptor member with no-follow source semantics."""
    source_fd = os.open(source, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        destination_fd = os.open(
            destination, os.O_WRONLY | os.O_CREAT | os.O_EXCL, mode
        )
        try:
            while chunk := os.read(source_fd, 1024 * 1024):
                os.write(destination_fd, chunk)
        finally:
            os.close(destination_fd)
    finally:
        os.close(source_fd)
    destination.chmod(mode)


def _verify_vitest_phase_toolchain(phase: VitestPhaseToolchain) -> None:
    """Verify the executable copy against captured descriptor identity."""
    descriptor = phase.descriptor
    dependency_members = _capture_vitest_tree(
        phase.dependencies, "dependencies", validate_links=False
    )
    _assert_vitest_members(
        dependency_members,
        _vitest_role_members(descriptor, "dependencies"),
        "copied dependencies",
    )
    singleton_paths = {
        "launcher": phase.launcher,
        "entrypoint": phase.entrypoint,
        "lockfile": phase.lockfile,
    }
    for role, path in singleton_paths.items():
        actual = (_capture_vitest_member(path, role, PurePosixPath(".")),)
        _assert_vitest_members(
            actual, _vitest_role_members(descriptor, role), f"copied {role}"
        )
    actual_native = tuple(
        _capture_vitest_member(path, "native_runtime", PurePosixPath(str(index)))
        for index, path in enumerate(phase.native_runtime)
    )
    _assert_vitest_members(
        actual_native,
        _vitest_role_members(descriptor, "native_runtime"),
        "copied native runtime",
    )
    expected_controller = {
        PurePosixPath("launcher"), PurePosixPath("lockfile"), PurePosixPath("native")
    } | {
        PurePosixPath("native") / str(index)
        for index in range(len(phase.native_runtime))
    }
    actual_controller = {
        PurePosixPath(path.relative_to(phase.controller).as_posix())
        for path in phase.controller.rglob("*")
    }
    if actual_controller != expected_controller:
        raise ValueError("Vitest copied controller member identity mismatch")


def _prepare_vitest_toolchain(
    root: Path, descriptor: VitestToolchainDescriptor
) -> VitestPhaseToolchain:
    """Copy identity-checked launcher and dependency bytes into one phase."""
    _verify_vitest_descriptor_source(descriptor)
    destination = root / "node_modules"
    if destination.exists() or destination.is_symlink():
        raise ValueError("Vitest phase tree already contains candidate node_modules")
    _copy_vitest_dependencies(descriptor.dependencies, destination)
    (destination / ".vite-temp").mkdir()
    (destination / ".vite").mkdir()
    controller = root / ".pdd-vitest-toolchain"
    controller.mkdir(mode=0o700)
    launcher = controller / "launcher"
    launcher_member = _vitest_role_members(descriptor, "launcher")[0]
    _copy_vitest_regular(descriptor.launcher, launcher, launcher_member.mode)
    lockfile = controller / "lockfile"
    lockfile_member = _vitest_role_members(descriptor, "lockfile")[0]
    _copy_vitest_regular(descriptor.lockfile, lockfile, lockfile_member.mode)
    native_directory = controller / "native"
    native_directory.mkdir(mode=0o700)
    native_runtime = []
    for index, source in enumerate(descriptor.native_runtime):
        destination_native = native_directory / str(index)
        member = _vitest_role_members(descriptor, "native_runtime")[index]
        _copy_vitest_regular(source, destination_native, member.mode)
        native_runtime.append(destination_native)
    entrypoint = destination / descriptor.entrypoint.relative_to(
        descriptor.dependencies
    )
    if not entrypoint.is_file() or entrypoint.is_symlink():
        raise ValueError("copied Vitest entrypoint is not a regular file")
    phase = VitestPhaseToolchain(
        launcher=launcher,
        entrypoint=entrypoint,
        lockfile=lockfile,
        native_runtime=tuple(native_runtime),
        readable_roots=(),
        readable_bindings=tuple(zip(native_runtime, descriptor.native_runtime)),
        dependencies=destination,
        controller=controller,
        descriptor=descriptor,
    )
    _verify_vitest_phase_toolchain(phase)
    current = _load_vitest_toolchain_descriptor(
        root,
        RunnerConfig(
            vitest_command=(str(descriptor.launcher), str(descriptor.entrypoint)),
            vitest_toolchain_manifest=descriptor.manifest,
            vitest_toolchain_identity=descriptor.identity,
        ),
    )
    if current.identity != descriptor.identity:
        raise ValueError("Vitest toolchain changed during phase setup")
    _verify_vitest_phase_toolchain(phase)
    return phase


def _directory_identity(path: Path) -> str:
    """Return a stable digest for files under a protected dependency directory."""
    digest = hashlib.sha256()
    if not path.is_dir():
        digest.update(str(path).encode() + b"\0<missing>")
        return digest.hexdigest()
    for item in sorted(path.rglob("*")):
        relative = item.relative_to(path).as_posix().encode()
        if item.is_symlink():
            try:
                target = os.readlink(item).encode()
            except OSError:
                target = b"<unreadable>"
            digest.update(relative + b"\0<symlink>\0" + target + b"\0")
            continue
        if not item.is_file():
            continue
        try:
            data = item.read_bytes()
        except OSError:
            data = b"<unreadable>"
        digest.update(relative + b"\0" + data + b"\0")
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
        payload["jest_toolchain"] = [
            _validator_tree_identity(path)
            for path in _jest_toolchain_roots(config.jest_command)
        ]
    if config.vitest_command is not None:
        try:
            descriptor = _load_vitest_toolchain_descriptor(root, config)
            payload["vitest"] = {
                "command": [str(descriptor.launcher), str(descriptor.entrypoint)],
                "identity": descriptor.identity,
            }
        except (OSError, ValueError):
            payload["vitest"] = "invalid-vitest-toolchain"
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


def _adapter_capture_error_identity(adapter: str, error: BaseException) -> str:
    """Return a stable, non-executable record of one adapter capture failure."""
    payload = {
        "adapter": adapter,
        "error_type": type(error).__name__,
        "message": str(error),
    }
    return "error:" + hashlib.sha256(json.dumps(
        payload, sort_keys=True, separators=(",", ":")
    ).encode()).hexdigest()


def _capture_adapter_identities(
    root: Path, config: RunnerConfig,
) -> tuple[tuple[tuple[str, str], ...], dict[str, str]]:
    """Capture stable success/error identities for configured JS adapters once."""
    identities: list[tuple[str, str]] = []
    errors: dict[str, str] = {}
    if config.jest_command is not None:
        try:
            error = _protected_command_error(root, config.jest_command)
            if error is not None:
                raise ValueError(error)
            identities.append(("jest", hashlib.sha256(json.dumps({
                "argv": [_command_part_identity(root, part) for part in config.jest_command],
                "toolchain": [
                    _validator_tree_identity(path)
                    for path in _jest_toolchain_roots(config.jest_command)
                ],
            }, sort_keys=True, separators=(",", ":")).encode()).hexdigest()))
        except (OSError, UnicodeError, ValueError) as exc:
            errors["jest"] = str(exc)
            identities.append(("jest", _adapter_capture_error_identity("jest", exc)))
    if config.vitest_command is not None or config.vitest_toolchain_manifest is not None:
        try:
            descriptor = _load_vitest_toolchain_descriptor(root, config)
            identities.append(("vitest", hashlib.sha256(json.dumps({
                "toolchain": descriptor.identity,
                "linux_wasm_trap_handler_disabled": sys.platform.startswith("linux"),
            }, sort_keys=True, separators=(",", ":")).encode()).hexdigest()))
        except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
            errors["vitest"] = str(exc)
            identities.append(("vitest", _adapter_capture_error_identity("vitest", exc)))
    return tuple(sorted(identities)), errors


def _verify_adapter_identities(root: Path, config: RunnerConfig) -> None:
    """Verify live configured adapter bytes against the captured identities."""
    captured, errors = _capture_adapter_identities(root, config)
    if errors:
        raise ValueError("configured adapter identity recapture failed")
    if config.adapter_identities and captured != config.adapter_identities:
        raise ValueError("configured adapter content identity changed")


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
) -> tuple[tuple[str, str, int, int, int], ...]:
    """Return byte-change-sensitive metadata without rereading runtime bytes."""
    manifest = []
    for name, path in entries:
        metadata = path.stat()
        manifest.append(
            (
                name,
                str(path),
                metadata.st_mtime_ns,
                metadata.st_ctime_ns,
                metadata.st_size,
            )
        )
    return tuple(manifest)


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
    return untrusted_child_environment(home=home, extra={"NODE_ENV": "test"})


def _jest_command(config: RunnerConfig) -> tuple[str, ...] | None:
    """Return an explicit local Jest argv prefix; never invoke an npm script."""
    if config.jest_command is not None:
        return config.jest_command
    return None


def _jest_toolchain_roots(command: tuple[str, ...]) -> tuple[Path, ...]:
    """Return external package roots needed by an absolute Jest entry point."""
    roots: set[Path] = set()
    for part in command[1:]:
        path = Path(part).expanduser()
        if not path.is_absolute():
            continue
        resolved = path.resolve()
        for parent in resolved.parents:
            if parent.parent.name == "node_modules":
                roots.add(parent)
                break
    return tuple(sorted(roots))


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
    # pylint: disable=too-many-return-statements,too-many-branches
    """Return a fail-closed reason for unprotected explicit validator argv."""
    if not command:
        return "explicit validator command is empty"
    candidate_root = root.resolve()
    path_operands: list[Path] = []
    executable = Path(command[0]).expanduser()
    if not executable.is_absolute():
        return "explicit validator command executable must be an absolute path"
    if executable.name.casefold() in {"npx", "npm", "pnpm", "yarn", "bunx", "env"}:
        return "validator launcher indirection is not trusted"
    if not executable.is_file():
        return "explicit validator command executable is missing"
    if not os.access(executable, os.X_OK):
        return "explicit validator command executable is not executable"
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
            return (
                "pathless validator entry point operand is not trusted; use an "
                "absolute digest-bound external path"
            )
        path_operands.append(path if path.is_absolute() else root / path)
    for index, operand in enumerate(path_operands):
        resolved = operand.resolve()
        if not resolved.exists() or not resolved.is_file() or resolved.is_symlink():
            return "explicit validator command path is missing or not a regular file"
        if index == 0 and not os.access(resolved, os.X_OK):
            return "explicit validator command executable is not executable"
        if _path_is_relative_to(resolved, candidate_root):
            return "explicit validator command inside the candidate checkout is not trusted"
    return None


def _vitest_command_error(root: Path, command: tuple[str, ...]) -> str | None:
    """Require exactly one absolute launcher and entrypoint for Vitest."""
    if len(command) != 2:
        return "Vitest command must contain exactly an absolute launcher and entrypoint"
    if any(part.startswith("-") for part in command):
        return "Vitest command cannot contain launcher flags or controls"
    return _protected_command_error(root, command)


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
    # pylint: disable=too-many-return-statements
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
        return (
            EvidenceOutcome.NOT_COLLECTED,
            "zero protected Jest test identities collected",
            (),
        )
    if len(set(identities)) != len(identities):
        return (
            EvidenceOutcome.COLLECTION_ERROR,
            "Jest reporter emitted duplicate test identities",
            (),
        )
    if expected is not None and identities != expected:
        return (
            EvidenceOutcome.QUARANTINED,
            "checked-head Jest identities differ from protected base",
            identities,
        )
    statuses = {item["status"] for item in tests}
    if statuses - {"passed", "failed", "pending", "todo", "skipped", "disabled"}:
        return (
            EvidenceOutcome.COLLECTION_ERROR,
            "Jest reporter emitted an unsupported status",
            identities,
        )
    if returncode or "failed" in statuses:
        return EvidenceOutcome.FAIL, "Jest reported failed protected tests", identities
    if statuses - {"passed"}:
        return EvidenceOutcome.SKIP, "Jest reported skipped or todo protected tests", identities
    return (
        EvidenceOutcome.PASS,
        f"{len(identities)} protected Jest tests passed",
        identities,
    )


def _run_jest(
    root: Path, paths: tuple[PurePosixPath, ...], timeout_seconds: int,
    config: RunnerConfig, expected: tuple[str, ...] | None = None,
) -> tuple[RunnerExecution, tuple[str, ...]]:
    # pylint: disable=too-many-return-statements
    """Run exact protected Jest paths using a temporary trusted reporter."""
    command_prefix = _jest_command(config)
    if command_prefix is None:
        if (root / "node_modules" / "jest" / "bin" / "jest.js").is_file():
            return RunnerExecution(
                "jest",
                EvidenceOutcome.ERROR,
                "jest-untrusted",
                "candidate node_modules Jest runner is not trusted",
            ), ()
        return RunnerExecution(
            "jest",
            EvidenceOutcome.ERROR,
            "jest-unavailable",
            "no local Jest binary is available",
        ), ()
    command_error = _protected_command_error(root, command_prefix)
    if command_error is not None:
        return RunnerExecution(
            "jest", EvidenceOutcome.ERROR, "jest-untrusted", command_error
        ), ()
    try:
        config_path, _config_data = _jest_config(root, "HEAD")
    except ValueError as exc:
        return RunnerExecution(
            "jest", EvidenceOutcome.ERROR, "jest-config", str(exc)
        ), ()
    with tempfile.TemporaryDirectory(prefix="pdd-trusted-jest-") as directory:
        temporary = Path(directory)
        controllers = temporary / f"controller-{os.urandom(16).hex()}"
        controllers.mkdir(mode=0o700)
        scratch = temporary / "scratch"
        home = scratch / "home"
        home.mkdir(mode=0o700, parents=True)
        reporter = controllers / "reporter.cjs"
        output = controllers / "results.json"
        reporter.write_text(_JEST_REPORTER, encoding="utf-8")
        output.touch(mode=0o600)
        command = [
            *command_prefix,
            *(path.as_posix() for path in paths),
            "--runInBand",
            f"--config={root / config_path}",
            f"--reporters={reporter}",
        ]
        digest = hashlib.sha256(
            json.dumps(command, separators=(",", ":")).encode()
        ).hexdigest()
        try:
            result, surviving = _managed_subprocess(
                command,
                cwd=root,
                timeout=timeout_seconds,
                env=_jest_environment(home)
                | {"PDD_TRUSTED_JEST_OUTPUT": str(output)},
                writable_roots=(scratch,),
                writable_files=(output,),
                readable_roots=(
                    root,
                    reporter,
                    *(
                        Path(part).expanduser().resolve()
                        for part in command_prefix[1:]
                        if Path(part).expanduser().is_absolute()
                    ),
                    *_jest_toolchain_roots(command_prefix),
                ),
            )
        except OSError as exc:
            return RunnerExecution(
                "jest",
                EvidenceOutcome.ERROR,
                digest,
                f"Jest process launch failed: {exc}",
            ), ()
        if surviving:
            return RunnerExecution(
                "jest",
                EvidenceOutcome.ERROR,
                digest,
                "Jest left a surviving process-group descendant",
            ), ()
        if result.returncode == 124:
            return RunnerExecution(
                "jest", EvidenceOutcome.TIMEOUT, digest, "Jest execution timed out"
            ), ()
        if result.returncode >= 125:
            diagnostic = (result.stderr or result.stdout).strip()[-500:]
            detail = "protected sandbox rejected Jest execution"
            if diagnostic:
                detail += f": {diagnostic}"
            return RunnerExecution(
                "jest", EvidenceOutcome.ERROR, digest, detail
            ), ()
        outcome, detail, identities = _jest_result(output, result.returncode, expected)
        return RunnerExecution("jest", outcome, digest, detail), identities


def _vitest_command(config: RunnerConfig) -> tuple[str, ...] | None:
    """Return an explicit local Vitest argv prefix; never invoke an npm script."""
    if config.vitest_command is not None:
        return config.vitest_command
    return None


def _vitest_environment(home: Path) -> dict[str, str]:
    """Return a credential-free, non-ambient environment for Vitest."""
    return untrusted_child_environment(
        drop={"PYTHONPATH", "PYTHONHOME", "PDD_PATH"}
    ) | {
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
        if not isinstance(payload, dict):
            raise ValueError("malformed Vitest reporter payload")
        tests = payload.get("tests")
        if tests is None:
            results = payload.get("testResults")
            if not isinstance(results, list):
                raise ValueError("malformed Vitest reporter payload")
            tests = [
                {
                    "identity": (
                        Path(item["name"]).resolve().relative_to(root.resolve()).as_posix()
                        + "::"
                        + assertion.get("fullName", assertion["title"])
                    ),
                    "status": assertion["status"],
                }
                for item in results
                for assertion in item["assertionResults"]
            ]
        if not isinstance(tests, list) or not all(
            isinstance(item, dict)
            and isinstance(item.get("identity"), str)
            and isinstance(item.get("status"), str)
            for item in tests
        ):
            raise ValueError("malformed Vitest reporter payload")
        prior_failures = any(
            item.get("failureMessages")
            for result in payload.get("testResults", [])
            for item in result.get("assertionResults", [])
        )
    except (AttributeError, OSError, TypeError, ValueError, json.JSONDecodeError, KeyError):
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
    if returncode or "failed" in statuses or prior_failures:
        return EvidenceOutcome.FAIL, "Vitest reported failed protected tests", identities
    if statuses - {"passed"}:
        return EvidenceOutcome.SKIP, "Vitest reported skipped or todo protected tests", identities
    return EvidenceOutcome.PASS, f"{len(identities)} protected Vitest tests passed", identities


def _vitest_reporter_source(result_fd: int) -> str:
    """Return a checker-owned reporter that writes only from the coordinator."""
    return f"""import fs from 'node:fs';
import path from 'node:path';
const RESULT_FD = {result_fd};
export default class PddTrustedVitestReporter {{
  constructor() {{ this.tests = []; }}
  onTestCaseResult(test) {{
    const result = test.result();
    const filename = path.relative(process.cwd(), test.module.moduleId);
    this.tests.push({{
      identity: filename + '::' + test.fullName,
      status: result.state,
      failureMessages: (result.errors || []).map((item) => item.stack || item.message),
    }});
  }}
  onTestRunEnd() {{
    fs.writeSync(RESULT_FD, JSON.stringify({{tests: this.tests}}));
  }}
}}
"""


def _drain_result_pipe(
    read_fd: int, finished: threading.Event, result: dict[str, object]
) -> None:
    """Drain the private FIFO while the child runs, discarding over-cap bytes."""
    chunks: list[bytes] = []
    size = 0
    overflow = False
    try:
        while not finished.is_set():
            ready, _write, _error = select.select((read_fd,), (), (), 0.05)
            if not ready:
                continue
            try:
                chunk = os.read(read_fd, 1024 * 1024)
            except BlockingIOError:
                continue
            if not chunk:
                continue
            size += len(chunk)
            if size > VITEST_RESULT_MAX_BYTES:
                overflow = True
            elif not overflow:
                chunks.append(chunk)
        while True:
            try:
                chunk = os.read(read_fd, 1024 * 1024)
            except BlockingIOError:
                break
            if not chunk:
                break
            size += len(chunk)
            if size > VITEST_RESULT_MAX_BYTES:
                overflow = True
            elif not overflow:
                chunks.append(chunk)
    except OSError as exc:
        result["error"] = exc
    result["overflow"] = overflow
    result["data"] = b"" if overflow else b"".join(chunks)


def _run_vitest(
    root: Path,
    paths: tuple[PurePosixPath, ...],
    timeout_seconds: int,
    config: RunnerConfig,
    expected: tuple[str, ...] | None = None,
    command_root: Path | None = None,
    phase_toolchain: VitestPhaseToolchain | None = None,
) -> tuple[RunnerExecution, tuple[str, ...]]:
    # pylint: disable=too-many-return-statements
    """Run exact protected Vitest paths with a private coordinator reporter."""
    tool_root = command_root or root
    command_prefix = _vitest_command(config)
    if command_prefix is None:
        if (tool_root / "node_modules" / "vitest" / "vitest.mjs").is_file():
            return RunnerExecution("vitest", EvidenceOutcome.ERROR, "vitest-untrusted", "candidate node_modules Vitest runner is not trusted"), ()
        return RunnerExecution("vitest", EvidenceOutcome.ERROR, "vitest-unavailable", "no local Vitest binary is available"), ()
    try:
        descriptor = _load_vitest_toolchain_descriptor(tool_root, config)
        if phase_toolchain is None:
            phase_toolchain = _prepare_vitest_toolchain(root, descriptor)
        if phase_toolchain.descriptor.identity != descriptor.identity:
            raise ValueError("Vitest copied descriptor identity mismatch")
        _verify_vitest_phase_toolchain(phase_toolchain)
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        return RunnerExecution(
            "vitest", EvidenceOutcome.ERROR, "vitest-toolchain", str(exc)
        ), ()
    try:
        config_path, _config_data = _vitest_config(root, "HEAD")
    except ValueError as exc:
        return RunnerExecution("vitest", EvidenceOutcome.ERROR, "vitest-config", str(exc)), ()
    with tempfile.TemporaryDirectory(prefix="pdd-trusted-vitest-") as directory:
        temporary = Path(directory)
        scratch = temporary / "scratch"
        home = scratch / "home"
        home.mkdir(parents=True, mode=0o700)
        output = temporary / "results.json"
        reporter = temporary / f"reporter-{os.urandom(16).hex()}.mjs"
        result_directory = temporary / f"channel-{os.urandom(16).hex()}"
        result_directory.mkdir(mode=0o700)
        result_fifo = result_directory / "result.fifo"
        os.mkfifo(result_fifo, mode=0o600)
        read_fd = os.open(result_fifo, os.O_RDONLY | os.O_NONBLOCK)
        drain_finished = threading.Event()
        drained: dict[str, object] = {}
        drain_thread = threading.Thread(
            target=_drain_result_pipe, args=(read_fd, drain_finished, drained), daemon=True
        )
        drain_thread.start()
        result_fd = 198
        reporter.write_text(_vitest_reporter_source(result_fd), encoding="utf-8")
        command = [
            str(phase_toolchain.launcher),
            *( ("--disable-wasm-trap-handler",) if sys.platform.startswith("linux") else () ),
            str(phase_toolchain.entrypoint),
            "run",
            *(path.as_posix() for path in paths),
            f"--config={root / config_path}",
            f"--reporter={reporter}",
        ]
        digest = hashlib.sha256(json.dumps(command, separators=(",", ":")).encode()).hexdigest()
        before = _validator_tree_identity(root)
        try:
            cache_roots = tuple(
                path for path in (
                    root / "node_modules/.vite-temp", root / "node_modules/.vite"
                ) if path.is_dir()
            )
            result, surviving = run_supervised(
                command,
                cwd=root,
                timeout=timeout_seconds,
                env=_vitest_environment(home),
                writable_roots=(scratch, *cache_roots),
                readable_roots=(reporter, *phase_toolchain.readable_roots),
                readable_bindings=phase_toolchain.readable_bindings,
                result_fifo=result_fifo,
                result_fd=result_fd,
            )
        except (OSError, UnicodeError, ValueError) as exc:
            drain_finished.set()
            drain_thread.join(timeout=1)
            os.close(read_fd)
            return RunnerExecution("vitest", EvidenceOutcome.ERROR, digest, f"Vitest launch failed: {exc}"), ()
        drain_finished.set()
        drain_thread.join(timeout=2)
        try:
            if "error" in drained:
                raise drained["error"]
            if drained.get("overflow"):
                return RunnerExecution(
                    "vitest", EvidenceOutcome.ERROR, digest,
                    "Vitest result transport exceeded byte limit",
                ), ()
            output.write_bytes(drained.get("data", b""))
        except OSError as exc:
            return RunnerExecution(
                "vitest", EvidenceOutcome.ERROR, digest,
                f"Vitest result transport failed: {exc}",
            ), ()
        finally:
            os.close(read_fd)
        if result.returncode == 124:
            return RunnerExecution("vitest", EvidenceOutcome.TIMEOUT, digest, "Vitest execution timed out"), ()
        if surviving:
            return RunnerExecution("vitest", EvidenceOutcome.ERROR, digest, "Vitest left a surviving process-group descendant"), ()
        output_data = output.read_bytes()
        if result.returncode in {126, 127} and not output_data:
            return RunnerExecution("vitest", EvidenceOutcome.ERROR, digest, "Vitest launcher is missing or not executable"), ()
        if result.returncode and not output_data:
            detail = (result.stderr or result.stdout or "Vitest exited without a result")[-2000:]
            return RunnerExecution("vitest", EvidenceOutcome.FAIL, digest, detail), ()
        if not output_data:
            return RunnerExecution(
                "vitest", EvidenceOutcome.COLLECTION_ERROR, digest,
                "Vitest reporter produced no result",
            ), ()
        if _validator_tree_identity(root) != before:
            return RunnerExecution("vitest", EvidenceOutcome.QUARANTINED, digest, "Vitest phase modified its protected execution tree"), ()
        try:
            _verify_vitest_phase_toolchain(phase_toolchain)
            if _load_vitest_toolchain_descriptor(tool_root, replace(
                config, vitest_toolchain_identity=descriptor.identity
            )).identity != descriptor.identity:
                raise ValueError("Vitest toolchain changed during phase")
        except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
            return RunnerExecution(
                "vitest", EvidenceOutcome.ERROR, digest,
                f"Vitest toolchain recheck failed: {exc}",
            ), ()
        outcome, detail, identities = _vitest_result(root, output, result.returncode, expected)
        return RunnerExecution("vitest", outcome, digest, detail), identities


def _playwright_command(config: RunnerConfig) -> tuple[str, ...] | None:
    """Return the checked-in local Playwright CLI, never an npm script."""
    if config.playwright_command is not None:
        return config.playwright_command
    return None


def _playwright_command_error(root: Path, command: tuple[str, ...]) -> str | None:
    """Enforce the exact protected Playwright launcher grammar."""
    error = _protected_command_error(root, command)
    if error is not None:
        return error
    if len(command) != 2:
        return "Playwright command must be exactly an executable and CLI entrypoint"
    if any(part.startswith("-") for part in command[1:]):
        return "Playwright command options are not trusted in the protected prefix"
    if not Path(command[1]).expanduser().is_absolute():
        return "Playwright CLI entrypoint must be an absolute external path"
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
    environment = untrusted_child_environment(
        home=home,
        extra={"NODE_ENV": "test"},
        drop={"NODE_PATH", "PLAYWRIGHT_BROWSERS_PATH"},
    )
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
        if not isinstance(payload, dict):
            raise ValueError("malformed Playwright reporter payload")
        tests = payload.get("tests")
        if tests is None:
            tests = []
            def visit(suite: object, parents: tuple[str, ...] = ()) -> None:
                if not isinstance(suite, dict):
                    raise ValueError("malformed Playwright suite")
                title = suite.get("title", "")
                next_parents = parents + ((title,) if isinstance(title, str) and title else ())
                specs = suite.get("specs", [])
                if not isinstance(specs, list):
                    raise ValueError("malformed Playwright specs")
                for spec in specs:
                    if not isinstance(spec, dict):
                        raise ValueError("malformed Playwright spec")
                    spec_file = Path(spec["file"])
                    if not spec_file.is_absolute():
                        spec_file = Path(os.path.abspath(root / spec_file))
                    filename = spec_file.resolve().relative_to(root.resolve()).as_posix()
                    title_path = " > ".join(next_parents + (spec["title"],))
                    spec_tests = spec.get("tests", [])
                    if not isinstance(spec_tests, list):
                        raise ValueError("malformed Playwright tests")
                    for item in spec_tests:
                        if not isinstance(item, dict):
                            raise ValueError("malformed Playwright test")
                        results = item.get("results") or [{}]
                        if not isinstance(results, list) or not results or not isinstance(results[-1], dict):
                            raise ValueError("malformed Playwright results")
                        result = results[-1]
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
    command_error = _playwright_command_error(root, prefix)
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
        if obligation.validator_id == "pytest":
            expected_config_digests = {
                pytest_validator_config_digest(root, ref, obligation.artifact_paths)
                for ref in (base_sha, head_sha)
            }
        else:
            expected_config_digests = {
                digest_function(
                    root,
                    ref,
                    obligation.artifact_paths,
                    obligation.code_under_test_paths,
                )
                for ref in (base_sha, head_sha)
            }
    except ValueError as exc:
        return RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.ERROR,
            obligation.validator_config_digest,
            str(exc),
        )
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
    root: Path,
    base_sha: str,
    paths: tuple[PurePosixPath, ...],
    config: RunnerConfig,
) -> tuple[RunnerExecution, tuple[str, ...]]:
    """Run protected-base Jest with the trusted reporter to establish identities."""
    with tempfile.TemporaryDirectory(prefix="pdd-jest-protected-base-") as directory:
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
            return RunnerExecution(
                "protected-base-collection",
                EvidenceOutcome.COLLECTION_ERROR,
                hashlib.sha256(base_sha.encode()).hexdigest(),
                "cannot create protected-base Jest clone",
            ), ()
        return _run_jest(clone, paths, config.timeout_seconds, config)


def _make_vitest_phase_read_only(root: Path) -> None:
    """Protect phase inputs while retaining only declared Vitest cache writes."""
    paths = sorted(root.rglob("*"), key=lambda item: len(item.parts), reverse=True)
    for path in paths:
        relative = path.relative_to(root)
        if ".git" in relative.parts or any(
            name in relative.parts for name in VITEST_CACHE_NAMES
        ):
            continue
        if relative.parts and relative.parts[0] in {
            "node_modules", ".pdd-vitest-toolchain"
        }:
            continue
        if path.is_symlink():
            raise ValueError(f"copied Vitest phase contains symlink: {relative}")
        executable = path.is_file() and bool(path.stat().st_mode & 0o111)
        path.chmod(0o555 if path.is_dir() or executable else 0o444)
    root.chmod(0o555)


def _collect_vitest_at_base(
    root: Path, base_sha: str, paths: tuple[PurePosixPath, ...], config: RunnerConfig
) -> tuple[RunnerExecution, tuple[str, ...]]:
    """Run protected-base Vitest to establish independently derived identities."""
    digest = hashlib.sha256(base_sha.encode()).hexdigest()
    try:
        descriptor = _load_vitest_toolchain_descriptor(root, config)
        with tempfile.TemporaryDirectory(
            prefix="pdd-vitest-protected-base-"
        ) as directory:
            clone = Path(directory) / "repository"
            cloned = subprocess.run(
                ["git", "clone", "-q", "--no-local", "--no-checkout",
                 str(root), str(clone)],
                capture_output=True, text=True, check=False,
            )
            checked_out = cloned.returncode == 0 and subprocess.run(
                ["git", "checkout", "-q", "--detach", base_sha],
                cwd=clone, capture_output=True, check=False,
            ).returncode == 0
            if not checked_out:
                return RunnerExecution(
                    "protected-base-collection", EvidenceOutcome.COLLECTION_ERROR,
                    digest, "cannot create protected-base Vitest clone",
                ), ()
            phase = _prepare_vitest_toolchain(clone, descriptor)
            _make_vitest_phase_read_only(clone)
            return _run_vitest(
                clone, paths, config.timeout_seconds, config,
                command_root=root, phase_toolchain=phase,
            )
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        return RunnerExecution(
            "protected-base-collection", EvidenceOutcome.ERROR, digest,
            f"Vitest phase setup failed: {exc}",
        ), ()


def _run_vitest_at_commit(
    root: Path, commit: str, paths: tuple[PurePosixPath, ...], config: RunnerConfig,
    expected: tuple[str, ...],
) -> tuple[RunnerExecution, tuple[str, ...]]:
    """Execute one fresh immutable exact-commit Vitest phase tree."""
    digest = hashlib.sha256(commit.encode()).hexdigest()
    try:
        descriptor = _load_vitest_toolchain_descriptor(root, config)
        with tempfile.TemporaryDirectory(prefix="pdd-vitest-checked-head-") as directory:
            clone = Path(directory) / "repository"
            cloned = subprocess.run(
                ["git", "clone", "-q", "--no-local", "--no-checkout",
                 str(root), str(clone)],
                capture_output=True, text=True, check=False,
            )
            checked_out = cloned.returncode == 0 and subprocess.run(
                ["git", "checkout", "-q", "--detach", commit], cwd=clone,
                capture_output=True, check=False,
            ).returncode == 0
            if not checked_out:
                return RunnerExecution(
                    "vitest", EvidenceOutcome.ERROR, digest,
                    "cannot create checked-head Vitest clone",
                ), ()
            phase = _prepare_vitest_toolchain(clone, descriptor)
            _make_vitest_phase_read_only(clone)
            return _run_vitest(
                clone, paths, config.timeout_seconds, config, expected,
                command_root=root, phase_toolchain=phase,
            )
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        return RunnerExecution(
            "vitest", EvidenceOutcome.ERROR, digest,
            f"Vitest phase setup failed: {exc}",
        ), ()


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
    # pylint: disable=too-many-locals,too-many-return-statements
    """Run one protected obligation with changed-test self-certification guards."""
    preflight = _obligation_preflight(root, obligation, base_sha, head_sha)
    if preflight is not None:
        return preflight
    if obligation.validator_id == "jest":
        profile = VerificationProfile(
            UnitId(
                "runner-closure", PurePosixPath("closure.prompt"), "javascript"
            ),
            (obligation,),
            obligation.requirement_ids,
            "closure",
        )
        _digest, support_paths = _jest_support_digest(root, head_sha, profile)
        protected_paths = tuple(
            sorted(set(obligation.artifact_paths) | set(support_paths))
        )
        changed = _changed_paths(root, base_sha, head_sha, protected_paths)
        changed.update(_dirty_jest_support(root))
        if changed:
            return RunnerExecution(
                obligation.obligation_id, EvidenceOutcome.QUARANTINED,
                obligation.validator_config_digest,
                "candidate-modified Jest support cannot solely certify itself: "
                + ", ".join(sorted(changed)),
            )
        base_execution, base_ids = _collect_jest_at_base(
            root, base_sha, obligation.artifact_paths, config
        )
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
        head_execution, _head_ids = _run_vitest_at_commit(
            root,
            head_sha,
            obligation.artifact_paths,
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
        "playwright": _dirty_playwright_support,
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
        try:
            descriptor = _load_vitest_toolchain_descriptor(root, config)
            config = replace(config, vitest_toolchain_identity=descriptor.identity)
        except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
            return RunnerExecution(
                obligation.obligation_id,
                EvidenceOutcome.ERROR,
                obligation.validator_config_digest,
                f"Vitest toolchain validation failed: {exc}",
            )
    if obligation.validator_id == "playwright":
        if _playwright_candidate_toolchain(root):
            return RunnerExecution(
                obligation.obligation_id,
                EvidenceOutcome.ERROR,
                obligation.validator_config_digest,
                "candidate node_modules Playwright toolchain is not trusted",
            )
        if config.playwright_command is not None:
            command_error = _playwright_command_error(root, config.playwright_command)
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
    adapter_identities, capture_errors = _capture_adapter_identities(root, config)
    config = replace(config, adapter_identities=adapter_identities)
    executions = tuple(
        RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.ERROR,
            "adapter-identity",
            "configured adapter initial capture failed: "
            + capture_errors[obligation.validator_id],
        )
        if obligation.validator_id in capture_errors
        else run_obligation(
                root,
                obligation,
                base_sha=binding.base_sha,
                head_sha=binding.head_sha,
                config=config,
            )
        for obligation in profile.obligations
    )
    if config.adapter_identities and not capture_errors:
        try:
            _verify_adapter_identities(root, config)
        except (OSError, UnicodeError, ValueError, json.JSONDecodeError):
            executions = tuple(
                RunnerExecution(
                    obligation.obligation_id,
                    EvidenceOutcome.ERROR,
                    execution.command_digest,
                    "configured adapter changed across protocol execution",
                ) if obligation.validator_id in {"jest", "vitest"} else execution
                for obligation, execution in zip(profile.obligations, executions)
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
        adapter_identities=config.adapter_identities,
        playwright_command=config.playwright_command,
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
