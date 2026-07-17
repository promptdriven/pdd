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
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import tomllib
import xml.etree.ElementTree as ET
from contextlib import ExitStack
from dataclasses import dataclass, replace
from datetime import datetime
from enum import Enum
from functools import wraps
from pathlib import Path, PurePosixPath
from types import MappingProxyType
from typing import NoReturn

import pytest
from tree_sitter import Node

from .trust import (
    AttestationBinding,
    AttestationEnvelope,
    AttestationIssuer,
    AttestationRequest,
)
from .isolation import untrusted_child_environment
from .git_io import read_git_blob, read_git_mode, read_git_regular_blob
from .types import (
    AssuranceLevel,
    EvidenceOutcome,
    ObligationEvidence,
    UnitId,
    VerificationObligation,
    VerificationProfile,
)
from .supervisor import (
    InfrastructureFailurePhase,
    ImmutableBindingProof,
    PlaywrightSnapshotAggregate,
    ScopeSetupFailureReason,
    SnapshotBindingProof,
    SupervisorLimits,
    SupervisorTermination,
    TerminationKind,
    _vitest_descriptor_attestation,
    released_runtime_closure_paths,
    run_supervised,
)


TRUSTED_RUNNER_VERSION = "pdd-trusted-runner-v2"
_IN_PROCESS_FRAMEWORK_ADAPTERS = frozenset(
    {"pytest", "jest", "vitest", "playwright"}
)
_VITEST_SUPERVISOR_LIMITS = SupervisorLimits(
    max_memory_bytes=4 * 1024 * 1024 * 1024,
)
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
VITEST_LIFECYCLE_SCHEMA = "pdd-vitest-lifecycle-v2"
VITEST_LIFECYCLE_MAX_MODULES = 64
VITEST_LIFECYCLE_MAX_TESTS = 2048
VITEST_LIFECYCLE_MAX_ERRORS = 2048
VITEST_LIFECYCLE_MAX_STRING = 1024
_VITEST_PROGRESS_PREFIX = b"PDD-VITEST-PROGRESS-V1 "
_VITEST_RESULT_PREFIX = b"PDD-VITEST-RESULT-V1 "
_VITEST_PROGRESS_MAX_RECORDS = 256


class VitestProgressStage(str, Enum):
    """Allowlisted checker-owned progress on the Vitest observation pipe."""

    POST_DROP_PROBES = "post-drop-probes"
    CANDIDATE_EXEC = "candidate-exec"
    COORDINATOR_START = "coordinator-start"
    WORKER_START = "worker-start"
    COLLECTION_COMPLETE = "collection-complete"
    MODULE_COMPLETE = "module-complete"
    RESULT_PUBLISHED = "result-published"


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
    immutable_binding_proofs: tuple[ImmutableBindingProof, ...]
    dependencies: Path
    controller: Path
    descriptor: VitestToolchainDescriptor


PLAYWRIGHT_CONFIG_NAMES = (
    "playwright.config.js", "playwright.config.cjs", "playwright.config.mjs",
    "playwright.config.ts", "playwright.config.cts", "playwright.config.mts",
)
_PLAYWRIGHT_HOST_TEMP_PARENT = Path("/var/tmp")
_PLAYWRIGHT_TEMP_FAILURE_DIGEST = hashlib.sha256(
    b"playwright-temporary-directory"
).hexdigest()
_PLAYWRIGHT_SNAPSHOT_TOOLCHAIN_SCHEMA = "pdd-playwright-snapshot-toolchain-v1"
_PLAYWRIGHT_SNAPSHOT_AGGREGATE_SCHEMA = "pdd-playwright-snapshot-aggregate-v1"

PLAYWRIGHT_TOOLCHAIN_ROLES = {
    "launcher", "entrypoint", "dependencies", "browser_runtime",
    "native_runtime", "lockfile",
}
PLAYWRIGHT_SUPERVISOR_LIMITS = SupervisorLimits(
    max_memory_bytes=2 * 1024 * 1024 * 1024,
    max_virtual_memory_bytes=256 * 1024 * 1024 * 1024,
)


@dataclass(frozen=True)
class PlaywrightToolchainRoles:
    """Validated external paths required by the Playwright process tree."""

    launcher: Path
    entrypoint: Path
    dependencies: Path
    browser_runtime: Path
    native_runtime: tuple[Path, ...]
    lockfile: Path

    @property
    def readable_roots(self) -> tuple[Path, ...]:
        """Return complete non-native roots mounted at their host paths."""
        return (
            self.launcher,
            self.browser_runtime,
            self.lockfile,
            *((self.entrypoint,)
              if not _path_is_relative_to(self.entrypoint, self.dependencies) else ()),
        )

    @property
    def native_bindings(self) -> tuple[tuple[Path, Path], ...]:
        """Bind native files at the exact paths retained by ELF loaders."""
        return tuple(
            (path.resolve(strict=True), path) for path in self.native_runtime
        )


class _PlaywrightTemporaryDirectoryError(Exception):
    """Mark an OSError from a checker-owned Playwright temporary directory."""


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
    playwright_toolchain_manifest: Path | None = None
    playwright_toolchain_identity: str | None = None


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
    for key in (
        "workspace", "projects", "plugins", "globalSetup", "poolOptions",
        "execArgv", "env", "browser",
    ):
        if key in config:
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
        "reporters", "coverage", "poolOptions", "execArgv", "env", "browser",
    ):
        if key in test_config:
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


_PLAYWRIGHT_RESERVED_PACKAGES = frozenset({
    "@playwright/test", "playwright", "playwright-core",
})
_PLAYWRIGHT_EXECUTABLE_SUFFIXES = frozenset(_JAVASCRIPT_SUFFIXES) - {".json"}


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
    scope = _nearest_package_scope(root, ref, found[0])
    if scope is not None:
        try:
            package = json.loads(scope[1].decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ValueError("Playwright config package scope is invalid") from exc
        if not isinstance(package, dict):
            raise ValueError("Playwright config package scope must be an object")
        if package.get("name") in _PLAYWRIGHT_RESERVED_PACKAGES:
            raise ValueError("Playwright config uses a reserved package self-reference")
    return found[0], content


def _playwright_tree_trust_manifests(root: Path, ref: str) -> set[PurePosixPath]:
    """Apply conservative Node trust policy to the complete exact phase tree."""
    manifests: set[PurePosixPath] = set()
    actual_node_modules = next(root.rglob("node_modules"), None)
    if actual_node_modules is not None:
        relative = actual_node_modules.relative_to(root).as_posix()
        raise ValueError(f"candidate node_modules is forbidden in phase tree: {relative}")
    listed = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", ref], cwd=root,
        capture_output=True, text=True, check=True,
    )
    for name in listed.stdout.splitlines():
        path = PurePosixPath(name)
        if "node_modules" in path.parts:
            raise ValueError(
                f"candidate node_modules is forbidden in exact tree: {path}"
            )
        if path.suffix == ".node":
            raise ValueError(f"Playwright native module is forbidden: {path}")
        if path.name != "package.json":
            continue
        regular = read_git_regular_blob(root, ref, path)
        if regular is None:
            raise ValueError(f"Playwright package scope must be a regular file: {path}")
        try:
            package = json.loads(regular.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ValueError(f"Playwright package scope is invalid: {path}") from exc
        if not isinstance(package, dict):
            raise ValueError(f"Playwright package scope must be an object: {path}")
        if package.get("name") in _PLAYWRIGHT_RESERVED_PACKAGES:
            raise ValueError(
                "Playwright closure uses a reserved package self-reference: "
                + path.as_posix()
            )
        manifests.add(path)
    return manifests


def _playwright_static_config(
    path: PurePosixPath, source: bytes, *, commonjs: bool = False,
) -> set[PurePosixPath]:
    """Validate a data-only AST config and return its bound local references."""
    tree = _javascript_parser(path).parse(source)
    if tree.root_node.has_error:
        raise ValueError("Playwright configuration is not valid JavaScript/TypeScript")
    statements = tree.root_node.named_children
    references: set[PurePosixPath] = set()
    config_node: Node | None = None
    define_config = False
    for statement in statements:
        if statement.type == "import_statement":
            imported_node = next(
                (child for child in statement.named_children if child.type == "string"), None
            )
            if imported_node is None:
                raise ValueError("Playwright config import is malformed")
            imported = _javascript_string(source, imported_node)
            if imported == "@playwright/test":
                if not re.fullmatch(
                    r"\s*import\s*\{\s*defineConfig\s*\}\s*from\s*['\"]@playwright/test['\"]\s*;?\s*",
                    _node_text(source, statement),
                ):
                    raise ValueError("only defineConfig may be imported from Playwright")
                define_config = True
            elif len(statement.named_children) == 1:
                references.add(_playwright_local_reference(path, imported, "config import"))
            else:
                raise ValueError("Playwright config imports must be side-effect-only")
        elif statement.type == "export_statement":
            config_node = statement.child_by_field_name("value")
            if config_node is None:
                raise ValueError("Playwright config must export one object")
        elif statement.type == "expression_statement" and (
            path.suffix in {".cjs", ".cts"} or path.suffix == ".js" and commonjs
        ):
            expression = statement.named_children[0] if statement.named_children else None
            if expression is None or expression.type != "assignment_expression":
                raise ValueError("Playwright CommonJS config must assign module.exports")
            left = expression.child_by_field_name("left")
            if left is None or _node_text(source, left) != "module.exports":
                raise ValueError("Playwright CommonJS config must assign module.exports")
            config_node = expression.child_by_field_name("right")
        else:
            raise ValueError("Playwright configuration must be one declarative object")
    if config_node is not None and config_node.type == "call_expression":
        function = config_node.child_by_field_name("function")
        arguments = config_node.child_by_field_name("arguments")
        values = arguments.named_children if arguments is not None else []
        if (
            not define_config or function is None
            or _node_text(source, function) != "defineConfig"
            or len(values) != 1 or values[0].type != "object"
        ):
            raise ValueError("Playwright configuration must be one declarative defineConfig wrapper")
        config_node = values[0]
    if config_node is None or config_node.type != "object":
        raise ValueError("Playwright configuration must be a declarative object literal")
    try:
        references.update(_validate_playwright_config_object(path, source, config_node))
    except ValueError as exc:
        raise ValueError(f"Playwright configuration is unsupported: {exc}") from exc
    return references


def _playwright_config_is_commonjs(
    root: Path, ref: str, path: PurePosixPath,
) -> bool:
    """Return the committed Node module mode for one Playwright config file."""
    if path.suffix in {".cjs", ".cts"}:
        return True
    if path.suffix in {".mjs", ".mts"}:
        return False
    if path.suffix != ".js":
        return False
    scope = _nearest_package_scope(root, ref, path)
    if scope is None:
        return True
    try:
        package = json.loads(scope[1].decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError("Playwright config package scope is invalid") from exc
    if not isinstance(package, dict):
        raise ValueError("Playwright config package scope must be an object")
    return package.get("type") != "module"


def _node_text(source: bytes, node: Node) -> str:
    """Return the exact UTF-8 text covered by an AST node."""
    return source[node.start_byte:node.end_byte].decode("utf-8")


def _javascript_parser(path: PurePosixPath):
    """Select the grammar matching JavaScript, JSX, TypeScript, or TSX."""
    if path.suffix == ".tsx":
        return _vitest_parser("tsx")
    if path.suffix in {".ts", ".cts", ".mts"}:
        return _vitest_parser("typescript")
    return _vitest_parser("javascript")


def _javascript_string(source: bytes, node: Node) -> str:
    """Decode one JavaScript string literal after AST validation."""
    if node.type != "string":
        raise ValueError("a static JavaScript string is required")
    try:
        value = ast.literal_eval(_node_text(source, node))
    except (SyntaxError, ValueError) as exc:
        raise ValueError("invalid JavaScript string literal") from exc
    if not isinstance(value, str):
        raise ValueError("a static JavaScript string is required")
    return value


def _playwright_local_reference(path: PurePosixPath, value: str, label: str) -> PurePosixPath:
    local = _jest_local_path(value)
    if local is None:
        raise ValueError(f"Playwright {label} is not a static local path")
    normalized = _normalize_repo_relative_path(path.parent / local)
    if normalized is None:
        raise ValueError(f"Playwright {label} escapes repository")
    return normalized


def _validate_playwright_config_object(
    path: PurePosixPath, source: bytes, config: Node
) -> set[PurePosixPath]:
    """Apply the explicit root-property allowlist to a parsed config object."""
    allowed_data = {
        "timeout", "fullyParallel", "forbidOnly", "outputDir",
        "testDir", "testMatch", "testIgnore", "preserveOutput", "quiet",
        "captureGitInfo", "metadata",
    }
    executable = {"globalSetup", "globalTeardown", "reporter"}
    forbidden = {
        "grep", "grepInvert", "shard", "retries", "workers", "repeatEach",
        "webServer", "storageState", "projects", "dependencies",
        "snapshotPathTemplate", "executablePath", "use",
        "updateSnapshots", "updateSourceMethod",
    }
    references: set[PurePosixPath] = set()
    for pair in config.named_children:
        if pair.type != "pair":
            raise ValueError("Playwright config methods and spreads are unsupported")
        key_node = pair.child_by_field_name("key")
        value_node = pair.child_by_field_name("value")
        if key_node is None or value_node is None or key_node.type == "computed_property_name":
            raise ValueError("Playwright config keys must be static")
        key = (_javascript_string(source, key_node) if key_node.type == "string"
               else _node_text(source, key_node))
        if key in forbidden:
            raise ValueError(f"Playwright config key {key} is unsupported")
        if key in executable:
            value = _javascript_string(source, value_node)
            references.add(_playwright_local_reference(path, value, key))
        elif key in allowed_data:
            _validate_playwright_data_value(source, value_node)
        else:
            raise ValueError(f"Playwright config key {key} is unsupported")
    return references


def _validate_playwright_data_value(source: bytes, node: Node) -> None:
    """Accept only recursively inert literals inside admitted data properties."""
    if node.type in {"string", "number", "true", "false", "null", "undefined"}:
        return
    if node.type in {"array", "object"}:
        for child in node.named_children:
            value = child.child_by_field_name("value") if child.type == "pair" else child
            if child.type == "pair":
                key = child.child_by_field_name("key")
                if key is None or key.type == "computed_property_name":
                    raise ValueError("Playwright config data keys must be static")
            if value is None:
                raise ValueError("Playwright config data must be literal")
            _validate_playwright_data_value(source, value)
        return
    raise ValueError("Playwright config data must be literal")


_PLAYWRIGHT_UNBOUND_PATH_KEYS = frozenset({
    "path", "pathTemplate", "snapshotPathTemplate", "storageState",
    "executablePath", "cert", "certPath", "har", "script", "style",
})

# These values configure the browser context; none can select an executable or
# a browser channel.  New Playwright options must be reviewed before admission.
_PLAYWRIGHT_USE_OPTIONS = frozenset({
    "acceptDownloads", "baseURL", "colorScheme", "extraHTTPHeaders", "geolocation",
    "hasTouch", "httpCredentials", "ignoreHTTPSErrors", "isMobile", "locale",
    "permissions", "proxy", "reducedMotion", "screen", "timezoneId", "userAgent",
    "video", "viewport",
})
_PLAYWRIGHT_EXECUTABLE_OPTIONS = frozenset({
    "browserName", "channel", "connectOptions", "executablePath", "launchOptions",
})


def _validate_playwright_use_value(source: bytes, node: Node, *, top_level: bool = True) -> None:
    """Accept only inert ``test.use`` data with no path-bearing capability."""
    if node.type in {"string", "number", "true", "false", "null", "undefined"}:
        return
    if node.type not in {"array", "object"}:
        raise ValueError("Playwright test.use options must be literal")
    for child in node.named_children:
        value = child.child_by_field_name("value") if child.type == "pair" else child
        if child.type == "pair":
            key = child.child_by_field_name("key")
            if key is None or key.type == "computed_property_name":
                raise ValueError("Playwright test.use keys must be static")
            label = (_javascript_string(source, key) if key.type == "string"
                     else _node_text(source, key))
            if label in _PLAYWRIGHT_UNBOUND_PATH_KEYS:
                raise ValueError(f"Playwright test.use path option {label} is unsupported")
            if label in _PLAYWRIGHT_EXECUTABLE_OPTIONS:
                raise ValueError(
                    f"Playwright test.use executable option {label} is unsupported"
                )
            if top_level and label not in _PLAYWRIGHT_USE_OPTIONS:
                raise ValueError(f"Playwright test.use option {label} is unsupported")
        if value is None:
            raise ValueError("Playwright test.use options must be literal")
        _validate_playwright_use_value(source, value, top_level=False)


def _playwright_support_closure(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...],
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
) -> tuple[tuple[PurePosixPath, bytes], ...]:
    # pylint: disable=too-many-locals
    """Bind config, local support, and test imports without executing them."""
    config_path, config_source = _playwright_config(root, ref)
    config_mode = read_git_mode(root, ref, config_path)
    if config_mode not in {"100644", "100755"}:
        raise ValueError("Playwright config must be a regular non-symlink file")
    paths = {config_path}
    scope = _nearest_package_scope(root, ref, config_path)
    if scope is not None:
        paths.add(scope[0] / "package.json")
    product_paths = frozenset(code_under_test_paths)
    all_owners = frozenset(test_paths)
    pending = [
        (item, all_owners, True) for item in _playwright_static_config(
            config_path,
            config_source,
            commonjs=_playwright_config_is_commonjs(root, ref, config_path),
        )
    ] + [(item, frozenset({item}), True) for item in test_paths]
    visited: dict[
        tuple[PurePosixPath, bool], frozenset[PurePosixPath]
    ] = {}
    snapshot_owners: set[PurePosixPath] = set()
    while pending:
        path, owners, node_executable = pending.pop()
        visit_key = (path, node_executable)
        known_owners = visited.get(visit_key, frozenset())
        new_owners = owners - known_owners
        if not new_owners:
            continue
        visited[visit_key] = known_owners | owners
        path, source = _read_javascript_support_blob(root, ref, path)
        if source is None:
            raise ValueError(f"Playwright local support path is missing: {path.as_posix()}")
        if node_executable and path in product_paths:
            raise ValueError(
                "Playwright Node closure imports declared product: "
                + path.as_posix()
            )
        mode = read_git_mode(root, ref, path)
        if mode not in {"100644", "100755"}:
            raise ValueError(
                f"Playwright closure member must be a regular non-symlink file: {path}"
            )
        paths.add(path)
        if not node_executable or path.suffix == ".json":
            continue
        if path.suffix not in _PLAYWRIGHT_EXECUTABLE_SUFFIXES:
            raise ValueError(
                f"Playwright local import has unsupported executable extension: {path}"
            )
        if path.suffix in _PLAYWRIGHT_EXECUTABLE_SUFFIXES:
            imports, bare_imports, has_snapshot, resources = _playwright_source_syntax(
                path, source
            )
            for imported in imports:
                normalized = _normalize_repo_relative_path(
                    path.parent / PurePosixPath(imported)
                )
                if normalized is None:
                    raise ValueError("Playwright import escapes the repository")
                resolved, imported_source = _read_javascript_support_blob(root, ref, normalized)
                if imported_source is None:
                    raise ValueError(f"Playwright local support path is missing: {resolved}")
                pending.append((resolved, owners, True))
            for resource in resources:
                normalized = _normalize_repo_relative_path(PurePosixPath(resource))
                if normalized is None:
                    raise ValueError("Playwright runtime resource escapes the repository")
                resolved, resource_source = _read_javascript_support_blob(
                    root, ref, normalized
                )
                if resource_source is None:
                    raise ValueError(
                        f"Playwright runtime resource path is missing: {resolved}"
                    )
                if resolved not in product_paths:
                    pending.append((resolved, owners, False))
            mapped_bare: set[PurePosixPath] = set()
            package_manifests: set[PurePosixPath] = set()
            unbound_bare: set[str] = set()
            for imported in bare_imports - {"@playwright/test"}:
                mapped = _package_mapping_target(root, ref, path, imported)
                if mapped is None:
                    unbound_bare.add(imported)
                    continue
                scope = _nearest_package_scope(root, ref, path)
                assert scope is not None
                package_manifests.add(scope[0] / "package.json")
                mapped_bare.add(mapped)
            if unbound_bare:
                raise ValueError(
                    "Playwright bare package imports are not bound by this adapter: "
                    + ", ".join(sorted(unbound_bare))
                )
            paths.update(package_manifests)
            for mapped in mapped_bare:
                pending.append((mapped, owners, True))
            if has_snapshot:
                snapshot_owners.update(owners)
    paths.update(_playwright_tree_trust_manifests(root, ref))
    for owner in snapshot_owners:
        snapshot_prefix = PurePosixPath(f"{owner.as_posix()}-snapshots")
        listed = subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", ref, "--", snapshot_prefix.as_posix()],
            cwd=root, capture_output=True, text=True, check=True,
        )
        for name in listed.stdout.splitlines():
            snapshot_path = PurePosixPath(name)
            if read_git_mode(root, ref, snapshot_path) == "120000":
                raise ValueError(
                    f"Playwright closure member must not be a symlink: {snapshot_path}"
                )
            snapshot = read_git_blob(root, ref, snapshot_path)
            if snapshot is not None:
                paths.add(snapshot_path)
    return tuple(
        (path, read_git_blob(root, ref, path)) for path in sorted(paths)
        if read_git_blob(root, ref, path) is not None
    )


def _playwright_source_syntax(
    path: PurePosixPath, source: bytes
) -> tuple[set[str], set[str], bool, set[str]]:
    # pylint: disable=too-many-nested-blocks
    """Derive module/snapshot edges under an AST runtime-capability allowlist."""
    tree = _javascript_parser(path).parse(source)
    if tree.root_node.has_error:
        raise ValueError("Playwright source is not valid JavaScript/TypeScript syntax")
    local: set[str] = set()
    bare: set[str] = set()
    resources: set[str] = set()
    snapshot = False
    assertion_calls = {
        "toBe", "toEqual", "toStrictEqual", "toBeTruthy", "toBeFalsy",
        "toContain", "toMatch", "toHaveTitle", "toHaveURL", "toBeVisible",
        "toBeHidden", "toHaveText", "toContainText", "toHaveValue",
        "toHaveScreenshot", "toMatchSnapshot", "toBeEnabled", "toBeDisabled",
        "toBeChecked", "toHaveAttribute", "toHaveClass", "toHaveCount",
        "toHaveCSS", "toHaveJSProperty", "toHaveId", "toHaveAccessibleName",
    }
    test_calls = {
        "use", "beforeEach", "afterEach", "beforeAll", "afterAll", "step",
        "configure",
    }
    page_calls = {
        "goto", "locator", "getByRole", "getByText", "getByTestId",
        "waitForSelector", "addInitScript", "addScriptTag", "addStyleTag",
        "routeFromHAR", "mainFrame",
    }
    locator_calls = {
        "click", "fill", "filter", "first", "last", "nth", "hover",
        "waitFor", "press", "selectOption", "uncheck", "locator",
        "getByRole", "getByText", "getByTestId",
    }
    frame_calls = {
        "goto", "locator", "getByRole", "getByText", "getByTestId",
        "waitForSelector",
    }
    allowed_calls = {
        "test", "describe", "expect", "check",
        "includes", "append",
    } | assertion_calls | test_calls | page_calls | locator_calls | frame_calls
    resource_calls = {"addInitScript", "addScriptTag", "addStyleTag", "routeFromHAR"}
    reflective_roots = {"Object", "Reflect", "Proxy", "Function"}
    local_callables: set[str] = set()
    receiver_bindings: dict[str, str] = {"page": "page", "frame": "frame"}
    playwright_bindings: dict[str, str] = {}

    def imported_playwright_name(specifier: Node) -> tuple[str, str]:
        """Return the local and exported names for one static import specifier."""
        names = [child for child in specifier.named_children if child.type == "identifier"]
        if not names:
            raise ValueError("Playwright imports must use named bindings")
        exported = _node_text(source, names[0])
        local_name = _node_text(source, names[-1])
        if exported not in {"test", "expect"}:
            raise ValueError(f"Playwright import {exported} is unsupported")
        return local_name, exported

    def is_bound_test(name: str) -> bool:
        return playwright_bindings.get(name) == "test"

    def is_bound_expect(node: Node | None) -> bool:
        if node is None:
            return False
        if node.type == "identifier":
            return playwright_bindings.get(_node_text(source, node)) == "expect"
        if node.type == "call_expression":
            return is_bound_expect(node.child_by_field_name("function"))
        if node.type in {"parenthesized_expression", "await_expression"}:
            return any(is_bound_expect(child) for child in node.named_children)
        return False

    def inferred_receiver(node: Node | None) -> str | None:
        """Infer a browser receiver kind from a structured expression."""
        if node is None:
            return None
        if node.type == "identifier":
            return receiver_bindings.get(_node_text(source, node))
        if node.type in {"parenthesized_expression", "await_expression"}:
            return next(
                (kind for child in node.named_children
                 if (kind := inferred_receiver(child)) is not None),
                None,
            )
        if node.type != "call_expression":
            return None
        function = node.child_by_field_name("function")
        if function is None or function.type != "member_expression":
            return None
        obj = function.child_by_field_name("object")
        prop = function.child_by_field_name("property")
        method = _node_text(source, prop) if prop is not None else ""
        owner = inferred_receiver(obj)
        if method == "mainFrame" and owner == "page":
            return "frame"
        if method in {"locator", "getByRole", "getByText", "getByTestId"} and owner in {
            "page", "frame", "locator",
        }:
            return "locator"
        if method in {"filter", "first", "last", "nth"} and owner == "locator":
            return "locator"
        return None

    def bind_pattern(pattern: Node | None, value: Node | None = None) -> bool:
        """Propagate receiver kinds through identifiers and object patterns."""
        if pattern is None:
            return False
        if pattern.type == "identifier":
            kind = inferred_receiver(value)
            name = _node_text(source, pattern)
            if kind is not None and receiver_bindings.get(name) != kind:
                receiver_bindings[name] = kind
                return True
            return False
        changed = False
        if pattern.type in {"object_pattern", "object"}:
            values = {}
            if value is not None and value.type == "object":
                for pair in value.named_children:
                    key = pair.child_by_field_name("key")
                    item = pair.child_by_field_name("value")
                    if key is not None:
                        values[_node_text(source, key)] = item
            for pair in pattern.named_children:
                key = pair.child_by_field_name("key")
                target = pair.child_by_field_name("value")
                if key is None:
                    key = pair
                    target = pair
                key_text = _node_text(source, key)
                seed = values.get(key_text)
                if seed is None and key_text in {"page", "frame"}:
                    receiver_bindings.setdefault(key_text, key_text)
                    if target is not None and target.type == "identifier":
                        alias = _node_text(source, target)
                        if receiver_bindings.get(alias) != key_text:
                            receiver_bindings[alias] = key_text
                            changed = True
                else:
                    changed |= bind_pattern(target, seed)
        return changed

    # Resolve import provenance before examining declarations.  Tree traversal
    # order is not lexical, so a one-pass walk can miss a preceding import.
    pending_imports = [tree.root_node]
    while pending_imports:
        candidate = pending_imports.pop()
        pending_imports.extend(candidate.named_children)
        if candidate.type != "import_statement":
            continue
        source_node = candidate.child_by_field_name("source")
        if source_node is None or _javascript_string(source, source_node) != "@playwright/test":
            continue
        clause = next(
            (child for child in candidate.named_children if child.type == "import_clause"), None
        )
        named = next(
            (child for child in (clause.named_children if clause else ())
             if child.type == "named_imports"), None,
        )
        if named is None:
            raise ValueError("Playwright imports must use named bindings")
        for specifier in named.named_children:
            local_name, exported = imported_playwright_name(specifier)
            if local_name in playwright_bindings:
                raise ValueError(f"duplicate Playwright binding {local_name}")
            playwright_bindings[local_name] = exported

    discovery = [tree.root_node]
    declarations: list[Node] = []
    while discovery:
        candidate = discovery.pop()
        discovery.extend(candidate.named_children)
        if candidate.type in {"function_declaration", "variable_declarator"}:
            name_node = candidate.child_by_field_name("name")
            value_node = candidate.child_by_field_name("value")
            if name_node is not None and name_node.type == "identifier" and _node_text(
                source, name_node
            ) in playwright_bindings:
                raise ValueError("Playwright imported binding is shadowed")
            if (
                candidate.type == "function_declaration"
                and name_node is not None and name_node.type == "identifier"
            ):
                local_callables.add(_node_text(source, name_node))
            if candidate.type == "variable_declarator":
                declarations.append(candidate)
                if (
                    value_node is not None
                    and _node_text(source, value_node) in {"require", "process", "globalThis"}
                ):
                    raise ValueError(
                        "dynamic or aliased Playwright module loading is not supported"
                    )
                if (
                    name_node is not None and name_node.type == "identifier"
                    and value_node is not None
                    and value_node.type in {"arrow_function", "function_expression"}
                ):
                    local_callables.add(_node_text(source, name_node))
        if candidate.type == "object_pattern":
            bind_pattern(candidate)
        if candidate.type in {"formal_parameters", "required_parameter", "optional_parameter"}:
            for parameter in candidate.named_children:
                if parameter.type == "identifier" and _node_text(source, parameter) in playwright_bindings:
                    raise ValueError("Playwright imported binding is shadowed")
    for _unused in range(len(declarations) + 1):
        changed = False
        for declaration in declarations:
            changed |= bind_pattern(
                declaration.child_by_field_name("name"),
                declaration.child_by_field_name("value"),
            )
        if not changed:
            break
    stack = [tree.root_node]
    while stack:
        node = stack.pop()
        stack.extend(node.named_children)
        if node.type in {"import_statement", "export_statement"}:
            source_node = node.child_by_field_name("source")
            if source_node is None and node.type == "import_statement":
                require_clause = next(
                    (
                        child for child in node.named_children
                        if child.type == "import_require_clause"
                    ),
                    None,
                )
                if require_clause is not None:
                    source_node = require_clause.child_by_field_name("source")
            if source_node is None and node.type == "import_statement":
                source_node = next(
                    (child for child in node.named_children if child.type == "string"), None
                )
            if source_node is not None:
                imported = _javascript_string(source, source_node)
                (local if imported.startswith(("./", "../")) else bare).add(imported)
        if node.type == "subscript_expression":
            label = "module loading" if "require" in _node_text(source, node) else "runtime resource"
            raise ValueError(f"Playwright {label} uses dynamic property access")
        if node.type == "identifier" and _node_text(source, node) in {
            "Reflect", "eval", "Function", "process", "globalThis", "global",
        }:
            raise ValueError("Playwright runtime resource access violates the runtime capability allowlist")
        if node.type == "identifier" and _node_text(source, node) in {
            "exec", "execSync", "execFile", "execFileSync", "spawn", "spawnSync",
            "fork", "readFile", "readFileSync", "writeFile", "writeFileSync",
        }:
            raise ValueError("Playwright runtime resource access violates the runtime capability allowlist")
        if node.type == "identifier" and _node_text(source, node) == "require":
            parent = node.parent
            if parent is None or parent.type != "call_expression" or parent.child_by_field_name("function") != node:
                raise ValueError("dynamic or aliased Playwright module loading is not supported")
        if node.type == "call_expression":
            function = node.child_by_field_name("function")
            arguments = node.child_by_field_name("arguments")
            if function is None:
                continue
            function_text = _node_text(source, function)
            if function.type == "import" or function_text == "require":
                values = arguments.named_children if arguments is not None else []
                if len(values) != 1 or values[0].type != "string":
                    raise ValueError("dynamic or aliased Playwright module loading is not supported")
                imported = _javascript_string(source, values[0])
                (local if imported.startswith(("./", "../")) else bare).add(imported)
            elif function.type == "identifier" and function_text in {
                "require", "eval", "Function", "createRequire",
            }:
                raise ValueError("dynamic or aliased Playwright module loading is not supported")
            elif function.type == "member_expression":
                prop = function.child_by_field_name("property")
                obj = function.child_by_field_name("object")
                name = _node_text(source, prop) if prop is not None else ""
                receiver = _node_text(source, obj) if obj is not None else ""
                root_name = _node_text(source, obj).split(".", 1)[0] if obj is not None else ""
                if name in {"require", "createRequire"}:
                    raise ValueError(
                        "dynamic or aliased Playwright module loading is not supported"
                    )
                if name in {
                    "getBuiltinModule", "exec", "execSync", "execFile", "execFileSync",
                    "spawn", "spawnSync", "fork", "readFile", "readFileSync",
                    "writeFile", "writeFileSync",
                } or root_name == "process":
                    raise ValueError(
                        "Playwright runtime resource access violates the runtime capability schema"
                    )
                if root_name in reflective_roots or name not in allowed_calls:
                    raise ValueError(
                        "Playwright call violates the positive runtime capability schema"
                    )
                if name in test_calls and not is_bound_test(root_name):
                    raise ValueError("Playwright test capability is not bound to an imported test")
                if name == "use":
                    values = arguments.named_children if arguments is not None else []
                    if len(values) != 1 or values[0].type != "object":
                        raise ValueError("Playwright test.use options must be one literal object")
                    _validate_playwright_use_value(source, values[0])
                if name == "configure":
                    values = arguments.named_children if arguments is not None else []
                    if len(values) != 1 or values[0].type != "object":
                        raise ValueError("Playwright suite configuration must be literal")
                    for pair in values[0].named_children:
                        key = pair.child_by_field_name("key")
                        value = pair.child_by_field_name("value")
                        label = _node_text(source, key).strip("'\"") if key else ""
                        if label == "retries":
                            raise ValueError("Playwright suite retries are unsupported")
                        if label != "mode" or value is None or value.type != "string":
                            raise ValueError(
                                "Playwright suite configuration only supports literal mode"
                            )
                if name in assertion_calls and not is_bound_expect(obj):
                    raise ValueError(
                        "Playwright assertion capability is not bound to an imported expect"
                    )
                receiver_methods = {
                    "locator": locator_calls,
                    "frame": frame_calls,
                    "page": page_calls,
                }
                receiver_kind = inferred_receiver(obj) or next(
                    (kind for kind, methods in receiver_methods.items()
                     if kind in receiver.lower()
                     or (kind == "locator" and any(
                         token in receiver for token in
                         ("getBy", ".filter(", ".first(", ".last(", ".nth(")
                     ))),
                    None,
                )
                browser_capabilities = page_calls | locator_calls | frame_calls
                if name in browser_capabilities and (
                    receiver_kind is None
                    or name not in receiver_methods[receiver_kind]
                ):
                    raise ValueError(
                        "Playwright browser capability is not valid for this receiver"
                    )
                if name in resource_calls:
                    values = arguments.named_children if arguments is not None else []
                    resource_node = values[0] if values else None
                    if resource_node is not None and resource_node.type == "object":
                        pairs = resource_node.named_children
                        if len(pairs) != 1 or pairs[0].type != "pair":
                            raise ValueError(
                                "Playwright runtime resource object schema requires one path property"
                            )
                        key = pairs[0].child_by_field_name("key")
                        if (
                            key is None
                            or key.type == "computed_property_name"
                            or _node_text(source, key).strip("'\"") != "path"
                        ):
                            raise ValueError(
                                "Playwright runtime resource object schema requires one static path property"
                            )
                        resource_node = pairs[0].child_by_field_name("value")
                    if resource_node is None or resource_node.type != "string":
                        raise ValueError("Playwright runtime resource path must be static")
                    value = _javascript_string(source, resource_node)
                    if not value.startswith(("./", "../")):
                        raise ValueError("Playwright runtime resource must be a local path")
                    resources.add(value)
            elif function.type == "identifier" and function_text in {
                "exec", "execSync", "execFile", "execFileSync", "spawn",
                "spawnSync", "fork", "readFile", "readFileSync", "writeFile",
                "writeFileSync",
            }:
                raise ValueError(
                    "Playwright runtime resource access violates the runtime capability schema"
                )
            elif (
                function.type == "identifier"
                and (
                    (function_text == "test" and not is_bound_test(function_text))
                    or (function_text == "expect" and playwright_bindings.get(function_text) != "expect")
                    or (
                        function_text not in allowed_calls
                        and function_text not in local_callables
                        and not is_bound_test(function_text)
                        and playwright_bindings.get(function_text) != "expect"
                    )
                )
            ):
                raise ValueError(
                    "Playwright call violates the positive runtime capability schema"
                )
        if node.type == "member_expression":
            prop = node.child_by_field_name("property")
            if prop is None:
                continue
            name = _node_text(source, prop)
            if name in {"toHaveScreenshot", "toMatchSnapshot"}:
                snapshot = True
            if name in {"only", "skip", "fixme", "slow"}:
                obj = node.child_by_field_name("object")
                if obj is not None and _node_text(source, obj) in {"test", "describe"}:
                    raise ValueError("Playwright focused, skipped, fixme, or slow tests are ambiguous")
            if name in {
                "createRequire",
            }:
                raise ValueError("dynamic or aliased Playwright module loading is not supported")
            if name in {
                "require", "getBuiltinModule", "exec", "execSync",
                "execFile", "execFileSync", "spawn", "spawnSync", "fork",
                "readFile", "readFileSync", "writeFile", "writeFileSync",
            }:
                if name == "require":
                    raise ValueError("dynamic or aliased Playwright module loading is not supported")
                raise ValueError("Playwright runtime resource access violates the runtime capability allowlist")
        if node.type == "string" and _javascript_string(source, node).startswith("node:"):
            raise ValueError("Playwright runtime resource access violates the runtime capability allowlist")
    return local, bare, snapshot, resources


def playwright_validator_config_digest(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...],
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
) -> str:
    """Hash Playwright config and every bound local executable dependency."""
    digest = hashlib.sha256()
    for path, content in _playwright_support_closure(
        root, ref, test_paths, code_under_test_paths
    ):
        digest.update(
            path.as_posix().encode() + b"\0" + read_git_mode(root, ref, path).encode()
            + b"\0" + content + b"\0"
        )
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
    product = tuple(
        path for obligation in profile.obligations
        if obligation.validator_id == "playwright"
        for path in obligation.code_under_test_paths
    )
    try:
        closure = _playwright_support_closure(root, ref, tests, product)
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
    writable_roots: tuple[Path, ...], readable_roots: tuple[Path, ...] = (),
    result_fifo: Path | None = None, result_fd: int = 198,
) -> tuple[subprocess.CompletedProcess[str], bool]:
    """Run an untrusted command in a networkless sandbox and reap its group."""
    return run_supervised(command, cwd=cwd, timeout=timeout, env=env,
                          writable_roots=writable_roots,
                          readable_roots=readable_roots,
                          result_fifo=result_fifo, result_fd=result_fd)


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
        "assurance": profile.assurance.value,
        "pytest_command": [
            "<measured-python-runtime>",
            "-P",
            "<trusted-worker-imports-pytest-before-candidate-root>",
            "import pytest",
            "pytest.main",
            "-q",
            *PYTEST_PROTECTED_FLAGS,
            "<protected-node-id>",
            "--junitxml=<checker-owned-observation-channel>",
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
            "--outputFile=<checker-owned-observation-channel>",
        ],
        "vitest_environment": {"NODE_ENV": "test"},
        "playwright_command": ["<role:launcher>", "<role:entrypoint>", "test", "<protected-test-path>", "--config=<protected-config-path>", "--reporter=<checker-owned-observation-channel>"],
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


def _vitest_member_payload(member: VitestToolchainMember) -> dict[str, object]:
    """Return the canonical descriptor-attestation shape for one member."""
    return {
        "role": member.role,
        "path": member.relative_path.as_posix(),
        "kind": member.kind,
        "mode": member.mode,
        "digest": member.content_digest,
        "target": member.link_target,
    }


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
    _attestation, identity = _vitest_descriptor_attestation(
        tuple(_vitest_member_payload(member) for member in members),
        native_runtime,
        linux_wasm_trap_handler_disabled=sys.platform.startswith("linux"),
    )
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


def _vitest_immutable_binding_proofs(
    native_runtime: tuple[Path, ...], descriptor: VitestToolchainDescriptor,
) -> tuple[ImmutableBindingProof, ...]:
    """Bind copied native files to their captured descriptor identities."""
    members = _vitest_role_members(descriptor, "native_runtime")
    if len(native_runtime) != len(members):
        raise ValueError("Vitest copied native runtime proof is incomplete")
    attestation, identity = _vitest_descriptor_attestation(
        tuple(_vitest_member_payload(member) for member in descriptor.members),
        descriptor.native_runtime,
        linux_wasm_trap_handler_disabled=sys.platform.startswith("linux"),
    )
    if identity != descriptor.identity:
        raise ValueError("Vitest native runtime descriptor identity mismatch")
    proofs = []
    for index, (copied, protected, member) in enumerate(zip(
        native_runtime, descriptor.native_runtime, members, strict=True
    )):
        if member.kind != "file" or member.content_digest is None:
            raise ValueError("Vitest native runtime descriptor member is malformed")
        proofs.append(ImmutableBindingProof(
            copied_source=copied,
            protected_source=protected,
            destination=protected,
            descriptor_attestation=attestation,
            descriptor_identity=identity,
            member_role="native_runtime",
            member_path=str(index),
            collision_category="vitest_inferred_runtime",
        ))
    return tuple(proofs)


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
    if phase.immutable_binding_proofs != _vitest_immutable_binding_proofs(
        phase.native_runtime, descriptor
    ):
        raise ValueError("Vitest copied native runtime proof mismatch")
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
        immutable_binding_proofs=_vitest_immutable_binding_proofs(
            tuple(native_runtime), descriptor
        ),
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


def _snapshot_link_is_contained(relative: PurePosixPath, target: str) -> bool:
    """Accept only a relative link whose lexical target remains in its root."""
    if PurePosixPath(target).is_absolute():
        return False
    parts: list[str] = []
    for part in (*relative.parent.parts, *PurePosixPath(target).parts):
        if part in {"", "."}:
            continue
        if part == "..":
            if not parts:
                return False
            parts.pop()
        else:
            parts.append(part)
    return True


def _snapshot_binding_proof(source: Path, destination: Path) -> SnapshotBindingProof:
    """Capture a complete no-follow regular-file tree for helper-owned staging."""
    root = source.resolve(strict=True)
    members: list[dict[str, object]] = []

    def capture(path: Path, relative: PurePosixPath) -> None:
        metadata = path.lstat()
        mode = stat.S_IMODE(metadata.st_mode)
        member: dict[str, object] = {
            "path": relative.as_posix(), "mode": mode,
            "digest": None, "size": None, "target": None,
        }
        if stat.S_ISDIR(metadata.st_mode):
            member["kind"] = "directory"
            members.append(member)
            for child in sorted(path.iterdir(), key=lambda item: item.name):
                capture(child, relative / child.name)
        elif stat.S_ISREG(metadata.st_mode):
            member["kind"] = "file"
            member["size"] = metadata.st_size
            descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0))
            try:
                digest = hashlib.sha256()
                while chunk := os.read(descriptor, 1024 * 1024):
                    digest.update(chunk)
                member["digest"] = digest.hexdigest()
            finally:
                os.close(descriptor)
            members.append(member)
        elif stat.S_ISLNK(metadata.st_mode):
            target = os.readlink(path)
            if not _snapshot_link_is_contained(relative, target):
                raise ValueError("Playwright snapshot symlink escapes its declared root")
            member["kind"] = "symlink"
            member["target"] = target
            members.append(member)
        else:
            raise ValueError("Playwright snapshot contains an unsupported special file")

    capture(root, PurePosixPath("."))
    members.sort(key=lambda member: str(member["path"]))
    attestation = json.dumps({
        "schema": "pdd-snapshot-binding-v1", "source": str(root),
        "destination": str(destination), "members": members,
    }, sort_keys=True, separators=(",", ":"))
    return SnapshotBindingProof(root, destination, attestation)


def _playwright_snapshot_binding_proofs(
    reporter: Path,
    roles: PlaywrightToolchainRoles,
    launcher_destination: Path,
    dependency_destination: Path,
    native_bindings: tuple[tuple[Path, Path], ...],
) -> tuple[SnapshotBindingProof, ...]:
    """Bind every Playwright-owned executable and tree to a helper snapshot."""
    try:
        roles.entrypoint.relative_to(roles.dependencies)
        entrypoint_pair: tuple[tuple[Path, Path], ...] = ()
    except ValueError:
        entrypoint_pair = ((roles.entrypoint, roles.entrypoint),)
    pairs = (
        (reporter, reporter), (roles.launcher, launcher_destination),
        (roles.browser_runtime, roles.browser_runtime), (roles.lockfile, roles.lockfile),
        (roles.dependencies, dependency_destination),
        *entrypoint_pair,
        *native_bindings,
    )
    return tuple(_snapshot_binding_proof(source, destination) for source, destination in pairs)


def _snapshot_binding_members(proof: SnapshotBindingProof) -> list[dict[str, object]]:
    """Return the canonical member set from one locally constructed snapshot."""
    # Exact built-in containers keep the role identity serialization unambiguous.
    # pylint: disable=unidiomatic-typecheck
    try:
        payload = json.loads(proof.attestation)
        if (
            type(payload) is not dict
            or set(payload) != {"schema", "source", "destination", "members"}
            or payload["schema"] != "pdd-snapshot-binding-v1"
            or payload["source"] != str(proof.source)
            or payload["destination"] != str(proof.destination)
            or proof.attestation != json.dumps(
                payload, sort_keys=True, separators=(",", ":")
            )
            or type(payload["members"]) is not list
        ):
            raise ValueError("invalid Playwright snapshot attestation")
        return payload["members"]
    except (TypeError, ValueError, json.JSONDecodeError) as exc:
        raise ValueError("invalid Playwright snapshot attestation") from exc


def _playwright_snapshot_toolchain_payload(
    launcher_members: list[dict[str, object]],
    dependency_members: list[dict[str, object]],
    entrypoint_members: list[dict[str, object]] | None,
    browser_members: list[dict[str, object]],
    native_members: tuple[list[dict[str, object]], ...],
    lockfile_members: list[dict[str, object]],
    entrypoint_relative: PurePosixPath | None,
) -> dict[str, object]:
    """Build the relocation-stable typed identity payload from snapshot members."""
    if entrypoint_relative is None:
        if (
            entrypoint_members is None
            or len(entrypoint_members) != 1
            or entrypoint_members[0].get("path") != "."
            or entrypoint_members[0].get("kind") != "file"
        ):
            raise ValueError("Playwright snapshot entrypoint role is malformed")
        entrypoint_role: dict[str, object] = {
            "role": "entrypoint", "members": entrypoint_members,
        }
    else:
        entrypoint_path = entrypoint_relative.as_posix()
        entrypoint = [
            member for member in dependency_members
            if member.get("path") == entrypoint_path and member.get("kind") == "file"
        ]
        if len(entrypoint) != 1:
            raise ValueError("Playwright snapshot does not contain the declared entrypoint")
        normalized_entrypoint = [{**entrypoint[0], "path": "."}]
        if entrypoint_members is not None and entrypoint_members != normalized_entrypoint:
            raise ValueError("Playwright entrypoint role differs from dependency member")
        entrypoint_role = {
            "role": "entrypoint",
            "binding": {"role": "dependencies", "path": entrypoint_path},
        }
    return {
        "schema": _PLAYWRIGHT_SNAPSHOT_TOOLCHAIN_SCHEMA,
        "roles": [
            {"role": "browser_runtime", "members": browser_members},
            {"role": "dependencies", "members": dependency_members},
            entrypoint_role,
            {"role": "launcher", "members": launcher_members},
            *(
                {
                    "role": "native_runtime",
                    "path": str(index),
                    "members": members,
                }
                for index, members in enumerate(native_members)
            ),
            {"role": "lockfile", "members": lockfile_members},
        ],
    }


def _playwright_snapshot_toolchain_identity(
    launcher_members: list[dict[str, object]],
    dependency_members: list[dict[str, object]],
    entrypoint_members: list[dict[str, object]] | None,
    browser_members: list[dict[str, object]],
    native_members: tuple[list[dict[str, object]], ...],
    lockfile_members: list[dict[str, object]],
    entrypoint_relative: PurePosixPath | None,
) -> str:
    """Hash the typed immutable role membership shared by identity and staging."""
    payload = _playwright_snapshot_toolchain_payload(
        launcher_members,
        dependency_members,
        entrypoint_members,
        browser_members,
        native_members,
        lockfile_members,
        entrypoint_relative,
    )
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def _playwright_snapshot_aggregate_identity(
    proofs: tuple[SnapshotBindingProof, ...],
    reporter: Path,
    roles: PlaywrightToolchainRoles,
    launcher_destination: Path,
    dependency_destination: Path,
    native_bindings: tuple[tuple[Path, Path], ...],
    result_fd: int = 198,
) -> tuple[str, PlaywrightSnapshotAggregate]:
    """Bind exact staged snapshots to the previously measured toolchain roles."""
    expected = (
        ("reporter", reporter, reporter),
        ("launcher", roles.launcher, launcher_destination),
        ("browser_runtime", roles.browser_runtime, roles.browser_runtime),
        ("lockfile", roles.lockfile, roles.lockfile),
        ("dependencies", roles.dependencies, dependency_destination),
        *(
            (("entrypoint", roles.entrypoint, roles.entrypoint),)
            if not _path_is_relative_to(roles.entrypoint, roles.dependencies) else ()
        ),
        *((f"native_runtime/{index}", source, destination)
          for index, (source, destination) in enumerate(native_bindings)),
    )
    if len(proofs) != len(expected):
        raise ValueError("Playwright snapshot aggregate is incomplete")
    role_members: dict[str, list[dict[str, object]]] = {}
    aggregate_members = []
    for proof, (role, source, destination) in zip(proofs, expected, strict=True):
        if proof.source != source.resolve(strict=True) or proof.destination != destination:
            raise ValueError("Playwright snapshot aggregate topology mismatch")
        members = _snapshot_binding_members(proof)
        role_members[role] = members
        aggregate_members.append({"role": role, "attestation": proof.attestation})
    native_members = tuple(
        role_members[f"native_runtime/{index}"]
        for index in range(len(native_bindings))
    )
    entrypoint_relative = (
        PurePosixPath(roles.entrypoint.relative_to(roles.dependencies).as_posix())
        if _path_is_relative_to(roles.entrypoint, roles.dependencies) else None
    )
    toolchain_identity = _playwright_snapshot_toolchain_identity(
        role_members["launcher"],
        role_members["dependencies"],
        role_members.get("entrypoint"),
        role_members["browser_runtime"],
        native_members,
        role_members["lockfile"],
        entrypoint_relative,
    )
    canonical_reporter = _playwright_reporter_source(result_fd).encode("utf-8")
    reporter_digest = hashlib.sha256(canonical_reporter).hexdigest()
    reporter_members = role_members["reporter"]
    if reporter_members != [{
        "path": ".", "mode": stat.S_IMODE(reporter.stat().st_mode),
        "digest": reporter_digest, "size": len(canonical_reporter),
        "target": None, "kind": "file",
    }]:
        raise ValueError("Playwright reporter snapshot is not canonical")
    checker_identity = hashlib.sha256(json.dumps({
        "reporter_sha256": reporter_digest,
        "toolchain_identity": toolchain_identity,
    }, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    aggregate = {
        "schema": _PLAYWRIGHT_SNAPSHOT_AGGREGATE_SCHEMA,
        "toolchain_identity": toolchain_identity,
        "checker_identity": checker_identity,
        "observation": {
            "role": "reporter", "transport": "anonymous-pipe-v1",
            "result_fd": result_fd, "reporter_sha256": reporter_digest,
        },
        "members": aggregate_members,
    }
    attestation = json.dumps(aggregate, sort_keys=True, separators=(",", ":"))
    return toolchain_identity, PlaywrightSnapshotAggregate(
        attestation=attestation,
        digest=hashlib.sha256(attestation.encode()).hexdigest(),
        accepted_toolchain_identity=checker_identity,
        result_fd=result_fd,
    )


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


def _manifest_path_identity(
    path: Path, seen: set[tuple[int, int]], relative: PurePosixPath = PurePosixPath(".")
) -> bytes:
    """Return a role-relative lstat Merkle digest without host path spellings."""
    digest = hashlib.sha256()
    try:
        metadata = path.lstat()
        identity = (metadata.st_dev, metadata.st_ino)
        if identity in seen:
            raise ValueError("Playwright toolchain symlink cycle is unsupported")
        seen.add(identity)
        mode = stat.S_IMODE(metadata.st_mode)
        prefix = relative.as_posix().encode() + b"\0" + oct(mode).encode() + b"\0"
        if stat.S_ISLNK(metadata.st_mode):
            target_text = os.readlink(path)
            if os.path.isabs(target_text):
                raise ValueError("Playwright toolchain absolute symlink is unsupported")
            target = (path.parent / target_text).resolve(strict=True)
            digest.update(b"symlink\0" + prefix + target_text.encode() + b"\0")
            digest.update(_manifest_path_identity(target, seen, PurePosixPath("@target")))
            return digest.digest()
        if stat.S_ISREG(metadata.st_mode):
            digest.update(b"file\0" + prefix)
            with path.open("rb") as stream:
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    digest.update(chunk)
            return digest.digest()
        if stat.S_ISDIR(metadata.st_mode):
            digest.update(b"directory\0" + prefix)
            for child in sorted(path.iterdir(), key=lambda item: item.name):
                digest.update(child.name.encode() + b"\0")
                digest.update(_manifest_path_identity(
                    child, seen.copy(), relative / child.name
                ))
                digest.update(b"\0")
            return digest.digest()
        raise ValueError("Playwright toolchain special files are unsupported")
    except OSError as exc:
        raise ValueError("Playwright toolchain member is unreadable") from exc


def _toolchain_manifest_identity(manifest_path: Path) -> str:
    """Hash a strict protected Playwright toolchain manifest and its closure."""
    try:
        payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError("Playwright toolchain manifest is invalid") from exc
    if not isinstance(payload, dict) or set(payload) != {"version", "roles"}:
        raise ValueError("Playwright toolchain manifest must declare typed roles")
    roles = payload.get("roles")
    if payload.get("version") != 3 or not isinstance(roles, dict):
        raise ValueError("Playwright toolchain manifest roles schema is invalid")
    native_values = roles.get("native_runtime")
    scalar_roles = PLAYWRIGHT_TOOLCHAIN_ROLES - {"native_runtime"}
    if (
        set(roles) != PLAYWRIGHT_TOOLCHAIN_ROLES
        or not all(
            isinstance(roles.get(role), str)
            and Path(roles[role]).is_absolute()
            for role in scalar_roles
        )
        or not isinstance(native_values, list)
        or not native_values
        or not all(
            isinstance(item, str) and Path(item).is_absolute()
            for item in native_values
        )
    ):
        raise ValueError("Playwright toolchain manifest roles are incomplete")
    captured: dict[str, list[dict[str, object]]] = {}
    for role in sorted(scalar_roles):
        item = roles[role]
        declared = Path(item)
        if not declared.exists():
            raise ValueError(f"Playwright toolchain role {role} does not exist")
        canonical = declared.resolve(strict=True)
        if role in {"launcher", "entrypoint", "lockfile"} and not canonical.is_file():
            raise ValueError(f"Playwright toolchain role {role} must be a file")
        if role in {"dependencies", "browser_runtime"} and not canonical.is_dir():
            raise ValueError(f"Playwright toolchain role {role} must be a directory")
        _manifest_path_identity(declared, set(), PurePosixPath(role))
        captured[role] = _snapshot_binding_members(
            _snapshot_binding_proof(canonical, Path(f"/{role}"))
        )
    native_members = []
    for index, item in enumerate(native_values):
        declared = Path(item)
        if not declared.exists() or not declared.resolve(strict=True).is_file():
            raise ValueError("Playwright native_runtime role must contain files")
        _manifest_path_identity(
            declared, set(), PurePosixPath("native_runtime") / str(index)
        )
        native_members.append(_snapshot_binding_members(
            _snapshot_binding_proof(
                declared.resolve(strict=True), Path(f"/native_runtime/{index}")
            )
        ))
    entrypoint = Path(roles["entrypoint"]).resolve(strict=True)
    dependencies = Path(roles["dependencies"]).resolve(strict=True)
    try:
        entrypoint_relative = PurePosixPath(entrypoint.relative_to(dependencies).as_posix())
    except ValueError:
        entrypoint_relative = None
    return _playwright_snapshot_toolchain_identity(
        captured["launcher"],
        captured["dependencies"],
        captured["entrypoint"],
        captured["browser_runtime"],
        tuple(native_members),
        captured["lockfile"],
        entrypoint_relative,
    )


def _toolchain_manifest_roles(manifest_path: Path) -> PlaywrightToolchainRoles:
    """Return canonical roles after the manifest has passed identity validation."""
    payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    roles = payload["roles"]
    return PlaywrightToolchainRoles(
        launcher=Path(roles["launcher"]).resolve(strict=True),
        entrypoint=Path(roles["entrypoint"]).resolve(strict=True),
        dependencies=Path(roles["dependencies"]).resolve(strict=True),
        browser_runtime=Path(roles["browser_runtime"]).resolve(strict=True),
        native_runtime=tuple(Path(value) for value in roles["native_runtime"]),
        lockfile=Path(roles["lockfile"]).resolve(strict=True),
    )


def _playwright_toolchain_identity(
    root: Path, command: tuple[str, ...], manifest: Path
) -> str:
    """Validate external command coverage and return the complete identity."""
    candidate = root.resolve()
    if _path_is_relative_to(manifest.resolve(), candidate):
        raise ValueError("Playwright toolchain manifest must be external to candidate checkout")
    manifest_identity = _toolchain_manifest_identity(manifest)
    roles = _toolchain_manifest_roles(manifest)
    role_paths = {
        "launcher": roles.launcher,
        "entrypoint": roles.entrypoint,
        "dependencies": roles.dependencies,
        "browser_runtime": roles.browser_runtime,
        "lockfile": roles.lockfile,
    }
    for role, role_path in role_paths.items():
        if _path_is_relative_to(role_path, candidate):
            raise ValueError(f"Playwright toolchain role {role} must be external")
    for role_path in roles.native_runtime:
        if _path_is_relative_to(role_path.resolve(strict=True), candidate):
            raise ValueError("Playwright toolchain role native_runtime must be external")
    if roles.dependencies.name != "node_modules":
        raise ValueError("Playwright dependencies role must be the NODE_PATH node_modules root")
    if roles.lockfile.parent != roles.dependencies.parent:
        raise ValueError("Playwright lockfile must govern the declared dependency tree")
    package_root = roles.dependencies / "@playwright" / "test"
    if not package_root.is_dir() or not _path_is_relative_to(
        roles.entrypoint, package_root
    ):
        raise ValueError(
            "Playwright entrypoint must be inside the declared @playwright/test dependency package"
        )
    command_paths = []
    for part in command[:2]:
        path = Path(part).expanduser()
        if path.is_absolute() or "/" in part:
            command_paths.append(path.resolve(strict=True))
        else:
            resolved = shutil.which(part)
            if resolved is None:
                raise ValueError("Playwright command launcher is not resolvable")
            command_paths.append(Path(resolved).resolve(strict=True))
    if not command_paths or command_paths[0] != roles.launcher:
        raise ValueError("Playwright toolchain launcher role does not cover command")
    if len(command_paths) < 2 or command_paths[1] != roles.entrypoint:
        raise ValueError("Playwright toolchain entrypoint role does not cover command")
    return manifest_identity


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
        if config.playwright_toolchain_manifest is None:
            payload["playwright_toolchain_manifest"] = "missing"
        else:
            try:
                identity = config.playwright_toolchain_identity or _toolchain_manifest_identity(
                    config.playwright_toolchain_manifest
                )
            except ValueError:
                identity = "invalid"
            payload["playwright_toolchain_manifest"] = identity
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
    if config.playwright_command is not None or config.playwright_toolchain_manifest is not None:
        try:
            if config.playwright_command is None or config.playwright_toolchain_manifest is None:
                raise ValueError("Playwright command and toolchain manifest are required together")
            identity = _playwright_toolchain_identity(
                root, config.playwright_command, config.playwright_toolchain_manifest
            )
            identities.append(("playwright", identity))
        except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
            errors["playwright"] = str(exc)
            identities.append(("playwright", _adapter_capture_error_identity("playwright", exc)))
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
    content: bytes, returncode: int, output: str, minimum_tests: int
) -> tuple[EvidenceOutcome, str]:
    try:
        root = ET.fromstring(content)
    except ET.ParseError as exc:
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


def _jest_reporter_source(result_fd: int) -> str:
    """Return a checker-owned Jest reporter for the observation descriptor."""
    return f"""const RESULT_FD = {result_fd};
class PddFrameworkReporter {{
  constructor() {{ this.tests = []; }}
  onTestResult(test, result) {{
    for (const assertion of result.testResults || []) {{
      const names = [...(assertion.ancestorTitles || []), assertion.title].join(' > ');
      this.tests.push({{identity: require('path').relative(process.cwd(), test.path) + '::' + names, status: assertion.status}});
    }}
  }}
  onRunComplete() {{ require('fs').writeSync(RESULT_FD, JSON.stringify({{tests: this.tests}})); }}
}}
module.exports = PddFrameworkReporter;
"""


def _jest_result(
    output: bytes, returncode: int, expected: tuple[str, ...] | None
) -> tuple[EvidenceOutcome, str, tuple[str, ...]]:
    # pylint: disable=too-many-return-statements
    """Validate checker-owned framework observations and normalize non-pass states."""
    try:
        payload = json.loads(output.decode("utf-8"))
        tests = payload["tests"]
        if not isinstance(tests, list) or not all(
            isinstance(item, dict)
            and isinstance(item.get("identity"), str)
            and isinstance(item.get("status"), str)
            for item in tests
        ):
            raise ValueError("malformed Jest reporter payload")
    except (UnicodeDecodeError, ValueError, json.JSONDecodeError, KeyError):
        return EvidenceOutcome.COLLECTION_ERROR, "Jest reporter produced malformed JSON", ()
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
    """Run exact protected Jest paths using a checker-owned reporter."""
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
        reporter.write_text(_jest_reporter_source(result_fd), encoding="utf-8")
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
                env=_jest_environment(home),
                writable_roots=(scratch,),
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
                result_fifo=result_fifo,
                result_fd=result_fd,
            )
        except OSError as exc:
            drain_finished.set()
            drain_thread.join(timeout=1)
            os.close(read_fd)
            return RunnerExecution(
                "jest",
                EvidenceOutcome.ERROR,
                digest,
                f"Jest process launch failed: {exc}",
            ), ()
        drain_finished.set()
        drain_thread.join(timeout=2)
        os.close(read_fd)
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
        if "error" in drained or drained.get("overflow"):
            return RunnerExecution(
                "jest", EvidenceOutcome.COLLECTION_ERROR, digest,
                "Jest bounded observation transport failed",
            ), ()
        output = drained.get("data", b"")
        if not isinstance(output, bytes):
            output = b""
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


VITEST_LIFECYCLE_REPORTER_ERRORS = frozenset({
    "queued-missing",
    "queued-unexpected",
    "queued-duplicate",
    "collected-missing",
    "collected-unexpected",
    "collected-duplicate",
    "started-missing",
    "started-unexpected",
    "started-duplicate",
    "ended-missing",
    "ended-unexpected",
    "ended-duplicate",
    "terminal-missing",
    "terminal-unexpected",
    "terminal-completed-divergence",
    "duplicate-run-start",
    "invalid-scheduled-modules",
    "invalid-queued-module",
    "unexpected-queued-module",
    "duplicate-queued-module",
    "invalid-collected-module",
    "unexpected-collected-module",
    "duplicate-collected-module",
    "invalid-started-module",
    "unexpected-started-module",
    "duplicate-started-module",
    "unscheduled-completed-module",
    "duplicate-completed-module",
    "test-count-overflow",
    "invalid-completed-module",
    "invalid-terminal-reason",
    "invalid-unhandled-errors",
    "invalid-terminal-modules",
    "invalid-completed-tests",
    "error-count-overflow",
})

VITEST_LIFECYCLE_STRUCTURAL_ERRORS = frozenset({
    "queued-missing", "queued-unexpected", "queued-duplicate",
    "collected-missing", "collected-unexpected", "collected-duplicate",
    "started-missing", "started-unexpected", "started-duplicate",
    "ended-missing", "ended-unexpected", "ended-duplicate",
    "terminal-missing", "terminal-unexpected",
})

VITEST_LIFECYCLE_REJECTIONS = MappingProxyType({
    "root-shape": "root fields are not canonical",
    "schema": "schema version is not supported",
    "lifecycle-shape": "lifecycle fields are not canonical",
    "errors-shape": "error fields are not canonical",
    "module-list-shape": "module table is not bounded",
    "test-list-shape": "test table is not bounded",
    "module-set-shape": "module callback sets are not canonical",
    "queued-missing": "queued callbacks are missing scheduled modules",
    "queued-unexpected": "queued callbacks include unexpected modules",
    "queued-duplicate": "queued callback was duplicated",
    "collected-missing": "collected callbacks are missing scheduled modules",
    "collected-unexpected": "collected callbacks include unexpected modules",
    "collected-duplicate": "collected callback was duplicated",
    "started-missing": "started callbacks are missing scheduled modules",
    "started-unexpected": "started callbacks include unexpected modules",
    "started-duplicate": "started callback was duplicated",
    "ended-missing": "ended callbacks are missing scheduled modules",
    "ended-unexpected": "ended callbacks include unexpected modules",
    "ended-duplicate": "ended callback was duplicated",
    "terminal-missing": "terminal callbacks are missing completed modules",
    "terminal-unexpected": "terminal callbacks include unexpected modules",
    "terminal-completed-divergence": "terminal modules diverged from completed modules",
    "duplicate-run-start": "run start callback was duplicated",
    "invalid-scheduled-modules": "scheduled module collection is invalid",
    "invalid-queued-module": "queued module identity is invalid",
    "unexpected-queued-module": "queued module was not scheduled",
    "duplicate-queued-module": "queued module callback was duplicated",
    "invalid-collected-module": "collected module identity is invalid",
    "unexpected-collected-module": "collected module was not scheduled",
    "duplicate-collected-module": "collected module callback was duplicated",
    "invalid-started-module": "started module identity is invalid",
    "unexpected-started-module": "started module was not scheduled",
    "duplicate-started-module": "started module callback was duplicated",
    "unscheduled-completed-module": "completed module was not scheduled",
    "duplicate-completed-module": "completed module callback was duplicated",
    "test-count-overflow": "completed test count exceeds the bound",
    "invalid-completed-module": "completed module snapshot is invalid",
    "invalid-terminal-reason": "terminal reason is invalid",
    "invalid-unhandled-errors": "unhandled error collection is invalid",
    "invalid-terminal-modules": "terminal module collection is invalid",
    "invalid-completed-tests": "completed test collection is invalid",
    "error-count-overflow": "combined reporter errors exceed the bound",
    "reason": "terminal reason is not supported",
    "proof-shape": "proof flag is not canonical",
    "exit-shape": "exit fields are not canonical",
    "exit-divergence": "reported exit differs from the process",
    "error-list-shape": "error list is not bounded",
    "reporter-error-shape": "reporter rejection is not allowlisted",
    "module-shape": "module table entry is not canonical",
    "module-identity": "module identity is not canonical",
    "module-count": "module counts are not bounded",
    "module-table-divergence": "module table diverged from completion",
    "module-error-divergence": "module error count diverged",
    "test-shape": "test table entry is not canonical",
    "test-identity": "test identity is not canonical",
    "test-order": "test identities are not unique and sorted",
    "test-count-divergence": "module test count diverged",
    "error-bound": "combined lifecycle errors exceed the bound",
    "proof-divergence": "reported proof or exit transition diverged",
    "reporter-state": "reporter rejected the public callback lifecycle",
    "non-pass-divergence": "non-pass lifecycle state is inconsistent",
})

# This ordering is shared verbatim with the trusted JavaScript reporter.  It is
# deliberately independent of callback arrival order and contains every fixed
# rejection exactly once, including codes Python alone can emit for schema data.
VITEST_LIFECYCLE_ERROR_PRIORITY = (
    "root-shape", "schema", "lifecycle-shape", "errors-shape",
    "module-list-shape", "test-list-shape", "module-set-shape",
    "queued-missing", "queued-unexpected", "queued-duplicate",
    "collected-missing", "collected-unexpected", "collected-duplicate",
    "started-missing", "started-unexpected", "started-duplicate",
    "ended-missing", "ended-unexpected", "ended-duplicate",
    "terminal-missing", "terminal-unexpected",
    "terminal-completed-divergence",
    "duplicate-run-start", "invalid-scheduled-modules",
    "invalid-queued-module", "unexpected-queued-module",
    "duplicate-queued-module", "invalid-collected-module",
    "unexpected-collected-module", "duplicate-collected-module",
    "invalid-started-module", "unexpected-started-module",
    "duplicate-started-module", "unscheduled-completed-module",
    "duplicate-completed-module", "test-count-overflow",
    "invalid-completed-module", "invalid-terminal-reason",
    "invalid-unhandled-errors", "invalid-terminal-modules",
    "invalid-completed-tests", "error-count-overflow",
    "reason", "proof-shape", "exit-shape", "exit-divergence",
    "error-list-shape", "reporter-error-shape", "module-shape",
    "module-identity", "module-count", "module-table-divergence",
    "module-error-divergence", "test-shape", "test-identity", "test-order",
    "test-count-divergence", "error-bound", "proof-divergence",
    "reporter-state", "non-pass-divergence",
)


class VitestLifecycleRejection(ValueError):
    """A fixed non-candidate lifecycle rejection safe for diagnostics."""

    def __init__(self, code: str) -> None:
        if code not in VITEST_LIFECYCLE_REJECTIONS:
            raise ValueError("unknown Vitest lifecycle rejection")
        self.code = code
        super().__init__(code)


def _reject_vitest_lifecycle(code: str) -> NoReturn:
    """Reject a lifecycle with an allowlisted non-reflective code."""
    raise VitestLifecycleRejection(code)


def _vitest_lifecycle_payload(
    payload: dict[str, object], returncode: int,
) -> tuple[list[dict[str, object]], str]:
    """Validate the bounded trusted lifecycle schema and recompute adjudication."""
    if set(payload) != {"schema", "lifecycle", "errors", "modules", "tests"}:
        _reject_vitest_lifecycle("root-shape")
    if payload.get("schema") != VITEST_LIFECYCLE_SCHEMA:
        _reject_vitest_lifecycle("schema")
    lifecycle = payload.get("lifecycle")
    errors = payload.get("errors")
    modules = payload.get("modules")
    tests = payload.get("tests")
    if not isinstance(lifecycle, dict) or set(lifecycle) != {
        "reason", "proof", "ambientExitCode", "exitCode", "scheduled",
        "completed", "terminal", "queued", "collected", "started", "ended",
        "stageFlags",
    }:
        _reject_vitest_lifecycle("lifecycle-shape")
    if not isinstance(errors, dict) or set(errors) != {
        "module", "unhandled", "reporter",
    }:
        _reject_vitest_lifecycle("errors-shape")
    if not isinstance(modules, list) or len(modules) > VITEST_LIFECYCLE_MAX_MODULES:
        _reject_vitest_lifecycle("module-list-shape")
    if not isinstance(tests, list) or len(tests) > VITEST_LIFECYCLE_MAX_TESTS:
        _reject_vitest_lifecycle("test-list-shape")

    def bounded_string(value: object, *, identity: bool = False) -> bool:
        limit = VITEST_LIFECYCLE_MAX_STRING * (2 if identity else 1) + (
            2 if identity else 0
        )
        return isinstance(value, str) and bool(value) and len(value) <= limit

    def integer(value: object) -> bool:
        return isinstance(value, int) and not isinstance(value, bool)

    def module_id(value: object) -> bool:
        if not bounded_string(value) or not isinstance(value, str):
            return False
        path = PurePosixPath(value)
        return (
            not path.is_absolute()
            and "\\" not in value
            and path.parts
            and all(part not in {"", ".", ".."} for part in path.parts)
        )

    def bounded_strings(
        value: object, *, canonical_order: bool = True,
    ) -> list[str]:
        if (
            not isinstance(value, list)
            or len(value) > VITEST_LIFECYCLE_MAX_ERRORS
            or not all(bounded_string(item) for item in value)
            or (canonical_order and value != sorted(value))
        ):
            _reject_vitest_lifecycle("error-list-shape")
        return value

    callback_names = (
        "scheduled", "queued", "collected", "started", "ended", "completed",
    )
    callback_sets: dict[str, list[str]] = {}
    for name in callback_names:
        value = lifecycle.get(name)
        if (
            not isinstance(value, list)
            or len(value) > VITEST_LIFECYCLE_MAX_MODULES
            or not all(module_id(item) for item in value)
            or value != sorted(value)
            or len(set(value)) != len(value)
        ):
            _reject_vitest_lifecycle("module-set-shape")
        callback_sets[name] = value
    scheduled = callback_sets["scheduled"]
    completed = callback_sets["completed"]
    if not scheduled:
        _reject_vitest_lifecycle("module-set-shape")
    raw_stage_flags = lifecycle.get("stageFlags")
    stage_names = ("queued", "collected", "started", "ended")
    if not isinstance(raw_stage_flags, dict) or set(raw_stage_flags) != set(
        stage_names
    ):
        _reject_vitest_lifecycle("lifecycle-shape")
    stage_flags: dict[str, dict[str, bool]] = {}
    for name in stage_names:
        value = raw_stage_flags.get(name)
        if (
            not isinstance(value, dict)
            or set(value) != {"unexpected", "duplicate"}
            or any(not isinstance(value.get(flag), bool) for flag in value)
        ):
            _reject_vitest_lifecycle("lifecycle-shape")
        stage_flags[name] = value

    scheduled_set = set(scheduled)
    structural_errors: set[str] = set()
    for name in stage_names:
        observed = set(callback_sets[name])
        missing = bool(scheduled_set - observed)
        unexpected = bool(observed - scheduled_set)
        if name == "ended":
            missing = missing or bool(scheduled_set - set(completed))
            unexpected = unexpected or bool(set(completed) - scheduled_set)
        if missing:
            structural_errors.add(f"{name}-missing")
        if unexpected or stage_flags[name]["unexpected"]:
            structural_errors.add(f"{name}-unexpected")
        if stage_flags[name]["duplicate"]:
            structural_errors.add(f"{name}-duplicate")

    terminal = lifecycle.get("terminal")
    if (
        not isinstance(terminal, list)
        or len(terminal) > VITEST_LIFECYCLE_MAX_MODULES
        or not all(module_id(item) for item in terminal)
        or terminal != sorted(terminal)
        or len(set(terminal)) != len(terminal)
    ):
        _reject_vitest_lifecycle("module-set-shape")
    if terminal:
        terminal_set = set(terminal)
        completed_set = set(completed)
        if completed_set - terminal_set:
            structural_errors.add("terminal-missing")
        if terminal_set - completed_set:
            structural_errors.add("terminal-unexpected")
    if lifecycle.get("reason") not in {"passed", "failed", "interrupted"}:
        _reject_vitest_lifecycle("reason")
    if not isinstance(lifecycle.get("proof"), bool):
        _reject_vitest_lifecycle("proof-shape")
    ambient_exit_code = lifecycle.get("ambientExitCode")
    exit_code = lifecycle.get("exitCode")
    if (
        not integer(ambient_exit_code)
        or not 0 <= ambient_exit_code <= 255
        or not integer(exit_code)
        or not 0 <= exit_code <= 255
    ):
        _reject_vitest_lifecycle("exit-shape")
    if returncode != exit_code:
        _reject_vitest_lifecycle("exit-divergence")

    module_errors = bounded_strings(errors.get("module"))
    unhandled_errors = bounded_strings(errors.get("unhandled"))
    reporter_errors = bounded_strings(
        errors.get("reporter"), canonical_order=False,
    )
    if (
        len(set(reporter_errors)) != len(reporter_errors)
        or set(reporter_errors) - VITEST_LIFECYCLE_REPORTER_ERRORS
    ):
        _reject_vitest_lifecycle("reporter-error-shape")
    reporter_only_errors = (
        set(reporter_errors) - VITEST_LIFECYCLE_STRUCTURAL_ERRORS
    )
    canonical_reporter_errors = [
        code for code in VITEST_LIFECYCLE_ERROR_PRIORITY
        if code in structural_errors or code in reporter_only_errors
    ]
    if reporter_errors != canonical_reporter_errors:
        _reject_vitest_lifecycle("reporter-error-shape")

    normalized_modules: list[dict[str, object]] = []
    for item in modules:
        if not isinstance(item, dict) or set(item) != {
            "moduleId", "testCount", "errorCount",
        }:
            _reject_vitest_lifecycle("module-shape")
        if not module_id(item.get("moduleId")):
            _reject_vitest_lifecycle("module-identity")
        if any(
            not integer(item.get(name))
            or not 0 <= item[name] <= VITEST_LIFECYCLE_MAX_TESTS
            for name in ("testCount", "errorCount")
        ):
            _reject_vitest_lifecycle("module-count")
        normalized_modules.append(item)
    module_ids = [item["moduleId"] for item in normalized_modules]
    if module_ids != completed or module_ids != sorted(module_ids):
        _reject_vitest_lifecycle("module-table-divergence")
    if sum(int(item["errorCount"]) for item in normalized_modules) != len(
        module_errors
    ):
        _reject_vitest_lifecycle("module-error-divergence")

    normalized_tests: list[dict[str, object]] = []
    for item in tests:
        if not isinstance(item, dict) or set(item) != {
            "moduleId", "name", "identity", "status", "failureMessages",
        }:
            _reject_vitest_lifecycle("test-shape")
        item_module = item.get("moduleId")
        name = item.get("name")
        identity = item.get("identity")
        failures = item.get("failureMessages")
        if (
            not module_id(item_module)
            or not bounded_string(name)
            or not bounded_string(identity, identity=True)
            or identity != f"{item_module}::{name}"
            or item_module not in completed
            or item.get("status") not in {
                "passed", "failed", "pending", "todo", "skipped", "disabled",
            }
        ):
            _reject_vitest_lifecycle("test-identity")
        bounded_strings(failures)
        normalized_tests.append(item)
    identities = [str(item["identity"]) for item in normalized_tests]
    if identities != sorted(identities) or len(set(identities)) != len(identities):
        _reject_vitest_lifecycle("test-order")
    for module in normalized_modules:
        if sum(
            item["moduleId"] == module["moduleId"] for item in normalized_tests
        ) != module["testCount"]:
            _reject_vitest_lifecycle("test-count-divergence")
    failure_count = sum(
        len(item["failureMessages"]) for item in normalized_tests
    )
    if (
        len(module_errors) + len(unhandled_errors) + failure_count
        > VITEST_LIFECYCLE_MAX_ERRORS
    ):
        _reject_vitest_lifecycle("error-bound")

    statuses = {str(item["status"]) for item in normalized_tests}
    proof = bool(
        normalized_tests
        and not reporter_errors
        and all(callback_sets[name] == scheduled for name in stage_names)
        and completed == scheduled
        and not any(
            flag
            for flags in stage_flags.values()
            for flag in flags.values()
        )
        and not module_errors
        and not unhandled_errors
        and not failure_count
        and statuses == {"passed"}
    )
    false_sentinel_pass = bool(
        proof
        and not terminal
        and lifecycle["reason"] == "failed"
        and ambient_exit_code == 1
    )
    normal_pass = bool(
        proof
        and terminal == scheduled
        and lifecycle["reason"] == "passed"
        and ambient_exit_code == 0
    )
    expected_exit_code = 0 if false_sentinel_pass or normal_pass else (
        ambient_exit_code or 1
    )
    if lifecycle["proof"] is not proof or exit_code != expected_exit_code:
        _reject_vitest_lifecycle("proof-divergence")
    if reporter_errors:
        _reject_vitest_lifecycle(reporter_errors[0])
    if false_sentinel_pass or normal_pass:
        return normalized_tests, "pass"
    if (
        module_errors or unhandled_errors or failure_count
        or "failed" in statuses
        or lifecycle["reason"] in {"failed", "interrupted"}
    ):
        return normalized_tests, "fail"
    if not normalized_tests:
        return normalized_tests, "empty"
    if statuses - {"passed"}:
        return normalized_tests, "skip"
    if proof and exit_code:
        return normalized_tests, "fail"
    _reject_vitest_lifecycle("non-pass-divergence")


def _vitest_result(
    root: Path, output: Path, returncode: int, expected: tuple[str, ...] | None
) -> tuple[EvidenceOutcome, str, tuple[str, ...]]:
    """Validate Vitest JSON output and normalize every non-pass state."""
    try:
        payload = json.loads(output.read_text(encoding="utf-8"))
        if not isinstance(payload, dict):
            raise ValueError("malformed Vitest reporter payload")
        lifecycle_outcome: str | None = None
        if "schema" in payload:
            tests, lifecycle_outcome = _vitest_lifecycle_payload(
                payload, returncode
            )
            canonical = True
        else:
            canonical = "tests" in payload
            tests = payload.get("tests")
        if lifecycle_outcome is None and not canonical:
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
        if lifecycle_outcome is None and (
            not isinstance(tests, list) or not all(
            isinstance(item, dict)
            and isinstance(item.get("identity"), str)
            and isinstance(item.get("status"), str)
            and (
                not canonical
                or "failureMessages" not in item
                or (
                    isinstance(item["failureMessages"], list)
                    and all(
                        isinstance(message, str)
                        for message in item["failureMessages"]
                    )
                )
            )
            for item in tests
            )
        ):
            raise ValueError("malformed Vitest reporter payload")
        prior_failures = (
            any(item.get("failureMessages", []) for item in tests)
            if canonical
            else any(
                item.get("failureMessages")
                for result in payload.get("testResults", [])
                for item in result.get("assertionResults", [])
            )
        ) if lifecycle_outcome is None else False
    except VitestLifecycleRejection as exc:
        detail = VITEST_LIFECYCLE_REJECTIONS[exc.code]
        return (
            EvidenceOutcome.COLLECTION_ERROR,
            f"Vitest lifecycle rejected [{exc.code}]: {detail}",
            (),
        )
    except (AttributeError, OSError, TypeError, ValueError, json.JSONDecodeError, KeyError):
        return EvidenceOutcome.COLLECTION_ERROR, "Vitest reporter produced malformed JSON", ()
    identities = tuple(sorted(item["identity"] for item in tests))
    if lifecycle_outcome == "collection-error":
        return EvidenceOutcome.COLLECTION_ERROR, "Vitest lifecycle proof is inconsistent", identities
    if lifecycle_outcome == "fail" and not identities:
        return EvidenceOutcome.FAIL, "Vitest reported failed protected tests", ()
    if lifecycle_outcome == "empty":
        return EvidenceOutcome.NOT_COLLECTED, "zero protected Vitest test identities collected", ()
    if not identities:
        return EvidenceOutcome.NOT_COLLECTED, "zero protected Vitest test identities collected", ()
    if len(set(identities)) != len(identities):
        return EvidenceOutcome.COLLECTION_ERROR, "Vitest reporter emitted duplicate test identities", ()
    if expected is not None and identities != expected:
        return EvidenceOutcome.QUARANTINED, "checked-head Vitest identities differ from protected base", identities
    if lifecycle_outcome == "fail":
        return EvidenceOutcome.FAIL, "Vitest reported failed protected tests", identities
    if lifecycle_outcome == "skip":
        return EvidenceOutcome.SKIP, "Vitest reported skipped or todo protected tests", identities
    if lifecycle_outcome == "pass":
        return EvidenceOutcome.PASS, f"{len(identities)} protected Vitest tests passed", identities
    statuses = {item["status"] for item in tests}
    if statuses - {"passed", "failed", "pending", "todo", "skipped", "disabled"}:
        return EvidenceOutcome.COLLECTION_ERROR, "Vitest reporter emitted an unsupported status", identities
    if returncode or "failed" in statuses or prior_failures:
        return EvidenceOutcome.FAIL, "Vitest reported failed protected tests", identities
    if statuses - {"passed"}:
        return EvidenceOutcome.SKIP, "Vitest reported skipped or todo protected tests", identities
    return EvidenceOutcome.PASS, f"{len(identities)} protected Vitest tests passed", identities


def _vitest_infrastructure_termination(
    result: subprocess.CompletedProcess[str], timeout_seconds: int,
    *, progress: tuple[object, ...] = (),
) -> tuple[EvidenceOutcome, str]:
    """Describe trusted no-reporter termination without trusting stderr prose."""
    termination = getattr(result, "termination", None)
    kind = getattr(getattr(termination, "kind", None), "value", None)
    if kind is None:
        kind = "timeout" if result.returncode == 124 else (
            "signal" if result.returncode < 0 else "exit"
        )
    fields = ["Vitest infrastructure termination: reporter=missing", f"kind={kind}"]
    trusted_progress: list[str] = []
    for stage in progress[:len(VitestProgressStage)]:
        if isinstance(stage, VitestProgressStage) and stage.value not in trusted_progress:
            trusted_progress.append(stage.value)
    if trusted_progress:
        fields.append("trusted_vitest_progress=" + ",".join(trusted_progress))
    if kind in {"exit", "sandbox-error"}:
        fields.append(f"exit_code={getattr(termination, 'exit_code', result.returncode)}")
    elif kind == "signal":
        number = getattr(termination, "signal_number", -result.returncode)
        try:
            name = signal.Signals(number).name
        except (TypeError, ValueError):
            name = "UNKNOWN"
        fields.extend((f"signal={name}", f"signal_number={number}"))
    elif kind == "timeout":
        fields.append(
            f"timeout_seconds={getattr(termination, 'timeout_seconds', timeout_seconds)}"
        )
    elif kind == "resource-limit":
        fields.append(f"resource_limit={getattr(termination, 'resource_limit', None) or 'unknown'}")
    if isinstance(termination, SupervisorTermination):
        if kind == "sandbox-error":
            raw_phases = termination.failure_phases
            phases: list[str] = []
            if isinstance(raw_phases, tuple):
                for phase in raw_phases[:len(InfrastructureFailurePhase)]:
                    if (
                        isinstance(phase, InfrastructureFailurePhase)
                        and phase.value not in phases
                    ):
                        phases.append(phase.value)
            if not phases:
                phases.append(InfrastructureFailurePhase.UNKNOWN.value)
            fields.append("trusted_failure_phases=" + ",".join(phases))
            subreason = termination.scope_setup_subreason
            if (
                InfrastructureFailurePhase.SCOPE_SETUP.value in phases
                and isinstance(subreason, ScopeSetupFailureReason)
            ):
                fields.append("trusted_scope_setup_subreason=" + subreason.value)
        telemetry = termination.resource_telemetry
        if telemetry is not None:
            fields.extend((
                f"cgroup_memory_oom_delta={telemetry.memory_oom_delta}",
                f"cgroup_memory_oom_kill_delta={telemetry.memory_oom_kill_delta}",
                f"cgroup_pids_max_delta={telemetry.pids_max_delta}",
            ))
    diagnostic = result.stderr or result.stdout
    if diagnostic:
        fields.append("diagnostic_sha256=" + hashlib.sha256(
            diagnostic.encode("utf-8")
        ).hexdigest())
    return (
        EvidenceOutcome.TIMEOUT if kind == "timeout" else EvidenceOutcome.ERROR,
        "; ".join(fields),
    )


def _vitest_progress_frame(stage: VitestProgressStage) -> bytes:
    """Return one atomic, value-free Vitest progress record."""
    if not isinstance(stage, VitestProgressStage):
        raise ValueError("Vitest progress transport stage is invalid")
    return _VITEST_PROGRESS_PREFIX + stage.value.encode("ascii") + b"\n"


def _vitest_result_frame(payload: bytes) -> bytes:
    """Return the terminal Vitest result record without interpreting its JSON."""
    if not isinstance(payload, bytes) or not payload or b"\n" in payload:
        raise ValueError("Vitest progress transport result is invalid")
    return _VITEST_RESULT_PREFIX + payload + b"\n"


def _parse_vitest_transport(
    transport: bytes,
) -> tuple[bytes, tuple[VitestProgressStage, ...]]:
    """Validate bounded process-topology progress and terminal reporter JSON."""
    if not isinstance(transport, bytes):
        raise ValueError("Vitest progress transport is invalid")
    # Retain deterministic unit harness compatibility. Production standard-
    # anonymous execution always emits the post-drop record before Node exec.
    if transport.startswith(b"{"):
        return transport, ()
    if not transport:
        return b"", ()
    if not transport.endswith(b"\n"):
        raise ValueError("Vitest progress transport has a partial record")
    records = transport.splitlines()
    if len(records) > _VITEST_PROGRESS_MAX_RECORDS + 1:
        raise ValueError("Vitest progress transport exceeded its record bound")
    observed: list[VitestProgressStage] = []
    result = b""
    for record in records:
        if result:
            raise ValueError("Vitest progress transport has trailing data")
        if record.startswith(_VITEST_RESULT_PREFIX):
            if not observed or observed[-1] is not VitestProgressStage.RESULT_PUBLISHED:
                raise ValueError("Vitest progress transport result is out of order")
            result = record[len(_VITEST_RESULT_PREFIX):]
            if not result:
                raise ValueError("Vitest progress transport result is invalid")
            continue
        if not record.startswith(_VITEST_PROGRESS_PREFIX):
            raise ValueError("Vitest progress transport record is invalid")
        try:
            stage = VitestProgressStage(
                record[len(_VITEST_PROGRESS_PREFIX):].decode("ascii")
            )
        except (UnicodeError, ValueError) as exc:
            raise ValueError("Vitest progress transport stage is invalid") from exc
        seen = set(observed)
        if VitestProgressStage.RESULT_PUBLISHED in seen:
            observed_values = ",".join(item.value for item in observed)
            raise ValueError(
                "Vitest progress transport stage is out of order "
                f"(observed={observed_values}; failing={stage.value})"
            )
        # The wrapper path is linear through exec. After exec, coordinator and
        # fork-worker writes race on the pipe; worker and collection callbacks
        # are observations, not prerequisites for coordinator publication.
        required = {
            VitestProgressStage.POST_DROP_PROBES: set(),
            VitestProgressStage.CANDIDATE_EXEC: {
                VitestProgressStage.POST_DROP_PROBES,
            },
            VitestProgressStage.COORDINATOR_START: {
                VitestProgressStage.CANDIDATE_EXEC,
            },
            VitestProgressStage.WORKER_START: {
                VitestProgressStage.CANDIDATE_EXEC,
            },
            VitestProgressStage.COLLECTION_COMPLETE: {
                VitestProgressStage.COORDINATOR_START,
            },
            VitestProgressStage.MODULE_COMPLETE: {
                VitestProgressStage.COORDINATOR_START,
            },
            VitestProgressStage.RESULT_PUBLISHED: {
                VitestProgressStage.COORDINATOR_START,
            },
        }[stage]
        if not required.issubset(seen):
            observed_values = ",".join(item.value for item in observed)
            raise ValueError(
                "Vitest progress transport stage is out of order "
                f"(observed={observed_values}; failing={stage.value})"
            )
        if (
            stage not in {
                VitestProgressStage.WORKER_START,
                VitestProgressStage.MODULE_COMPLETE,
            }
            and stage in seen
        ):
            raise ValueError("Vitest progress transport stage is duplicated")
        if stage not in seen:
            observed.append(stage)
    return result, tuple(observed)


def _vitest_reporter_source(result_fd: int) -> str:
    """Return a checker-owned reporter that writes only from the coordinator."""
    return f"""import fs from 'node:fs';
import path from 'node:path';
const RESULT_FD = {result_fd};
const SCHEMA = '{VITEST_LIFECYCLE_SCHEMA}';
const MAX_MODULES = {VITEST_LIFECYCLE_MAX_MODULES};
const MAX_TESTS = {VITEST_LIFECYCLE_MAX_TESTS};
const MAX_ERRORS = {VITEST_LIFECYCLE_MAX_ERRORS};
const MAX_STRING = {VITEST_LIFECYCLE_MAX_STRING};
const ERROR_PRIORITY = {json.dumps(VITEST_LIFECYCLE_ERROR_PRIORITY)};
const coordinatorExit = process.exit.bind(process);
const writeAll = (value) => {{
  const buffer = Buffer.from(value);
  let offset = 0;
  while (offset < buffer.length) {{
    const remaining = buffer.length - offset;
    const written = fs.writeSync(RESULT_FD, buffer, offset, remaining);
    if (!Number.isSafeInteger(written) || written <= 0 || written > remaining) {{
      throw new Error('trusted Vitest result write did not advance safely');
    }}
    offset += written;
  }}
}};
const progress = (stage) => writeAll(
  'PDD-VITEST-PROGRESS-V1 ' + stage + '\\n'
);
const byteCompare = (left, right) => Buffer.compare(
  Buffer.from(left, 'utf8'), Buffer.from(right, 'utf8')
);
const errorText = (item) => {{
  let value = 'error';
  try {{
    if (typeof item === 'string' && item) value = item;
    else if (item && typeof item.stack === 'string' && item.stack) value = item.stack;
    else if (item && typeof item.message === 'string' && item.message) value = item.message;
  }} catch (_error) {{
    value = 'error';
  }}
  return value.slice(0, MAX_STRING) || 'error';
}};
const boundedErrors = (value) => {{
  if (value === undefined || value === null) return [];
  if (!Array.isArray(value) || value.length > MAX_ERRORS) {{
    throw new Error('invalid error collection');
  }}
  return value.map(errorText).sort(byteCompare);
}};
const moduleIdentity = (value) => {{
  if (typeof value !== 'string' || !value || value.length > MAX_STRING) {{
    throw new Error('invalid module identity');
  }}
  const absolute = path.normalize(value);
  if (!path.isAbsolute(absolute)) throw new Error('module identity is not absolute');
  const relative = path.relative(process.cwd(), absolute).split(path.sep).join('/');
  if (
    !relative || relative.length > MAX_STRING || path.posix.isAbsolute(relative)
    || relative === '..' || relative.startsWith('../')
  ) {{
    throw new Error('module identity escapes the protected root');
  }}
  return {{absolute, relative}};
}};
const sameArray = (left, right) => (
  left.length === right.length && left.every((value, index) => value === right[index])
);
const freezeSnapshot = (snapshot) => Object.freeze({{
  moduleId: snapshot.moduleId,
  absoluteId: snapshot.absoluteId,
  errors: Object.freeze(snapshot.errors),
  tests: Object.freeze(snapshot.tests.map((test) => Object.freeze({{
    ...test,
    failureMessages: Object.freeze(test.failureMessages),
  }}))),
}});
export default class PddFrameworkVitestReporter {{
  constructor() {{
    this.runStarted = false;
    this.collectionReported = false;
    this.scheduled = [];
    this.completed = new Map();
    this.stages = {{
      queued: new Map(),
      collected: new Map(),
      started: new Map(),
      ended: new Map(),
    }};
    this.stageFlags = {{
      queued: {{unexpected: false, duplicate: false}},
      collected: {{unexpected: false, duplicate: false}},
      started: {{unexpected: false, duplicate: false}},
      ended: {{unexpected: false, duplicate: false}},
    }};
    this.reporterErrors = [];
    progress('coordinator-start');
  }}
  invalidate(code) {{
    if (!this.reporterErrors.includes(code)) this.reporterErrors.push(code);
  }}
  recordStage(name, value) {{
    let identity;
    try {{
      identity = moduleIdentity(value?.moduleId);
    }} catch (_error) {{
      this.stageFlags[name].unexpected = true;
      this.invalidate('invalid-' + name + '-module');
      return false;
    }}
    if (!this.scheduled.some((item) => item.absolute === identity.absolute)) {{
      this.stageFlags[name].unexpected = true;
      this.invalidate('unexpected-' + name + '-module');
      return false;
    }}
    if (this.stages[name].has(identity.absolute)) {{
      this.stageFlags[name].duplicate = true;
      this.invalidate('duplicate-' + name + '-module');
      return false;
    }}
    this.stages[name].set(identity.absolute, identity);
    return true;
  }}
  stageValues(name) {{
    return [...this.stages[name].values()].sort(
      (left, right) => byteCompare(left.absolute, right.absolute)
    );
  }}
  onTestRunStart(specifications) {{
    if (this.runStarted) {{ this.invalidate('duplicate-run-start'); return; }}
    this.runStarted = true;
    try {{
      if (
        !Array.isArray(specifications) || specifications.length === 0
        || specifications.length > MAX_MODULES
      ) throw new Error('invalid scheduled modules');
      const scheduled = specifications.map((item) => moduleIdentity(item?.moduleId));
      scheduled.sort((left, right) => byteCompare(left.absolute, right.absolute));
      if (new Set(scheduled.map((item) => item.absolute)).size !== scheduled.length) {{
        throw new Error('duplicate scheduled module');
      }}
      this.scheduled = scheduled;
    }} catch (_error) {{
      this.invalidate('invalid-scheduled-modules');
    }}
  }}
  onTestModuleQueued(testModule) {{ this.recordStage('queued', testModule); }}
  onTestModuleCollected(testModule) {{
    this.recordStage('collected', testModule);
    if (!this.collectionReported) {{
      this.collectionReported = true;
      progress('collection-complete');
    }}
  }}
  onTestModuleStart(testModule) {{ this.recordStage('started', testModule); }}
  captureModule(testModule) {{
    const identity = moduleIdentity(testModule?.moduleId);
    if (typeof testModule?.errors !== 'function') {{
      throw new Error('module errors are unavailable');
    }}
    const errors = boundedErrors(testModule.errors());
    if (typeof testModule?.children?.allTests !== 'function') {{
      throw new Error('module tests are unavailable');
    }}
    const tests = [];
    for (const test of testModule.children.allTests()) {{
      if (tests.length >= MAX_TESTS) throw new Error('test bound exceeded');
      const name = test?.fullName;
      if (typeof name !== 'string' || !name || name.length > MAX_STRING) {{
        throw new Error('invalid test name');
      }}
      if (typeof test?.result !== 'function') throw new Error('test result is unavailable');
      const result = test.result();
      if (!result || typeof result !== 'object' || typeof result.state !== 'string') {{
        throw new Error('invalid test result');
      }}
      const failureMessages = boundedErrors(result.errors);
      tests.push({{
        moduleId: identity.relative,
        name,
        identity: identity.relative + '::' + name,
        status: result.state,
        failureMessages,
      }});
    }}
    tests.sort((left, right) => byteCompare(left.identity, right.identity));
    if (new Set(tests.map((test) => test.identity)).size !== tests.length) {{
      throw new Error('duplicate test identity');
    }}
    const errorCount = errors.length + tests.reduce(
      (count, test) => count + test.failureMessages.length, 0
    );
    if (errorCount > MAX_ERRORS) throw new Error('module error bound exceeded');
    return freezeSnapshot({{
      moduleId: identity.relative,
      absoluteId: identity.absolute,
      errors,
      tests,
    }});
  }}
  onTestModuleEnd(testModule) {{
    try {{
      const snapshot = this.captureModule(testModule);
      if (!this.scheduled.some((item) => item.absolute === snapshot.absoluteId)) {{
        this.stageFlags.ended.unexpected = true;
        this.invalidate('unscheduled-completed-module');
      }} else if (this.stages.ended.has(snapshot.absoluteId)) {{
        this.stageFlags.ended.duplicate = true;
        this.invalidate('duplicate-completed-module');
      }} else if (this.completed.has(snapshot.absoluteId)) {{
        this.stageFlags.ended.duplicate = true;
        this.invalidate('duplicate-completed-module');
      }} else {{
        const total = [...this.completed.values()].reduce(
          (count, item) => count + item.tests.length, snapshot.tests.length
        );
        if (total > MAX_TESTS) this.invalidate('test-count-overflow');
        else {{
          this.stages.ended.set(snapshot.absoluteId, {{
            absolute: snapshot.absoluteId,
            relative: snapshot.moduleId,
          }});
          this.completed.set(snapshot.absoluteId, snapshot);
        }}
      }}
    }} catch (_error) {{
      this.stageFlags.ended.unexpected = true;
      this.invalidate('invalid-completed-module');
    }}
    progress('module-complete');
  }}
  onTestRunEnd(testModules = [], unhandledErrors = [], reason = 'failed') {{
    let terminal = [];
    if (!['passed', 'failed', 'interrupted'].includes(reason)) {{
      this.invalidate('invalid-terminal-reason');
      reason = 'failed';
    }}
    let unhandled = [];
    try {{
      unhandled = boundedErrors(unhandledErrors);
    }} catch (_error) {{
      this.invalidate('invalid-unhandled-errors');
    }}
    try {{
      if (!Array.isArray(testModules) || testModules.length > MAX_MODULES) {{
        throw new Error('invalid terminal modules');
      }}
      terminal = testModules.map((item) => this.captureModule(item));
      terminal.sort((left, right) => byteCompare(left.absoluteId, right.absoluteId));
      if (new Set(terminal.map((item) => item.absoluteId)).size !== terminal.length) {{
        throw new Error('duplicate terminal module');
      }}
    }} catch (_error) {{
      terminal = [];
      this.invalidate('invalid-terminal-modules');
    }}
    const scheduledIds = this.scheduled.map((item) => item.absolute);
    const queued = this.stageValues('queued');
    const collected = this.stageValues('collected');
    const started = this.stageValues('started');
    const ended = this.stageValues('ended');
    const callbackStages = [queued, collected, started, ended];
    const completed = [...this.completed.values()].sort(
      (left, right) => byteCompare(left.absoluteId, right.absoluteId)
    );
    const completedIds = completed.map((item) => item.absoluteId);
    const structuralErrors = new Set();
    const stageValues = {{queued, collected, started, ended}};
    for (const name of ['queued', 'collected', 'started', 'ended']) {{
      const stageIds = stageValues[name].map((item) => item.absolute);
      const missing = scheduledIds.some((id) => !stageIds.includes(id))
        || (name === 'ended' && scheduledIds.some((id) => !completedIds.includes(id)));
      const unexpected = stageIds.some((id) => !scheduledIds.includes(id))
        || (name === 'ended' && completedIds.some((id) => !scheduledIds.includes(id)))
        || this.stageFlags[name].unexpected;
      if (missing) structuralErrors.add(name + '-missing');
      if (unexpected) structuralErrors.add(name + '-unexpected');
      if (this.stageFlags[name].duplicate) structuralErrors.add(name + '-duplicate');
    }}
    if (terminal.length) {{
      const terminalIds = terminal.map((item) => item.absoluteId);
      if (completedIds.some((id) => !terminalIds.includes(id))) {{
        structuralErrors.add('terminal-missing');
      }}
      if (terminalIds.some((id) => !completedIds.includes(id))) {{
        structuralErrors.add('terminal-unexpected');
      }}
      if (sameArray(completedIds, terminalIds)) {{
        for (let index = 0; index < terminal.length; index += 1) {{
          if (JSON.stringify(terminal[index]) !== JSON.stringify(completed[index])) {{
            structuralErrors.add('terminal-completed-divergence');
            break;
          }}
        }}
      }}
    }}
    const tests = completed.flatMap((item) => item.tests);
    tests.sort((left, right) => byteCompare(left.identity, right.identity));
    if (tests.length > MAX_TESTS || new Set(tests.map((item) => item.identity)).size !== tests.length) {{
      this.invalidate('invalid-completed-tests');
    }}
    const moduleErrors = completed.flatMap((item) => item.errors).sort(byteCompare);
    const failureCount = tests.reduce(
      (count, test) => count + test.failureMessages.length, 0
    );
    if (moduleErrors.length + unhandled.length + failureCount > MAX_ERRORS) {{
      this.invalidate('error-count-overflow');
    }}
    const diagnosticCodes = new Set([...structuralErrors, ...this.reporterErrors]);
    this.reporterErrors = ERROR_PRIORITY.filter((code) => diagnosticCodes.has(code));
    const proof = (
      this.reporterErrors.length === 0 && scheduledIds.length > 0
      && callbackStages.every((stage) => sameArray(
        scheduledIds, stage.map((item) => item.absolute)
      ))
      && sameArray(scheduledIds, completedIds) && tests.length > 0
      && moduleErrors.length === 0 && unhandled.length === 0
      && tests.every((test) => (
        test.status === 'passed' && test.failureMessages.length === 0
      ))
    );
    const ambientExitCode = (
      Number.isSafeInteger(process.exitCode)
      && process.exitCode >= 1 && process.exitCode <= 255
    ) ? process.exitCode : 0;
    const falseSentinelPass = (
      proof && terminal.length === 0 && reason === 'failed' && ambientExitCode === 1
    );
    const normalPass = (
      proof && terminal.length > 0 && reason === 'passed' && ambientExitCode === 0
    );
    const exitCode = (falseSentinelPass || normalPass) ? 0 : (ambientExitCode || 1);
    process.exitCode = exitCode;
    const payload = {{
      schema: SCHEMA,
      lifecycle: {{
        reason,
        proof,
        ambientExitCode,
        exitCode,
        scheduled: this.scheduled.map((item) => item.relative),
        completed: completed.map((item) => item.moduleId),
        terminal: terminal.map((item) => item.moduleId),
        queued: queued.map((item) => item.relative),
        collected: collected.map((item) => item.relative),
        started: started.map((item) => item.relative),
        ended: ended.map((item) => item.relative),
        stageFlags: {{
          queued: {{...this.stageFlags.queued}},
          collected: {{...this.stageFlags.collected}},
          started: {{...this.stageFlags.started}},
          ended: {{...this.stageFlags.ended}},
        }},
      }},
      errors: {{
        module: moduleErrors,
        unhandled,
        reporter: this.reporterErrors,
      }},
      modules: completed.map((item) => ({{
        moduleId: item.moduleId,
        testCount: item.tests.length,
        errorCount: item.errors.length,
      }})),
      tests,
    }};
    Object.freeze(payload);
    progress('result-published');
    writeAll(
      'PDD-VITEST-RESULT-V1 ' + JSON.stringify(payload) + '\\n'
    );
    coordinatorExit(exitCode);
  }}
}}
"""


def _vitest_worker_preload_source(
    result_fd: int, device: int | None = None, inode: int | None = None,
) -> str:
    """Close every inherited checker observation descriptor in a worker."""
    device_source = (
        f"{device}n" if device is not None
        else "identity('PDD_FRAMEWORK_OBSERVATION_DEVICE')"
    )
    inode_source = (
        f"{inode}n" if inode is not None
        else "identity('PDD_FRAMEWORK_OBSERVATION_INODE')"
    )
    return f"""'use strict';
const fs = require('node:fs');
const RESULT_FD = {result_fd};
function identity(name) {{
  const value = process.env[name];
  if (!value || !/^(0|[1-9][0-9]*)$/.test(value)) {{
    throw new Error('trusted Vitest result descriptor identity is missing');
  }}
  return BigInt(value);
}}
const EXPECTED_DEVICE = {device_source};
const EXPECTED_INODE = {inode_source};
function descriptorTable() {{
  try {{
    return fs.readdirSync('/proc/self/fd')
      .filter((value) => /^(0|[1-9][0-9]*)$/.test(value))
      .map(Number);
  }} catch (error) {{
    if (!error || !['ENOENT', 'ENOTDIR'].includes(error.code)) throw error;
    return Array.from({{ length: 256 }}, (_value, fd) => fd);
  }}
}}
function matches(fd) {{
  try {{
    const observed = fs.fstatSync(fd, {{ bigint: true }});
    return observed.isFIFO()
      && observed.dev === EXPECTED_DEVICE
      && observed.ino === EXPECTED_INODE;
  }} catch (error) {{
    if (error && ['EBADF', 'ENOENT'].includes(error.code)) return false;
    throw error;
  }}
}}
try {{
  const primary = fs.fstatSync(RESULT_FD, {{ bigint: true }});
  if (!primary.isFIFO()
      || primary.dev !== EXPECTED_DEVICE
      || primary.ino !== EXPECTED_INODE) {{
    throw new Error('trusted Vitest result descriptor identity mismatch');
  }}
  fs.writeSync(RESULT_FD, 'PDD-VITEST-PROGRESS-V1 worker-start\\n');
}} catch (error) {{
  if (!error || !['EBADF', 'ENOENT'].includes(error.code)) throw error;
}}
for (const fd of new Set(descriptorTable())) {{
  if (!matches(fd)) continue;
  try {{ fs.closeSync(fd); }} catch (error) {{
    if (!error || !['EBADF', 'ENOENT'].includes(error.code)) throw error;
  }}
}}
for (const fd of new Set(descriptorTable())) {{
  if (matches(fd)) {{
    throw new Error('trusted Vitest result descriptor remained in worker');
  }}
}}
"""


def _drain_result_pipe(
    read_fd: int, finished: threading.Event, result: dict[str, object]
) -> None:
    """Drain the observation FIFO while the child runs, discarding over-cap bytes."""
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
                finished.wait(.01)
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
    """Run Vitest with a bounded checker-created framework observation channel."""
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
        config_path, config_data = _vitest_config(root, "HEAD")
        _vitest_config_references(config_data)
    except ValueError as exc:
        return RunnerExecution("vitest", EvidenceOutcome.ERROR, "vitest-config", str(exc)), ()
    with tempfile.TemporaryDirectory(prefix="pdd-trusted-vitest-") as directory:
        temporary = Path(directory)
        scratch = temporary / "scratch"
        home = scratch / "home"
        home.mkdir(parents=True, mode=0o700)
        output = temporary / "results.json"
        reporter = temporary / f"reporter-{os.urandom(16).hex()}.mjs"
        read_fd, write_fd = os.pipe()
        os.set_blocking(read_fd, False)
        drain_finished = threading.Event()
        drained: dict[str, object] = {}
        drain_thread = threading.Thread(
            target=_drain_result_pipe, args=(read_fd, drain_finished, drained), daemon=True
        )
        drain_thread.start()
        result_fd = 198
        reporter.write_text(_vitest_reporter_source(result_fd), encoding="utf-8")
        worker_preload = temporary / "worker-preload.cjs"
        worker_preload.write_text(
            _vitest_worker_preload_source(result_fd),
            encoding="utf-8",
        )
        command = [
            str(phase_toolchain.launcher),
            *( ("--disable-wasm-trap-handler",) if sys.platform.startswith("linux") else () ),
            str(phase_toolchain.entrypoint),
            "run",
            *(path.as_posix() for path in paths),
            f"--config={root / config_path}",
            f"--reporter={reporter}",
            "--pool=forks",
            f"--execArgv=--require={worker_preload}",
        ]
        digest = hashlib.sha256(json.dumps(command, separators=(",", ":")).encode()).hexdigest()
        before = _validator_tree_identity(root)
        try:
            cache_roots = tuple(
                path for path in (
                    root / "node_modules/.vite-temp", root / "node_modules/.vite"
                ) if path.is_dir()
            )
            try:
                result, surviving = run_supervised(
                    command,
                    cwd=root,
                    timeout=timeout_seconds,
                    env=_vitest_environment(home),
                    limits=_VITEST_SUPERVISOR_LIMITS,
                    writable_roots=(scratch, *cache_roots),
                    readable_roots=(
                        reporter, worker_preload, *phase_toolchain.readable_roots
                    ),
                    readable_bindings=phase_toolchain.readable_bindings,
                    immutable_binding_proofs=phase_toolchain.immutable_binding_proofs,
                    result_write_fd=write_fd,
                    result_fd=result_fd,
                )
            finally:
                os.close(write_fd)
        except (OSError, UnicodeError, ValueError) as exc:
            drain_finished.set()
            drain_thread.join(timeout=1)
            os.close(read_fd)
            return RunnerExecution("vitest", EvidenceOutcome.ERROR, digest, f"Vitest launch failed: {exc}"), ()
        drain_finished.set()
        drain_thread.join(timeout=2)
        os.close(read_fd)
        termination = getattr(result, "termination", None)
        progress: tuple[VitestProgressStage, ...] = ()
        if (
            isinstance(termination, SupervisorTermination)
            and termination.kind is TerminationKind.SANDBOX_ERROR
        ):
            if (
                "error" not in drained
                and not drained.get("overflow")
                and isinstance(drained.get("data", b""), bytes)
            ):
                try:
                    _payload, progress = _parse_vitest_transport(
                        drained.get("data", b"")
                    )
                except ValueError:
                    progress = ()
            outcome, detail = _vitest_infrastructure_termination(
                result, timeout_seconds, progress=progress,
            )
            return RunnerExecution("vitest", outcome, digest, detail), ()
        try:
            if "error" in drained:
                raise drained["error"]
            if drained.get("overflow"):
                return RunnerExecution(
                    "vitest", EvidenceOutcome.ERROR, digest,
                    "Vitest result transport exceeded byte limit",
                ), ()
            output_data, progress = _parse_vitest_transport(
                drained.get("data", b"")
            )
            output.write_bytes(output_data)
        except (OSError, ValueError) as exc:
            return RunnerExecution(
                "vitest", EvidenceOutcome.ERROR, digest,
                "Vitest progress transport failed: " + str(exc),
            ), ()
        if surviving:
            return RunnerExecution("vitest", EvidenceOutcome.ERROR, digest, "Vitest left a surviving process-group descendant"), ()
        output_data = output.read_bytes()
        if result.returncode in {126, 127} and not output_data:
            return RunnerExecution("vitest", EvidenceOutcome.ERROR, digest, "Vitest launcher is missing or not executable"), ()
        termination_kind = getattr(getattr(termination, "kind", None), "value", None)
        if termination_kind == "timeout" or result.returncode == 124:
            outcome, detail = _vitest_infrastructure_termination(
                result, timeout_seconds, progress=progress,
            )
            return RunnerExecution("vitest", outcome, digest, detail), ()
        if result.returncode and not output_data:
            outcome, detail = _vitest_infrastructure_termination(
                result, timeout_seconds, progress=progress,
            )
            return RunnerExecution("vitest", outcome, digest, detail), ()
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
    executable = Path(command[0]).expanduser()
    entrypoint = Path(command[1]).expanduser()
    if not executable.is_file() or not os.access(executable, os.X_OK):
        return "Playwright launch executable is missing or not executable"
    if not entrypoint.is_file():
        return "Playwright launch entrypoint is missing or is not a file"
    return None


def _playwright_candidate_toolchain(root: Path) -> bool:
    """Return whether candidate checkout infrastructure would affect Playwright."""
    node_modules = root / "node_modules"
    return (
        (node_modules / "@playwright" / "test").exists()
        or (node_modules / "playwright-core" / ".local-browsers").exists()
    )


def _playwright_node_modules_destination_error(root: Path) -> str | None:
    """Reject destination topology that could redirect the trusted package mount."""
    destination = root / "node_modules"
    if not os.path.lexists(destination):
        return None
    try:
        metadata = destination.lstat()
    except OSError as exc:
        return f"candidate node_modules destination is unreadable: {exc}"
    if stat.S_ISLNK(metadata.st_mode):
        return "candidate node_modules destination is a symlink"
    if not stat.S_ISDIR(metadata.st_mode):
        return "candidate node_modules destination is not a real directory"
    return "candidate node_modules destination already exists"


def _playwright_nested_node_modules_error(root: Path) -> str | None:
    """Reject candidate package trees before trusted toolchain validation."""
    nested = next(root.rglob("node_modules"), None)
    if nested is None:
        return None
    return (
        "candidate nested node_modules destination is not trusted: "
        f"{nested.relative_to(root).as_posix()}"
    )


def _create_playwright_node_modules_mountpoint(root: Path) -> tuple[Path, int, int]:
    """Create one checker-owned target after exact-tree trust validation."""
    destination = root / "node_modules"
    try:
        destination.mkdir(mode=0o700)
        metadata = destination.lstat()
    except OSError as exc:
        raise ValueError("cannot create trusted node_modules mountpoint") from exc
    if (
        not stat.S_ISDIR(metadata.st_mode)
        or stat.S_ISLNK(metadata.st_mode)
        or metadata.st_uid != os.getuid()
    ):
        raise ValueError("trusted node_modules mountpoint identity is invalid")
    return destination, metadata.st_dev, metadata.st_ino


def _remove_playwright_node_modules_mountpoint(
    identity: tuple[Path, int, int],
) -> None:
    """Remove only the unchanged empty checker-owned binding target."""
    destination, expected_device, expected_inode = identity
    try:
        metadata = destination.lstat()
        if (
            not stat.S_ISDIR(metadata.st_mode)
            or stat.S_ISLNK(metadata.st_mode)
            or metadata.st_uid != os.getuid()
            or (metadata.st_dev, metadata.st_ino)
            != (expected_device, expected_inode)
            or any(destination.iterdir())
        ):
            raise ValueError("trusted node_modules mountpoint changed")
        destination.rmdir()
    except OSError as exc:
        raise ValueError("cannot remove trusted node_modules mountpoint") from exc


def _playwright_environment(
    home: Path, dependencies: Path | None, browser_runtime: Path | None = None
) -> dict[str, str]:
    """Return an isolated credential-free environment for Playwright."""
    environment = untrusted_child_environment(
        home=home,
        extra={"NODE_ENV": "test"},
        drop={"NODE_PATH", "PLAYWRIGHT_BROWSERS_PATH"},
    )
    if dependencies is not None and browser_runtime is not None:
        environment["NODE_PATH"] = str(dependencies)
        environment["PLAYWRIGHT_BROWSERS_PATH"] = str(browser_runtime)
    return environment


def _playwright_reporter_source(result_fd: int) -> str:
    """Return the checker-owned reporter for the observation descriptor."""
    return f"""const fs = require('fs');
const path = require('path');
const RESULT_FD = {result_fd};
const REPORTER_ERROR = 'invalid_reporter_state';
const REPORTER_ERROR_REASONS = new Set([
  'invalid_suite', 'suite_all_tests_access', 'suite_all_tests_call',
  'invalid_title_path',
  'title_path_call', 'invalid_project_title', 'project_access', 'project_call',
  'invalid_location', 'location_access', 'path_operation', 'duplicate_identity',
  'invalid_test_result', 'unknown_test', 'invalid_framework_error',
  'framework_error', 'invalid_run_result', 'serialization_failure', 'write_failure',
]);
const ERROR_RECEIPTS = Object.freeze({{
  invalid_suite: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"invalid_suite"}}',
  suite_all_tests_access: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"suite_all_tests_access"}}',
  suite_all_tests_call: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"suite_all_tests_call"}}',
  invalid_title_path: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"invalid_title_path"}}',
  title_path_call: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"title_path_call"}}',
  invalid_project_title: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"invalid_project_title"}}',
  project_access: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"project_access"}}',
  project_call: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"project_call"}}',
  invalid_location: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"invalid_location"}}',
  location_access: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"location_access"}}',
  path_operation: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"path_operation"}}',
  duplicate_identity: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"duplicate_identity"}}',
  invalid_test_result: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"invalid_test_result"}}',
  unknown_test: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"unknown_test"}}',
  invalid_framework_error: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"invalid_framework_error"}}',
  framework_error: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"framework_error"}}',
  invalid_run_result: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"invalid_run_result"}}',
  serialization_failure: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"serialization_failure"}}',
  write_failure: '{{"pdd_playwright_reporter":1,"reporter_error":"invalid_reporter_state","reason":"write_failure"}}',
}});
const EXECUTION_STATUSES = new Set(['passed', 'failed', 'skipped', 'timedOut', 'interrupted']);
class PddFrameworkReporter {{
  constructor() {{
    this.tests = new Map();
    this.reporterError = null;
    this.frameworkError = false;
  }}
  version() {{ return 'v2'; }}
  invalidate(reason) {{
    if (this.reporterError) return;
    this.reporterError = REPORTER_ERROR_REASONS.has(reason)
      ? reason : 'serialization_failure';
    this.tests = null;
  }}
  identity(test) {{
    if (!test || typeof test !== 'object') return {{reason: 'invalid_title_path'}};
    let titlePathFunction;
    try {{ titlePathFunction = test.titlePath; }} catch (_error) {{
      return {{reason: 'title_path_call'}};
    }}
    if (typeof titlePathFunction !== 'function') return {{reason: 'invalid_title_path'}};
    let titlePath;
    try {{ titlePath = titlePathFunction.call(test); }} catch (_error) {{
      return {{reason: 'title_path_call'}};
    }}
    if (!Array.isArray(titlePath) || titlePath.length < 4
        || titlePath[0] !== '' || !titlePath.every((item) => typeof item === 'string')) {{
      return {{reason: 'invalid_title_path'}};
    }}
    const [, titleProject, titleFile, ...titles] = titlePath;
    let parent;
    let projectFunction;
    let projectObject;
    let project;
    try {{
      parent = test.parent;
      projectFunction = parent && parent.project;
    }} catch (_error) {{ return {{reason: 'project_access'}}; }}
    if (typeof projectFunction !== 'function') {{
      return {{reason: 'invalid_project_title'}};
    }}
    try {{ projectObject = projectFunction.call(parent); }} catch (_error) {{
      return {{reason: 'project_call'}};
    }}
    try {{ project = projectObject && projectObject.name; }} catch (_error) {{
      return {{reason: 'project_access'}};
    }}
    if (typeof project !== 'string' || project !== titleProject
        || !titles.length || titles.some((title) => !title)
        || [project, titleFile, ...titles].some((item) => item.includes('::')
          || item.includes(' > ') || /[\\0\\r\\n]/.test(item) || item.length > 1024)) {{
      return {{reason: 'invalid_project_title'}};
    }}
    let location;
    let locationFile;
    try {{
      location = test.location;
      locationFile = location && location.file;
    }} catch (_error) {{ return {{reason: 'location_access'}}; }}
    if (typeof locationFile !== 'string') {{
      return {{reason: 'invalid_location'}};
    }}
    let absolute;
    let file;
    let basename;
    try {{
      absolute = path.isAbsolute(locationFile);
      file = path.relative(process.cwd(), locationFile);
      basename = path.basename(file);
    }} catch (_error) {{ return {{reason: 'path_operation'}}; }}
    if (!absolute) return {{reason: 'invalid_location'}};
    if (!file || path.isAbsolute(file) || file === '..'
        || file.startsWith(`..${{path.sep}}`) || basename !== titleFile
        || file.includes('::') || /[\\0\\r\\n]/.test(file) || file.length > 4096) {{
      return {{reason: 'invalid_location'}};
    }}
    return {{value: `${{project}}::${{file}}::${{titles.join(' > ')}}`}};
  }}
  onBegin(suite) {{
    if (this.reporterError) return;
    if (!suite || typeof suite !== 'object') {{
      this.invalidate('invalid_suite');
      return;
    }}
    let allTestsFunction;
    try {{ allTestsFunction = suite.allTests; }} catch (_error) {{
      this.invalidate('suite_all_tests_access');
      return;
    }}
    if (typeof allTestsFunction !== 'function') {{
      this.invalidate('invalid_suite');
      return;
    }}
    let allTests;
    try {{
      allTests = allTestsFunction.call(suite);
    }} catch (_error) {{
      this.invalidate('suite_all_tests_call');
      return;
    }}
    if (!Array.isArray(allTests)) {{
      this.invalidate('suite_all_tests_call');
      return;
    }}
    try {{
      const collected = new Map();
      for (const test of allTests) {{
        const observed = this.identity(test);
        if (!observed.value) {{ this.invalidate(observed.reason); return; }}
        const identity = observed.value;
        if (collected.has(identity)) {{ this.invalidate('duplicate_identity'); return; }}
        collected.set(identity, {{status: 'collected'}});
      }}
      this.tests = collected;
    }} catch (_error) {{
      this.invalidate('suite_all_tests_call');
    }}
  }}
  onTestEnd(test, result) {{
    if (this.reporterError) return;
    try {{
      const observed = this.identity(test);
      if (!observed.value) {{ this.invalidate(observed.reason); return; }}
      const identity = observed.value;
      if (!this.tests.has(identity)) {{ this.invalidate('unknown_test'); return; }}
      if (!result || typeof result !== 'object'
          || !EXECUTION_STATUSES.has(result.status)) {{
        this.invalidate('invalid_test_result');
        return;
      }}
      let error = '';
      if (result.error !== undefined && result.error !== null) {{
        if (typeof result.error !== 'object'
            || typeof result.error.message !== 'string') {{
          this.invalidate('invalid_test_result');
          return;
        }}
        error = result.error.message.slice(0, 4096);
      }}
      this.tests.set(identity, {{status: result.status, error}});
    }} catch (_error) {{
      this.invalidate('invalid_test_result');
    }}
  }}
  onError(error) {{
    if (this.reporterError) return;
    try {{
      if (!error || typeof error !== 'object' || typeof error.message !== 'string') {{
        this.invalidate('invalid_framework_error');
        return;
      }}
    }} catch (_error) {{
      this.invalidate('invalid_framework_error');
      return;
    }}
    this.frameworkError = true;
  }}
  writeErrorReceipt() {{
    const receipt = ERROR_RECEIPTS[this.reporterError]
      || ERROR_RECEIPTS.serialization_failure;
    try {{ fs.writeSync(RESULT_FD, receipt); }} catch (_error) {{}}
  }}
  onEnd(result) {{
    if (this.reporterError) {{ this.writeErrorReceipt(); return; }}
    let status;
    try {{ status = result && result.status; }} catch (_error) {{
      this.invalidate('invalid_run_result');
      this.writeErrorReceipt();
      return;
    }}
    if (!new Set(['passed', 'failed', 'timedout', 'interrupted']).has(status)) {{
      this.invalidate('invalid_run_result');
      this.writeErrorReceipt();
      return;
    }}
    if (this.frameworkError && status !== 'passed') {{
      this.invalidate('framework_error');
      this.writeErrorReceipt();
      return;
    }}
    try {{
      const tests = Array.from(
        this.tests, ([identity, result]) => ({{identity, ...result}})
      );
      const receipt = JSON.stringify({{pdd_playwright_reporter: 1, tests}});
      if (typeof receipt !== 'string') {{
        this.invalidate('serialization_failure');
        this.writeErrorReceipt();
        return;
      }}
      const written = fs.writeSync(RESULT_FD, receipt);
      if (written !== Buffer.byteLength(receipt)) {{
        this.invalidate('write_failure');
        this.writeErrorReceipt();
      }}
    }} catch (_error) {{
      this.invalidate('serialization_failure');
      this.writeErrorReceipt();
    }}
  }}
}}
module.exports = PddFrameworkReporter;
"""


def _playwright_missing_result_detail(
    result: subprocess.CompletedProcess[str],
) -> str:
    """Summarize a failed reporter launch without unbounded child output."""
    diagnostic = " ".join(result.stderr.split())
    if len(diagnostic) > 512:
        diagnostic = diagnostic[:509] + "..."
    detail = f"Playwright reporter produced no observation (exit {result.returncode})"
    return f"{detail}: {diagnostic}" if diagnostic else detail


def _playwright_infrastructure_termination(
    result: subprocess.CompletedProcess[str], collection: bool,
) -> tuple[EvidenceOutcome, str] | None:
    """Admit reporter interpretation only after authenticated ordinary exit."""
    termination = getattr(result, "termination", None)
    kind = getattr(termination, "kind", None)
    phase = "collection" if collection else "execution"
    if kind is TerminationKind.EXIT:
        exit_code = getattr(termination, "exit_code", None)
        if type(exit_code) is int and exit_code == result.returncode:  # pylint: disable=unidiomatic-typecheck
            return None
        return EvidenceOutcome.ERROR, f"phase={phase}; Playwright trusted exit evidence is invalid"
    if kind is TerminationKind.TIMEOUT:
        return EvidenceOutcome.TIMEOUT, f"phase={phase}; Playwright supervisor timed out and descendants were reaped"
    if kind is TerminationKind.RESOURCE_LIMIT:
        resource = getattr(termination, "resource_limit", None) or "unknown"
        return EvidenceOutcome.ERROR, f"phase={phase}; Playwright supervisor resource limit: {resource}"
    if kind is TerminationKind.SIGNAL:
        number = getattr(termination, "signal_number", None)
        return EvidenceOutcome.ERROR, f"phase={phase}; Playwright terminated by trusted signal {number}"
    if kind is TerminationKind.SANDBOX_ERROR:
        return EvidenceOutcome.ERROR, f"phase={phase}; Playwright sandbox infrastructure failed"
    return EvidenceOutcome.ERROR, f"phase={phase}; Playwright trusted termination evidence is missing"


def _playwright_runtime_prefix(
    prefix: tuple[str, ...], _launcher: Path,
) -> tuple[str, ...]:
    """Return the trusted toolchain argv without checker-injected browser flags."""
    return prefix


def _playwright_reported_failure_detail(tests: list[dict[str, object]]) -> str:
    """Return one bounded reporter diagnostic for a failed protected test."""
    errors = [
        " ".join(error.split())
        for item in tests
        if isinstance((error := item.get("error")), str) and error.strip()
    ]
    if not errors:
        return "Playwright reported failed protected tests"
    diagnostic = errors[0]
    if len(diagnostic) > 2048:
        diagnostic = diagnostic[:1021] + "...<truncated>..." + diagnostic[-1012:]
    return f"Playwright reported failed protected tests: {diagnostic}"


def _playwright_timeout_detail(tests: list[dict[str, object]]) -> str:
    """Return one bounded reporter error for a Playwright test timeout."""
    errors = [
        " ".join(error.split())
        for item in tests
        if item.get("status") == "timedOut"
        and isinstance((error := item.get("error")), str)
        and error.strip()
    ]
    if not errors:
        return "Playwright reported a timed out protected test"
    diagnostic = errors[0]
    if len(diagnostic) > 1024:
        diagnostic = diagnostic[:509] + "...<truncated>..." + diagnostic[-500:]
    return f"Playwright reported a timed out protected test: {diagnostic}"


def _playwright_phase_detail(
    detail: str, result: subprocess.CompletedProcess[str], collection: bool,
) -> str:
    """Attach bounded phase and supervisor diagnostics to Playwright evidence."""
    phase = "collection" if collection else "execution"
    diagnostic = " ".join(result.stderr.split())
    if len(diagnostic) > 1024:
        diagnostic = diagnostic[:509] + "...<truncated>..." + diagnostic[-500:]
    value = f"phase={phase}; {detail}"
    return f"{value}; supervisor={diagnostic}" if diagnostic else value


def _playwright_result(
    root: Path, output: str, returncode: int, expected: tuple[str, ...] | None,
    collection: bool = False,
) -> tuple[EvidenceOutcome, str, tuple[str, ...]]:
    """Normalize JSON reporter output to project, file, title-path identities."""
    try:
        payload = json.loads(output)
        if not isinstance(payload, dict):
            raise ValueError("malformed Playwright reporter payload")
        marker = payload.get("pdd_playwright_reporter")
        tests: list[dict[str, object]]
        if "pdd_playwright_reporter" in payload:
            if type(marker) is not int or marker != 1:  # pylint: disable=unidiomatic-typecheck
                raise ValueError("malformed Playwright reporter payload")
            error_keys = {
                "pdd_playwright_reporter", "reporter_error", "reason"
            }
            if set(payload) == error_keys:
                if payload["reporter_error"] != "invalid_reporter_state":
                    raise ValueError("malformed Playwright reporter error")
                reasons = {
                    "invalid_suite", "suite_all_tests_access",
                    "suite_all_tests_call", "invalid_title_path",
                    "title_path_call", "invalid_project_title", "project_access",
                    "project_call", "invalid_location", "location_access",
                    "path_operation", "duplicate_identity", "invalid_test_result",
                    "unknown_test", "invalid_framework_error", "framework_error",
                    "invalid_run_result", "serialization_failure", "write_failure",
                }
                reason = payload["reason"]
                if not isinstance(reason, str) or reason not in reasons:
                    raise ValueError("malformed Playwright reporter error")
                return (
                    EvidenceOutcome.COLLECTION_ERROR,
                    "Playwright reporter rejected an invalid framework observation "
                    f"({reason})",
                    (),
                )
            if set(payload) != {"pdd_playwright_reporter", "tests"}:
                raise ValueError("malformed Playwright reporter payload")
            raw_tests = payload["tests"]
            if not isinstance(raw_tests, list):
                raise ValueError("malformed Playwright reporter payload")
            tests = raw_tests
            statuses = {
                "collected", "passed", "failed", "skipped", "timedOut", "interrupted"
            }
            for item in tests:
                if (
                    not isinstance(item, dict)
                    or set(item) not in (
                        {"identity", "status"}, {"identity", "status", "error"}
                    )
                    or not isinstance(item.get("identity"), str)
                    or not item["identity"]
                    or len(item["identity"]) > 8192
                    or not isinstance(item.get("status"), str)
                    or item["status"] not in statuses
                    or (
                        "error" in item
                        and (
                            not isinstance(item["error"], str)
                            or len(item["error"]) > 4096
                        )
                    )
                ):
                    raise ValueError("malformed Playwright reporter test")
        else:
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
                        if (
                            not isinstance(results, list)
                            or not results
                            or not all(isinstance(result, dict) for result in results)
                        ):
                            raise ValueError("malformed Playwright results")
                        attempts = {
                            result.get("status", "passed" if collection else "skipped")
                            for result in results
                        }
                        status = next(
                            (candidate for candidate in (
                                "timedOut", "failed", "interrupted", "skipped", "passed"
                            ) if candidate in attempts),
                            "skipped",
                        )
                        tests.append({
                            "identity": f"{item['projectName']}::{filename}::{title_path}",
                            "status": status,
                        })
                for child in suite.get("suites", []):
                    visit(child, next_parents)
            if "tests" in payload or not isinstance(payload.get("suites"), list):
                raise ValueError("untrusted Playwright result payload")
            for suite in payload["suites"]:
                visit(suite)
        if not isinstance(tests, list):
            raise ValueError("malformed Playwright reporter payload")
    except (KeyError, TypeError, ValueError, json.JSONDecodeError):
        return EvidenceOutcome.COLLECTION_ERROR, "Playwright reporter produced malformed JSON", ()
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
    if statuses - {"collected", "passed", "failed", "skipped", "timedOut", "interrupted"}:
        return EvidenceOutcome.COLLECTION_ERROR, "Playwright reporter emitted an unsupported status", identities
    if "timedOut" in statuses:
        return EvidenceOutcome.TIMEOUT, _playwright_timeout_detail(tests), identities
    if returncode or "failed" in statuses or "interrupted" in statuses:
        return (
            EvidenceOutcome.FAIL,
            _playwright_reported_failure_detail(tests),
            identities,
        )
    if "collected" in statuses:
        return EvidenceOutcome.SKIP, "Playwright did not execute every collected protected test", identities
    if statuses - {"passed"}:
        return EvidenceOutcome.SKIP, "Playwright reported skipped protected tests", identities
    return EvidenceOutcome.PASS, f"{len(identities)} protected Playwright tests passed", identities


def _playwright_execution_tree_identity(root: Path) -> str:
    """Bind every non-Git execution-tree entry, including ignored files."""
    digest = hashlib.sha256()
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        if relative.parts and relative.parts[0] == ".git":
            continue
        metadata = path.lstat()
        digest.update(relative.as_posix().encode() + b"\0")
        digest.update(str(metadata.st_mode).encode() + b"\0")
        if path.is_symlink():
            digest.update(os.readlink(path).encode())
        elif path.is_file():
            digest.update(path.read_bytes())
    return digest.hexdigest()


def _playwright_protected_worktree_identity(
    root: Path, ref: str, paths: tuple[PurePosixPath, ...],
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
) -> str:
    """Bind blob bytes and Git modes for the complete protected closure."""
    closure = _playwright_support_closure(
        root, ref, paths, code_under_test_paths
    )
    config_path, config_source = _playwright_config(root, ref)
    members = tuple(closure) + ((config_path, config_source),)
    digest = hashlib.sha256()
    for path, expected in sorted(members):
        actual = root / path
        if actual.is_symlink() or not actual.is_file():
            raise ValueError(
                f"Playwright closure member must be a regular non-symlink file: {path}"
            )
        digest.update(path.as_posix().encode() + b"\0")
        digest.update(read_git_mode(root, ref, path).encode() + b"\0")
        digest.update(expected + b"\0" + actual.read_bytes() + b"\0")
        executable = bool(actual.stat().st_mode & 0o111)
        if executable != (read_git_mode(root, ref, path) == "100755"):
            raise ValueError(f"Playwright closure member mode changed: {path}")
    return digest.hexdigest()


def _playwright_host_temp_parent() -> Path:
    """Return a writable host temp parent outside the sandbox's host-backed tmp."""
    try:
        parent = _PLAYWRIGHT_HOST_TEMP_PARENT.resolve(strict=True)
        sandbox_tmp = Path("/tmp").resolve(strict=True)
        parent_metadata = parent.stat()
    except OSError as exc:
        raise RuntimeError("trusted Playwright temp parent is unavailable") from exc
    if not stat.S_ISDIR(parent_metadata.st_mode) or not os.access(
        parent, os.W_OK | os.X_OK
    ):
        raise RuntimeError("trusted Playwright temp parent is not writable")
    if parent == sandbox_tmp or parent.is_relative_to(sandbox_tmp):
        raise RuntimeError("trusted Playwright temp parent aliases sandbox /tmp")
    return parent


class _PlaywrightTemporaryDirectory:
    """Normalize OSErrors from one checker-owned temporary directory lifecycle."""

    def __init__(self, prefix: str, parent: Path) -> None:
        self._prefix = prefix
        self._parent = parent
        self._stack = ExitStack()

    def __enter__(self) -> str:
        try:
            return self._stack.enter_context(
                tempfile.TemporaryDirectory(prefix=self._prefix, dir=self._parent)
            )
        except OSError as exc:
            raise _PlaywrightTemporaryDirectoryError(
                f"Playwright temporary directory failed: {exc}"
            ) from exc

    def __exit__(self, exc_type, exc_value, traceback) -> bool | None:
        try:
            return self._stack.__exit__(exc_type, exc_value, traceback)
        except OSError as exc:
            raise _PlaywrightTemporaryDirectoryError(
                f"Playwright temporary directory failed: {exc}"
            ) from exc


def _playwright_temporary_directory(
    prefix: str, parent: Path,
) -> _PlaywrightTemporaryDirectory:
    """Create one checker-owned temporary directory lifecycle wrapper."""
    return _PlaywrightTemporaryDirectory(prefix, parent)


def _normalize_playwright_temp_errors(outcome: EvidenceOutcome):
    """Return a decorator that turns checker temporary lifecycle failures into evidence."""
    def decorate(function):
        @wraps(function)
        def guarded(*args, **kwargs):
            try:
                return function(*args, **kwargs)
            except _PlaywrightTemporaryDirectoryError as exc:
                return RunnerExecution(
                    "playwright", outcome, _PLAYWRIGHT_TEMP_FAILURE_DIGEST, str(exc)
                ), ()
        return guarded
    return decorate


def _playwright_sandbox_destination_error(
    roles: PlaywrightToolchainRoles,
    native_bindings: tuple[tuple[Path, Path], ...],
) -> str | None:
    """Reject manifest destinations that collide with the bounded sandbox /tmp bind."""
    try:
        literal_sandbox_tmp = Path("/tmp")
        resolved_sandbox_tmp = literal_sandbox_tmp.resolve(strict=True)
        for destination in roles.readable_roots:
            if destination == resolved_sandbox_tmp or destination.is_relative_to(
                resolved_sandbox_tmp
            ):
                return (
                    "Playwright toolchain destination resolves into sandbox /tmp: "
                    f"{destination}"
                )
        for _source, destination in native_bindings:
            lexical = Path(os.path.normpath(destination))
            if lexical == literal_sandbox_tmp or lexical.is_relative_to(
                literal_sandbox_tmp
            ):
                return (
                    "Playwright toolchain destination lexically aliases sandbox /tmp: "
                    f"{destination}"
                )
            resolved_parent = destination.parent.resolve(strict=True)
            if resolved_parent == resolved_sandbox_tmp or resolved_parent.is_relative_to(
                resolved_sandbox_tmp
            ):
                return (
                    "Playwright toolchain destination parent resolves into sandbox /tmp: "
                    f"{destination}"
                )
    except OSError as exc:
        return f"cannot validate Playwright toolchain sandbox destinations: {exc}"
    return None


@_normalize_playwright_temp_errors(EvidenceOutcome.ERROR)
def _run_playwright_in_tree(
    root: Path, paths: tuple[PurePosixPath, ...], timeout_seconds: int,
    config: RunnerConfig, expected: tuple[str, ...] | None = None,
    command_root: Path | None = None, collection: bool = False,
    expected_commit: str | None = None,
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
) -> tuple[RunnerExecution, tuple[str, ...]]:
    """Execute exact paths through Playwright's bounded observation channel."""
    tool_root = command_root or root
    destination_error = _playwright_node_modules_destination_error(root)
    if destination_error is not None:
        return RunnerExecution(
            "playwright", EvidenceOutcome.ERROR,
            "playwright-untrusted", destination_error,
        ), ()
    nested_destination_error = _playwright_nested_node_modules_error(root)
    if nested_destination_error is not None:
        return RunnerExecution(
            "playwright", EvidenceOutcome.ERROR,
            "playwright-untrusted", nested_destination_error,
        ), ()
    if _playwright_candidate_toolchain(tool_root):
        return RunnerExecution("playwright", EvidenceOutcome.ERROR, "playwright-untrusted", "candidate node_modules Playwright toolchain is not trusted"), ()
    prefix = _playwright_command(config)
    if prefix is None:
        return RunnerExecution("playwright", EvidenceOutcome.ERROR, "playwright-unavailable", "no local Playwright CLI is available"), ()
    if config.playwright_toolchain_manifest is None:
        return RunnerExecution(
            "playwright", EvidenceOutcome.COLLECTION_ERROR,
            "playwright-untrusted", "Playwright toolchain manifest is required",
        ), ()
    try:
        current_identity = _playwright_toolchain_identity(
            tool_root, prefix, config.playwright_toolchain_manifest
        )
        toolchain_identity = config.playwright_toolchain_identity or current_identity
        if current_identity != toolchain_identity:
            raise ValueError("Playwright toolchain changed across protocol execution")
    except ValueError as exc:
        return RunnerExecution(
            "playwright", EvidenceOutcome.COLLECTION_ERROR,
            "playwright-untrusted", str(exc),
        ), ()
    command_error = _playwright_command_error(root, prefix)
    if command_error is not None:
        return RunnerExecution(
            "playwright", EvidenceOutcome.COLLECTION_ERROR,
            "playwright-untrusted", command_error,
        ), ()
    roles = _toolchain_manifest_roles(config.playwright_toolchain_manifest)
    native_bindings = roles.native_bindings
    runtime_prefix = _playwright_runtime_prefix(prefix, roles.launcher)
    destination_error = _playwright_sandbox_destination_error(
        roles, native_bindings
    )
    if destination_error is not None:
        return RunnerExecution(
            "playwright", EvidenceOutcome.COLLECTION_ERROR,
            "playwright-untrusted", destination_error,
        ), ()
    try:
        config_path, _source = _playwright_config(root, "HEAD")
    except ValueError as exc:
        return RunnerExecution("playwright", EvidenceOutcome.ERROR, "playwright-config", str(exc)), ()
    try:
        host_temp_parent = _playwright_host_temp_parent()
    except RuntimeError as exc:
        return RunnerExecution(
            "playwright", EvidenceOutcome.ERROR, "playwright-temp", str(exc)
        ), ()
    with _playwright_temporary_directory(
        "pdd-trusted-playwright-", host_temp_parent
    ) as directory:
        temporary = Path(directory)
        scratch = temporary / "scratch"
        home = scratch / "home"
        home.mkdir(parents=True, mode=0o700)
        sandbox_tmp = scratch / "tmp"
        sandbox_tmp.mkdir(mode=0o700)
        controllers = temporary / f"controller-{os.urandom(16).hex()}"
        controllers.mkdir(mode=0o700)
        reporter = controllers / "reporter.cjs"
        result_fd = 198
        reporter.write_text(_playwright_reporter_source(result_fd), encoding="utf-8")
        commit = expected_commit or subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=root, capture_output=True,
            text=True, check=True,
        ).stdout.strip()
        try:
            closure_identity = _playwright_protected_worktree_identity(
                root, commit, paths, code_under_test_paths
            )
            tree_identity = _playwright_execution_tree_identity(root)
            mountpoint_identity = _create_playwright_node_modules_mountpoint(root)
            dependency_destination = mountpoint_identity[0]
            canonical_entrypoint = dependency_destination / roles.entrypoint.relative_to(
                roles.dependencies
            )
            snapshot_binding_proofs = _playwright_snapshot_binding_proofs(
                reporter,
                roles,
                Path(runtime_prefix[0]),
                dependency_destination,
                native_bindings,
            )
            snapshot_identity, _snapshot_aggregate = (
                _playwright_snapshot_aggregate_identity(
                    snapshot_binding_proofs,
                    reporter,
                    roles,
                    Path(runtime_prefix[0]),
                    dependency_destination,
                    native_bindings,
                )
            )
            if snapshot_identity != toolchain_identity:
                raise ValueError(
                    "Playwright snapshot does not match the accepted toolchain identity"
                )
        except ValueError as exc:
            return RunnerExecution(
                "playwright", EvidenceOutcome.ERROR, "playwright-closure", str(exc)
            ), ()
        command = [
            runtime_prefix[0],
            str(canonical_entrypoint),
            "test", *(f"^{re.escape(str(root / path))}$" for path in paths),
            f"--config={root / config_path}", f"--reporter={reporter}",
            "--update-snapshots=none", f"--output={scratch / 'results'}",
        ]
        if collection:
            command.append("--list")
        digest = hashlib.sha256(
            json.dumps(command, separators=(",", ":")).encode()
        ).hexdigest()
        read_fd, write_fd = os.pipe()
        os.set_blocking(read_fd, False)
        drain_finished = threading.Event()
        drained: dict[str, object] = {}
        drain_thread = threading.Thread(
            target=_drain_result_pipe, args=(read_fd, drain_finished, drained), daemon=True
        )
        drain_thread.start()
        result, surviving = run_supervised(
            command,
            cwd=root,
            timeout=timeout_seconds,
            env=_playwright_environment(
                home,
                dependency_destination,
                roles.browser_runtime,
            ),
            writable_roots=(scratch,),
            writable_bindings=((sandbox_tmp, Path("/tmp")),),
            temp_directory=Path("/tmp"),
            readable_roots=(reporter, *roles.readable_roots),
            readable_bindings=(
                *native_bindings, (roles.dependencies, dependency_destination),
            ),
            snapshot_binding_proofs=snapshot_binding_proofs,
            playwright_snapshot_aggregate=_snapshot_aggregate,
            limits=PLAYWRIGHT_SUPERVISOR_LIMITS,
            result_write_fd=write_fd,
            result_fd=result_fd,
        )
        os.close(write_fd)
        drain_finished.set()
        drain_thread.join(timeout=2)
        try:
            if "error" in drained:
                raise drained["error"]
            if drained.get("overflow"):
                return RunnerExecution(
                    "playwright", EvidenceOutcome.ERROR, digest,
                    "Playwright result transport exceeded byte limit",
                ), ()
            output = drained.get("data", b"")
            if not isinstance(output, bytes):
                raise OSError("invalid Playwright result transport")
        except OSError as exc:
            return RunnerExecution(
                "playwright", EvidenceOutcome.ERROR, digest,
                f"Playwright result transport failed: {exc}",
            ), ()
        finally:
            os.close(read_fd)
        try:
            _remove_playwright_node_modules_mountpoint(mountpoint_identity)
        except ValueError as exc:
            return RunnerExecution(
                "playwright", EvidenceOutcome.ERROR, digest, str(exc)
            ), ()
        if surviving:
            return RunnerExecution(
                "playwright", EvidenceOutcome.ERROR, digest,
                "Playwright left surviving descendants after execution",
            ), ()
        infrastructure = _playwright_infrastructure_termination(result, collection)
        if infrastructure is not None:
            outcome, detail = infrastructure
            return RunnerExecution(
                "playwright", outcome, digest,
                _playwright_phase_detail(detail, result, collection),
            ), ()
        denied_write = result.returncode != 0 and any(
            marker in result.stderr
            for marker in ("Operation not permitted", "Permission denied")
        )
        current_commit = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=root, capture_output=True,
            text=True, check=False,
        )
        try:
            current_closure_identity = _playwright_protected_worktree_identity(
                root, commit, paths, code_under_test_paths
            )
        except ValueError:
            current_closure_identity = "invalid"
        modified = (
            current_commit.returncode != 0
            or current_commit.stdout.strip() != commit
            or current_closure_identity != closure_identity
            or _playwright_execution_tree_identity(root) != tree_identity
        )
        if modified or denied_write:
            return RunnerExecution(
                "playwright", EvidenceOutcome.ERROR, digest,
                "protected Playwright execution tree was modified",
            ), ()
    try:
        if _playwright_toolchain_identity(
            tool_root, prefix, config.playwright_toolchain_manifest
        ) != toolchain_identity:
            return RunnerExecution(
                "playwright", EvidenceOutcome.COLLECTION_ERROR, digest,
                "Playwright toolchain changed during execution",
            ), ()
    except ValueError as exc:
        return RunnerExecution(
            "playwright", EvidenceOutcome.COLLECTION_ERROR, digest, str(exc)
        ), ()
    if not output:
        return RunnerExecution(
            "playwright", EvidenceOutcome.COLLECTION_ERROR, digest,
            _playwright_missing_result_detail(result),
        ), ()
    outcome, detail, identities = _playwright_result(
        root, output.decode("utf-8", errors="replace"), result.returncode, expected, collection
    )
    return RunnerExecution(
        "playwright", outcome, digest,
        _playwright_phase_detail(detail, result, collection),
    ), identities


@_normalize_playwright_temp_errors(EvidenceOutcome.COLLECTION_ERROR)
def _run_playwright(
    root: Path, paths: tuple[PurePosixPath, ...], timeout_seconds: int,
    config: RunnerConfig, expected: tuple[str, ...] | None = None,
    command_root: Path | None = None, collection: bool = False,
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
) -> tuple[RunnerExecution, tuple[str, ...]]:
    """Run one protocol phase from a fresh exact-commit materialization."""
    source_root = root
    tool_root = command_root or root
    resolved = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=source_root, capture_output=True,
        text=True, check=False,
    )
    if resolved.returncode != 0:
        return RunnerExecution(
            "playwright", EvidenceOutcome.COLLECTION_ERROR,
            hashlib.sha256(b"invalid-playwright-ref").hexdigest(),
            "cannot resolve exact Playwright phase commit",
        ), ()
    commit = resolved.stdout.strip()
    try:
        host_temp_parent = _playwright_host_temp_parent()
    except RuntimeError as exc:
        return RunnerExecution(
            "playwright", EvidenceOutcome.COLLECTION_ERROR,
            hashlib.sha256(commit.encode()).hexdigest(), str(exc),
        ), ()
    with _playwright_temporary_directory(
        "pdd-playwright-phase-", host_temp_parent
    ) as directory:
        phase_root = Path(directory) / "repository"
        cloned = subprocess.run(
            ["git", "clone", "-q", "--no-local", "--no-checkout",
             str(source_root), str(phase_root)],
            capture_output=True, text=True, check=False,
        )
        checked = cloned.returncode == 0 and subprocess.run(
            ["git", "checkout", "-q", "--detach", commit], cwd=phase_root,
            capture_output=True, text=True, check=False,
        ).returncode == 0
        if not checked:
            return RunnerExecution(
                "playwright", EvidenceOutcome.COLLECTION_ERROR,
                hashlib.sha256(commit.encode()).hexdigest(),
                "cannot create fresh exact-commit Playwright phase tree",
            ), ()
        return _run_playwright_in_tree(
            phase_root, paths, timeout_seconds, config, expected,
            command_root=tool_root, collection=collection,
            expected_commit=commit,
            code_under_test_paths=code_under_test_paths,
        )


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
        worker = _trusted_execution_runner(
            controllers, root,
            [*pytest_args, f"--junitxml=/proc/self/fd/{result_fd}"],
        )
        result, surviving = _managed_subprocess(
            [sys.executable, "-P", str(worker)], cwd=controllers,
            timeout=timeout_seconds, env=_pytest_environment(home),
            writable_roots=(home.parent,), readable_roots=(root,),
            result_fifo=result_fifo, result_fd=result_fd,
        )
        drain_finished.set()
        drain_thread.join(timeout=2)
        os.close(read_fd)
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
        observation_output = drained.get("data", b"")
        if "error" in drained or drained.get("overflow") or not isinstance(
            observation_output, bytes
        ):
            return RunnerExecution(
                node_id, EvidenceOutcome.COLLECTION_ERROR, command_digest,
                "pytest bounded observation transport failed",
            )
        outcome, detail = _junit_outcome(
            observation_output, result.returncode, output, 1
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
    """Run protected-base Jest to observe framework test identities."""
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
    root: Path, base_sha: str, paths: tuple[PurePosixPath, ...], config: RunnerConfig,
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
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
            collection=True, code_under_test_paths=code_under_test_paths,
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
        base_execution, base_ids = _collect_playwright_at_base(
            root, base_sha, obligation.artifact_paths, config,
            obligation.code_under_test_paths,
        )
        if base_execution.outcome is not EvidenceOutcome.PASS:
            return RunnerExecution(obligation.obligation_id, base_execution.outcome, base_execution.command_digest, base_execution.detail)
        head_collection, _head_ids = _run_playwright(
            root, obligation.artifact_paths, config.timeout_seconds, config,
            base_ids, collection=True,
            code_under_test_paths=obligation.code_under_test_paths,
        )
        if head_collection.outcome is not EvidenceOutcome.PASS:
            return RunnerExecution(obligation.obligation_id, head_collection.outcome, head_collection.command_digest, head_collection.detail)
        head_execution, _head_ids = _run_playwright(
            root, obligation.artifact_paths, config.timeout_seconds, config, base_ids,
            code_under_test_paths=obligation.code_under_test_paths,
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
                    EvidenceOutcome.COLLECTION_ERROR
                    if command_error.startswith("Playwright launch")
                    else EvidenceOutcome.ERROR,
                    obligation.validator_config_digest,
                    command_error,
                )
        prefix = _playwright_command(config)
        if prefix is not None and config.playwright_toolchain_manifest is not None:
            try:
                identity = _playwright_toolchain_identity(
                    root, prefix, config.playwright_toolchain_manifest
                )
            except (OSError, ValueError) as exc:
                return RunnerExecution(
                    obligation.obligation_id,
                    EvidenceOutcome.COLLECTION_ERROR,
                    obligation.validator_config_digest,
                    str(exc),
                )
            if config.playwright_toolchain_identity is not None:
                if identity != config.playwright_toolchain_identity:
                    return RunnerExecution(
                        obligation.obligation_id,
                        EvidenceOutcome.COLLECTION_ERROR,
                        obligation.validator_config_digest,
                        "Playwright toolchain changed across protocol execution",
                    )
            else:
                config = replace(config, playwright_toolchain_identity=identity)
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
    prefix = _playwright_command(config)
    if prefix is not None and config.playwright_toolchain_manifest is not None:
        try:
            identity = _playwright_toolchain_identity(
                root, prefix, config.playwright_toolchain_manifest
            )
        except (OSError, ValueError):
            identity = None
        if identity is not None:
            config = replace(config, playwright_toolchain_identity=identity)
    executions = tuple(
        RunnerExecution(
            obligation.obligation_id,
            EvidenceOutcome.ERROR,
            profile.profile_digest,
            "isolated_black_box assurance requires an external SUT adapter; "
            f"the in-process {obligation.validator_id} adapter is unsupported",
        )
        if (
            profile.assurance is AssuranceLevel.ISOLATED_BLACK_BOX
            and obligation.validator_id in _IN_PROCESS_FRAMEWORK_ADAPTERS
        )
        else (
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
                ) if obligation.validator_id in {"jest", "vitest", "playwright"} else execution
                for obligation, execution in zip(profile.obligations, executions)
            )
    if (
        prefix is not None
        and config.playwright_toolchain_manifest is not None
        and config.playwright_toolchain_identity is not None
    ):
        try:
            final_identity = _playwright_toolchain_identity(
                root, prefix, config.playwright_toolchain_manifest
            )
        except (OSError, ValueError):
            final_identity = None
        if final_identity != config.playwright_toolchain_identity:
            executions = tuple(
                RunnerExecution(
                    obligation.obligation_id,
                    EvidenceOutcome.COLLECTION_ERROR,
                    execution.command_digest,
                    "Playwright toolchain changed across protocol execution",
                ) if obligation.validator_id == "playwright" else execution
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
        playwright_toolchain_identity=config.playwright_toolchain_identity,
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
