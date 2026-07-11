"""Trusted validator adapters and pass-only normalized evidence outcomes."""
# pylint: disable=too-many-lines,too-many-boolean-expressions,too-many-locals

from __future__ import annotations

import hashlib
import ast
import json
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
from .isolation import untrusted_child_environment
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
    for key in ("setupFiles", "setupFilesAfterEnv", "reporters", "projects"):
        value = config.get(key, [])
        if not isinstance(value, list):
            raise ValueError(f"Jest {key} must be an array")
        for item in value:
            target = item[0] if isinstance(item, list) and item else item
            if isinstance(target, str):
                path = _jest_local_path(target)
                if path is not None:
                    references.add(path)
    resolver = config.get("resolver")
    if resolver is not None:
        if not isinstance(resolver, str):
            raise ValueError("Jest resolver must be a string")
        path = _jest_local_path(resolver)
        if path is not None:
            references.add(path)
    transforms = config.get("transform", {})
    if not isinstance(transforms, dict):
        raise ValueError("Jest transform must be an object")
    for value in transforms.values():
        target = value[0] if isinstance(value, list) and value else value
        if isinstance(target, str):
            path = _jest_local_path(target)
            if path is not None:
                references.add(path)
        elif not isinstance(target, dict):
            raise ValueError("Jest transform entry must be a static path")
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
        r"(?:from\s+|import\s*\(|require\s*\()['\"](\.{1,2}/[^'\"]+)['\"]",
        text,
    )
    resolved: set[PurePosixPath] = set()
    for item in imports:
        candidate = source_path.parent / PurePosixPath(item)
        candidates = [candidate]
        if not candidate.suffix:
            candidates.extend(candidate.with_suffix(suffix) for suffix in (".js", ".cjs", ".mjs", ".ts", ".tsx", ".jsx", ".json"))
            candidates.extend(candidate / f"index{suffix}" for suffix in (".js", ".ts", ".tsx"))
        resolved.update(path for path in candidates if read_git_blob(root, ref, path) is not None)
    return resolved


def _jest_support_closure(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...]
) -> tuple[tuple[PurePosixPath, bytes], ...]:
    """Return static config and transitive local Jest support modules."""
    config_path, config = _jest_config(root, ref)
    paths = {config_path}
    pending = list(_jest_config_references(config))
    visited: set[PurePosixPath] = set()
    while pending:
        path = pending.pop()
        if path in visited:
            continue
        visited.add(path)
        source = read_git_blob(root, ref, path)
        if source is None:
            raise ValueError(f"Jest support path is missing: {path.as_posix()}")
        paths.add(path)
        pending.extend(_local_javascript_imports(root, ref, path, source) - visited)
    return tuple((path, read_git_blob(root, ref, path)) for path in sorted(paths) if read_git_blob(root, ref, path) is not None)


def jest_validator_config_digest(
    root: Path, ref: str, test_paths: tuple[PurePosixPath, ...]
) -> str:
    """Hash static Jest config and executable local support closure."""
    del test_paths
    digest = hashlib.sha256()
    for path, content in _jest_support_closure(root, ref, ()):
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
    profile: VerificationProfile, *, root: Path | None = None, ref: str = "HEAD"
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
            (_support_digest(root, ref, profile)[0] + _jest_support_digest(root, ref, profile)[0]).encode()
        ).hexdigest()
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


def _jest_command(root: Path, config: RunnerConfig) -> tuple[str, ...] | None:
    """Return an explicit local Jest argv prefix; never invoke an npm script."""
    if config.jest_command is not None:
        return config.jest_command
    node = shutil.which("node")
    binary = root / "node_modules" / "jest" / "bin" / "jest.js"
    if node is None or not binary.is_file():
        return None
    return (node, str(binary))


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
    command_prefix = _jest_command(root, config)
    if command_prefix is None:
        return RunnerExecution("jest", EvidenceOutcome.ERROR, "jest-unavailable", "no local Jest binary is available"), ()
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
    runner_digest = runner_identity_digest(profile, root=root, ref=binding.head_sha)
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
