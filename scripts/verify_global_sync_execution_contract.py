#!/usr/bin/env python3
"""Fail-closed semantic verification for the global-sync M0 contract.

The evidence ledger renderer protects bytes and promotion evidence.  This
companion deliberately checks the active execution metadata: commands that
look plausible in prose must resolve to real, correctly-parented interfaces.
"""
# pylint: disable=too-many-boolean-expressions,too-many-branches,too-many-locals,too-many-return-statements,too-many-statements,line-too-long

from __future__ import annotations

import argparse
import importlib.util
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable

import yaml


STATES = frozenset({"EXISTS", "TO_BUILD", "EXTERNAL_PROTECTED", "ARCHIVED"})
MILESTONES = ["M0", "M1", "M2", "M3", "M4", "M5"]
SHA1 = re.compile(r"^[0-9a-f]{40}$")
PLAN_TO_BUILD = {
    "pdd.sync_core.vertical_slice_verifier": (
        "vertical-slice-verifier", ["python", "-m", "pdd.sync_core.vertical_slice_verifier"]
    ),
    "pdd.sync_core.production_routing_verifier": (
        "production-routing-verifier", ["python", "-m", "pdd.sync_core.production_routing_verifier"]
    ),
    "pdd.sync_core.scan_verifier": (
        "scan-verifier", ["python", "-m", "pdd.sync_core.scan_verifier"]
    ),
    "pdd.sync_core.consumer_ownership_verifier": (
        "consumer-ownership-verifier", ["python", "-m", "pdd.sync_core.consumer_ownership_verifier"]
    ),
    "pdd.sync_core.nightly_ledger_verifier": (
        "nightly-ledger-verifier", ["python", "-m", "pdd.sync_core.nightly_ledger_verifier"]
    ),
    "pdd-sync-reference-verifier": ("reference-verifier", ["pdd-sync-reference-verifier"]),
    "pdd-sync-certificate-finalizer": ("certificate-finalizer", ["pdd-sync-certificate-finalizer"]),
    ".github/workflows/global-sync-merge-group.yml": (
        "merge-group-workflow", [".github/workflows/global-sync-merge-group.yml"]
    ),
    ".github/workflows/global-sync-shadow-nightly.yml": (
        "shadow-nightly-workflow", [".github/workflows/global-sync-shadow-nightly.yml"]
    ),
    "tests/test_sync_core_runner_pytest.py": (
        "sync-core-runner-pytest-test", ["python", "-m", "pytest", "tests/test_sync_core_runner_pytest.py"]
    ),
    "tests/test_global_sync_vertical_slice.py": (
        "global-sync-vertical-slice-test", ["python", "-m", "pytest", "tests/test_global_sync_vertical_slice.py"]
    ),
    "pdd.sync_core.production_global_sync_verifier": (
        "production-global-sync-verifier", ["python", "-m", "pdd.sync_core.production_global_sync_verifier"]
    ),
}
REQUIRED_COMMAND_FIELDS = (
    "id", "state", "argv", "owner", "introducing_milestone",
    "earliest_invocable_milestone", "introducing_pr",
    "last_source_validation_sha", "last_wheel_validation_sha",
)


def _load(path: Path) -> dict[str, Any]:
    try:
        value = yaml.safe_load(path.read_text(encoding="utf-8"))
    except (OSError, yaml.YAMLError) as error:
        raise ValueError(f"cannot load {path}: {error}") from error
    if not isinstance(value, dict):
        raise ValueError(f"{path} must contain a mapping")
    return value


def _error(errors: list[str], message: str) -> None:
    errors.append(f"execution-contract: {message}")


def _strings(value: Any) -> bool:
    return isinstance(value, list) and all(isinstance(item, str) and item for item in value)


def _path_exists(root: Path, path: str) -> bool:
    candidate = root / path
    return candidate.is_file() and not candidate.is_symlink()


def _component_errors(command: dict[str, Any], root: Path) -> list[str]:
    command_id = str(command.get("id", "<unknown>"))
    argv = command.get("argv")
    kind = command.get("kind")
    if not _strings(argv):
        return [f"{command_id}: argv must be a non-empty exact argument vector"]
    if kind == "module":
        try:
            index = argv.index("-m")
            module = argv[index + 1]
        except (ValueError, IndexError):
            return [f"{command_id}: module argv must contain '-m MODULE'"]
        local_module = root.joinpath(*module.split("."))
        if not (local_module.with_suffix(".py").is_file() or (local_module / "__init__.py").is_file()) and importlib.util.find_spec(module) is None:
            return [f"{command_id}: module does not exist: {module}"]
    elif kind in {"script", "test", "workflow"}:
        if kind == "workflow":
            target = argv[-1]
        elif kind == "test":
            targets = [item for item in argv if item.startswith("tests/")]
            target = targets[0] if targets else ""
        else:
            targets = [item for item in argv if item.endswith(".py")]
            target = targets[-1] if targets else ""
        if not target or not _path_exists(root, target):
            return [f"{command_id}: {kind} does not exist: {target or '<missing path>'}"]
    elif kind == "console":
        if argv[0] != "pdd":
            return [f"{command_id}: console entry point must be pdd"]
    else:
        return [f"{command_id}: unsupported command kind: {kind}"]
    return []


def _cli_errors(command: dict[str, Any], python: str, label: str, root: Path) -> list[str]:
    command_id = command["id"]
    argv = command["argv"]
    if command.get("kind") != "console":
        return []
    words = argv[1:]
    canonical = {"certify", "validate", "baseline", "recover"}
    if not words or words[0] not in canonical:
        errors = [f"{command_id}: wrong Click parent; canonical command must be top-level pdd certify|validate|baseline|recover"]
        errors.extend(f"{command_id}: documented option {option!r} is not accepted by {label} CLI" for option in command.get("documented_options", []))
        return errors
    if len(words) != 1:
        errors = [f"{command_id}: wrong Click parent; nested pdd commands are not canonical"]
        errors.extend(f"{command_id}: documented option {option!r} is not accepted by {label} CLI" for option in command.get("documented_options", []))
        return errors
    launcher = [python, "-m", "pdd"]
    cwd = root
    environment = None
    if label == "built-wheel":
        wheel_error, launcher, cwd, environment = _wheel_origin_preflight(
            python, root
        )
        if wheel_error:
            return [f"{command_id}: {wheel_error}"]
        try:
            preflight = subprocess.run(
                [*launcher, "-c", "import pathlib, pdd; print(pathlib.Path(pdd.__file__).resolve())"],
                cwd=cwd, env=environment, text=True, capture_output=True, check=False,
            )
        except OSError as error:
            return [f"{command_id}: built-wheel origin preflight failed: {error}"]
        origin_error = _wheel_origin_error(preflight, root, cwd)
        if origin_error:
            return [f"{command_id}: {origin_error}"]
    try:
        result = subprocess.run(
            [*launcher, words[0], "--help"], cwd=cwd, env=environment, text=True,
            capture_output=True, check=False,
        )
    except OSError as error:
        return [f"{command_id}: {label} CLI launcher failed: {error}"]
    if result.returncode:
        return [f"{command_id}: {label} CLI does not accept {' '.join(argv)}"]
    help_text = result.stdout + result.stderr
    errors = []
    for option in command.get("documented_options", []):
        if not isinstance(option, str) or option not in help_text:
            errors.append(f"{command_id}: documented option {option!r} is not accepted by {label} CLI")
    return errors


def _wheel_origin_preflight(
    python: str, root: Path
) -> tuple[str | None, list[str], Path, dict[str, str]]:
    """Prepare a wheel-only interpreter invocation outside candidate source."""
    interpreter = Path(python)
    if not interpreter.is_absolute() or interpreter.is_symlink():
        return "built-wheel interpreter must be an absolute non-symlink path", [], root, {}
    try:
        resolved = interpreter.resolve(strict=True)
    except OSError:
        return "built-wheel interpreter does not resolve", [], root, {}
    if root == resolved or root in resolved.parents:
        return "built-wheel interpreter resolves inside checkout", [], root, {}
    wheel_root = resolved.parent.parent
    if not wheel_root.is_dir():
        return "built-wheel interpreter has no environment root", [], root, {}
    environment = {
        key: value for key, value in os.environ.items()
        if key not in {"PYTHONHOME", "PYTHONPATH"}
    }
    environment["PYTHONNOUSERSITE"] = "1"
    return None, [str(resolved), "-I"], wheel_root, environment


def _wheel_origin_error(result: subprocess.CompletedProcess[str] | Any, root: Path, wheel_root: Path) -> str | None:
    """Reject a wheel interpreter that did not import an installed wheel package."""
    if result.returncode:
        return "built-wheel origin preflight could not import pdd"
    origins = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    if len(origins) != 1:
        return "built-wheel origin preflight returned an ambiguous package path"
    try:
        package = Path(origins[0]).resolve(strict=True)
    except OSError:
        return "built-wheel origin preflight returned an unresolved package path"
    if root == package or root in package.parents:
        return "built-wheel origin resolves to checkout source"
    if wheel_root not in package.parents or "site-packages" not in package.parts:
        return "built-wheel origin is outside its environment site-packages"
    return None


def _walk_references(value: Any, key: str | None = None) -> Iterable[str]:
    if isinstance(value, dict):
        for child_key, child in value.items():
            yield from _walk_references(child, child_key)
    elif isinstance(value, list):
        if key and (key.endswith("commands") or key.endswith("command_ids")):
            yield from (item for item in value if isinstance(item, str))
        else:
            for child in value:
                yield from _walk_references(child, key)


def verify(plan: Path, state_path: Path, *, root: Path | None = None, validate_cli: bool = True, wheel_python: str | None = None) -> list[str]:
    """Return all semantic contract violations; an empty list is a pass."""
    root = (root or state_path.parents[1]).resolve()
    plan = plan.resolve()
    state_path = state_path.resolve()
    errors: list[str] = []
    try:
        state = _load(state_path)
        plan_text = plan.read_text(encoding="utf-8")
    except (ValueError, OSError, UnicodeDecodeError) as error:
        return [f"execution-contract: {error}"]
    if not all(milestone in plan_text for milestone in MILESTONES):
        _error(errors, "active plan must define M0-M5 vocabulary")
    if state.get("milestone_order") != MILESTONES:
        _error(errors, "state milestone_order must be exactly M0-M5")
    base = state.get("protected_base_sha")
    if not isinstance(base, str) or len(base) != 40:
        _error(errors, "state must record a 40-character protected base SHA")
    if state.get("active_blocker") != "m0-executable-baseline":
        _error(errors, "active blocker must be m0-executable-baseline")
    for required in ("integration", "tracks"):
        if required not in state:
            _error(errors, f"state missing integration topology: {required}")

    registry = state.get("command_registry")
    if not isinstance(registry, list):
        return errors + ["execution-contract: state command_registry must be a list"]
    by_id: dict[str, dict[str, Any]] = {}
    for command in registry:
        if not isinstance(command, dict):
            _error(errors, "command registry entries must be mappings")
            continue
        command_id = command.get("id")
        if not isinstance(command_id, str) or command_id in by_id:
            _error(errors, f"command registry id is missing or duplicated: {command_id!r}")
            continue
        by_id[command_id] = command
        missing = [field for field in REQUIRED_COMMAND_FIELDS if field not in command]
        if missing:
            _error(errors, f"{command_id}: missing command fields: {', '.join(missing)}")
        if command.get("state") not in STATES:
            _error(errors, f"{command_id}: invalid execution state {command.get('state')!r}")
        for field in ("introducing_milestone", "earliest_invocable_milestone"):
            if command.get(field) not in MILESTONES:
                _error(errors, f"{command_id}: {field} must use M0-M5 vocabulary")
        if command.get("state") == "EXTERNAL_PROTECTED":
            if not command.get("artifact_digest") or not command.get("control_plane_identity"):
                _error(errors, f"{command_id}: EXTERNAL_PROTECTED requires artifact digest and control-plane identity")
        if command.get("state") == "EXISTS":
            for message in _component_errors(command, root):
                _error(errors, message)
        if validate_cli and command.get("state") == "EXISTS":
            for message in _cli_errors(command, sys.executable, "source", root):
                _error(errors, message)
            if wheel_python:
                for message in _cli_errors(command, wheel_python, "built-wheel", root):
                    _error(errors, message)

        for field in ("last_source_validation_sha", "last_wheel_validation_sha"):
            value = command.get(field)
            if value is not None and (not isinstance(value, str) or not SHA1.fullmatch(value)):
                _error(errors, f"{command_id}: {field} must be null or an exact 40-character SHA")

    steps = state.get("validation_steps", [])
    if not isinstance(steps, list):
        _error(errors, "validation_steps must be a list")
        steps = []
    invoked: set[str] = set()
    for step in steps:
        if not isinstance(step, dict):
            _error(errors, "validation step must be a mapping")
            continue
        commands = step.get("validation_commands", [])
        if step.get("executable") is True and not commands:
            _error(errors, f"{step.get('id', '<unknown>')}: executable step has empty validation commands")
        if not isinstance(commands, list):
            _error(errors, f"{step.get('id', '<unknown>')}: validation_commands must be a list")
            continue
        invoked.update(item for item in commands if isinstance(item, str))
    invoked.update(_walk_references({key: value for key, value in state.items() if key not in {"command_registry", "validation_steps"}}))
    for command_id in invoked:
        command = by_id.get(command_id)
        if command is None:
            _error(errors, f"invoked command is absent from registry: {command_id}")
        elif command.get("state") in {"TO_BUILD", "ARCHIVED"}:
            _error(errors, f"{command_id}: {command['state']} command is invoked before implementation")
        elif command.get("state") == "EXTERNAL_PROTECTED":
            digest = command.get("artifact_digest")
            identity = command.get("control_plane_identity")
            if (
                not isinstance(digest, str)
                or not digest.startswith("sha256:")
                or digest == "pending"
                or not isinstance(identity, str)
                or not identity
                or identity == "pending"
            ):
                _error(errors, f"{command_id}: EXTERNAL_PROTECTED command has pending binding at invocation")

    required_ids = set(state.get("required_to_build_components", []))
    for name, (command_id, expected_argv) in PLAN_TO_BUILD.items():
        if name in plan_text or command_id in required_ids:
            command = by_id.get(command_id)
            if command is None:
                _error(errors, f"missing plan-named TO_BUILD component: {command_id}")
            elif command.get("state") != "TO_BUILD" or command.get("argv") != expected_argv:
                _error(errors, f"{command_id}: plan-named component must be TO_BUILD with exact argv")

    source_relative = state.get("ledger_source")
    generated_relative = state.get("generated_ledger")
    if not isinstance(source_relative, str) or not isinstance(generated_relative, str):
        _error(errors, "state must name ledger_source and generated_ledger")
        return errors
    try:
        source = _load(root / source_relative)
        generated = _load(root / generated_relative)
    except ValueError as error:
        return errors + [f"execution-contract: {error}"]
    source_contract = source.get("execution_contract")
    generated_contract = generated.get("execution_contract")
    if source_contract != generated_contract:
        _error(errors, "generated ledger execution contract disagrees with source")
    if not isinstance(source_contract, dict):
        _error(errors, "ledger source must contain execution_contract")
    else:
        for key, expected in (("protected_base_sha", base), ("milestone_order", MILESTONES), ("active_blocker", "m0-executable-baseline")):
            if source_contract.get(key) != expected:
                label = "base SHA" if key == "protected_base_sha" else key
                _error(errors, f"plan/state/ledger disagreement for {label}")
        if source_contract.get("registry_state") == state_path.relative_to(root).as_posix():
            if source_contract.get("execution_state_vocabulary") != sorted(STATES):
                _error(errors, "ledger execution-state vocabulary disagrees with registry")
        else:
            for key, expected in (("command_registry", registry), ("validation_steps", steps)):
                if source_contract.get(key) != expected:
                    _error(errors, f"plan/state/ledger disagreement for {key}")
    legacy_steps = source.get("steps", [])
    if not isinstance(legacy_steps, list):
        _error(errors, "ledger steps must be a list")
    for step in legacy_steps:
        if not isinstance(step, dict) or step.get("execution_state") != "ARCHIVED":
            _error(errors, "legacy step must declare execution_state: ARCHIVED")
    return errors


def main() -> int:
    """Parse command-line arguments and return a process-compatible status."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--wheel-python", help="Python executable from the built PDD wheel environment")
    parser.add_argument("--semantic-only", action="store_true", help="Skip source/wheel Click help probes")
    args = parser.parse_args()
    errors = verify(args.plan, args.state, root=args.root, validate_cli=not args.semantic_only, wheel_python=args.wheel_python)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("global-sync execution contract passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
