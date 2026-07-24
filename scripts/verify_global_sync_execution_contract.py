#!/usr/bin/env python3
"""Fail-closed semantic verification for the global-sync M0 contract.

The evidence ledger renderer protects bytes and promotion evidence.  This
companion deliberately checks the active execution metadata: commands that
look plausible in prose must resolve to real, correctly-parented interfaces.
"""
# pylint: disable=too-many-arguments,too-many-boolean-expressions,too-many-branches,too-many-locals,too-many-return-statements,too-many-statements,line-too-long

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import shlex
import hashlib
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable

import yaml


STATES = frozenset({"EXISTS", "TO_BUILD", "EXTERNAL_PROTECTED", "ARCHIVED"})
MILESTONES = ["M0", "M1", "M2", "M3", "M4", "M5"]
SHA1 = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
M0_FOCUSED_TEST_TARGETS = (
    "tests/test_sync_core_cli.py",
    "tests/test_sync_core_transaction.py",
    "tests/test_sync_core_reporting.py",
    "tests/test_sync_core_standalone_package.py",
)
M0_FINALIZER_NODE = (
    "tests/test_sync_core_reporting.py::"
    "test_trusted_finalizer_commits_artifact_closure_evidence_and_fingerprint"
)
FUTURE_COMPONENTS = {
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
        "production-global-sync-verifier", [
            "python", "-m", "pdd.sync_core.production_global_sync_verifier",
            "--pdd-repo", "{pdd_repo}", "--pdd-cloud-repo", "{pdd_cloud_repo}",
            "--require-milestone", "M4", "--fresh-evidence", "--fault-injection",
            "--output", "{m4_report}",
        ]
    ),
}
M4_COMMAND = FUTURE_COMPONENTS[
    "pdd.sync_core.production_global_sync_verifier"
]
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
        modules = [argv[index + 1] for index, item in enumerate(argv[:-1]) if item == "-m"]
        if not modules:
            return [f"{command_id}: module argv must contain '-m MODULE'"]
        errors = []
        for module in modules:
            local_module = root.joinpath(*module.split("."))
            if not (local_module.with_suffix(".py").is_file() or (local_module / "__init__.py").is_file()) and importlib.util.find_spec(module) is None:
                errors.append(f"{command_id}: module does not exist: {module}")
        return errors
    if kind in {"script", "test", "workflow"}:
        if kind == "workflow":
            targets = [item for item in argv if item.startswith(".github/workflows/")]
        else:
            targets = (
                [item for item in argv if item.startswith("tests/")]
                if kind == "test" else [item for item in argv if item.endswith(".py")]
            )
        if not targets:
            return [f"{command_id}: {kind} argv must name at least one repository target"]
        return [
            f"{command_id}: {kind} does not exist: {target}"
            for target in targets if not _path_exists(root, target)
        ]
    if kind == "console":
        if argv[0] != "pdd":
            return [f"{command_id}: console entry point must be pdd"]
        return []
    return [f"{command_id}: unsupported command kind: {kind}"]


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
                [*launcher, "-c", "import json, pathlib, sys, pdd; print(json.dumps({'prefix': str(pathlib.Path(sys.prefix).resolve()), 'pdd_file': str(pathlib.Path(pdd.__file__).resolve())}))"],
                cwd=cwd, env=environment, text=True, capture_output=True, check=False,
            )
        except OSError as error:
            return [f"{command_id}: built-wheel origin preflight failed: {error}"]
        origin_error = _wheel_origin_error(preflight, root, cwd)
        if origin_error:
            return [f"{command_id}: {origin_error}"]
        launcher = [*launcher, "-m", "pdd"]
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
        if not isinstance(option, str) or not re.search(
            rf"(?<![A-Za-z0-9_-]){re.escape(option)}(?![A-Za-z0-9_-])", help_text
        ):
            errors.append(f"{command_id}: documented option {option!r} is not accepted by {label} CLI")
    return errors


def _plan_commands(plan_text: str) -> list[list[str]]:
    """Return shell-tokenized Python/PDD commands from active fenced plan blocks."""
    commands: list[list[str]] = []
    for match in re.finditer(r"```[^\n]*\n(.*?)```", plan_text, re.DOTALL):
        logical = ""
        for raw_line in match.group(1).splitlines():
            line = raw_line.strip()
            if not line or line.startswith("#"):
                continue
            logical = f"{logical} {line}".strip() if logical else line
            if logical.endswith("\\"):
                logical = logical[:-1].rstrip()
                continue
            try:
                argv = shlex.split(logical)
            except ValueError:
                logical = ""
                continue
            logical = ""
            if not argv:
                continue
            executable = argv[0]
            if re.fullmatch(r"python(?:[0-9]+(?:\.[0-9]+)?)?", executable):
                commands.append(argv)
            elif executable == "pdd" and len(argv) > 1 and not argv[1].endswith(":"):
                commands.append(argv)
    return commands


def _validate_plan_commands(plan_text: str, registry: list[dict[str, Any]], errors: list[str]) -> None:
    """Require every executable command printed by the plan to be registry-backed."""
    registered = {
        tuple(command["argv"]) for command in registry
        if _strings(command.get("argv"))
    }
    for argv in _plan_commands(plan_text):
        if tuple(argv) not in registered:
            _error(errors, f"plan command is absent from registry or differs from exact argv: {' '.join(argv)}")


def _milestone_before(left: Any, right: Any) -> bool:
    return isinstance(left, str) and isinstance(right, str) and left in MILESTONES and right in MILESTONES and MILESTONES.index(left) < MILESTONES.index(right)


def _previous_milestone(milestone: Any) -> str | None:
    """Return the protected predecessor required before a milestone activates."""
    if not isinstance(milestone, str) or milestone not in MILESTONES:
        return None
    index = MILESTONES.index(milestone)
    return MILESTONES[index - 1] if index else None


def _git_diff_paths(root: Path, protected_base: str, candidate: str) -> list[str]:
    """Return the exact protected-base..candidate changed paths, fail-closed."""
    try:
        result = subprocess.run(
            ["git", "-C", str(root), "diff", "--name-status", "--find-renames",
             "--find-copies-harder",
             f"{protected_base}..{candidate}"],
            text=True, capture_output=True, check=False,
        )
    except OSError as error:
        raise ValueError(f"cannot inspect protected-base candidate diff: {error}") from error
    if result.returncode:
        raise ValueError("cannot inspect protected-base candidate diff")
    paths: list[str] = []
    for line in result.stdout.splitlines():
        fields = line.split("\t")
        if not fields or not fields[0]:
            raise ValueError("protected-base candidate diff returned malformed status")
        if fields[0][0] in {"R", "C"}:
            if len(fields) != 3 or not all(fields[1:]):
                raise ValueError("protected-base candidate diff returned malformed rename/copy")
            paths.extend(fields[1:])
        elif fields[0][0] in {"A", "D", "M", "T", "U", "X", "B"}:
            if len(fields) != 2 or not fields[1]:
                raise ValueError("protected-base candidate diff returned malformed path")
            paths.append(fields[1])
        else:
            raise ValueError("protected-base candidate diff returned unknown status")
    return paths


def _resolved_candidate_sha(root: Path, candidate_sha: str | None) -> str | None:
    """Use an explicit candidate when supplied, otherwise safely resolve HEAD."""
    if candidate_sha is not None:
        return candidate_sha
    if not (root / ".git").exists():
        return None
    try:
        result = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"], text=True,
                                capture_output=True, check=False)
    except OSError:
        return None
    candidate = result.stdout.strip()
    return candidate if not result.returncode and SHA1.fullmatch(candidate) else None


def _m0_diff_errors(state: dict[str, Any], root: Path, base: Any,
                    candidate_sha: str | None) -> list[str]:
    """Bind an unpromoted M0 to the actual protected-base..candidate delta."""
    if state.get("active_blocker") != "m0-executable-baseline" or not isinstance(base, str):
        return []
    if candidate_sha is None and not (root / ".git").exists():
        return []
    if candidate_sha is None:
        return ["M0 bootstrap requires an explicit candidate SHA or a resolvable checkout HEAD"]
    if not SHA1.fullmatch(candidate_sha):
        return ["M0 bootstrap candidate SHA must be an exact lowercase 40-character SHA"]
    allowlist = state.get("m0_bootstrap_allowlist")
    if not _strings(allowlist) or len(allowlist) != len(set(allowlist)):
        return ["M0 bootstrap allowlist must be a unique non-empty exact path list"]
    integration = state.get("integration")
    tracks = state.get("tracks")
    if not isinstance(integration, dict) or not _strings(integration.get("write_set")):
        return ["M0 bootstrap integration topology requires an exact integration write_set"]
    if not isinstance(tracks, list):
        return ["M0 bootstrap integration topology requires tracks"]
    m0_paths = set(integration["write_set"])
    for track in tracks:
        if isinstance(track, dict) and str(track.get("id", "")).startswith("m0-"):
            write_set = track.get("write_set")
            if not _strings(write_set):
                return ["M0 bootstrap track requires an exact write_set"]
            m0_paths.update(write_set)
    errors: list[str] = []
    try:
        changed_paths = _git_diff_paths(root, base, candidate_sha)
    except ValueError as error:
        return [str(error)]
    for path in changed_paths:
        if path not in allowlist:
            errors.append(f"M0 bootstrap allowlist rejects changed path: {path}")
        if path not in m0_paths:
            errors.append(f"M0 bootstrap topology/write sets do not record changed path: {path}")
    return errors


def _promotion_errors(state: dict[str, Any], registry: list[dict[str, Any]]) -> list[str]:
    """Validate milestone activation and the evidence that makes it legal."""
    promotions = state.get("milestone_promotions", {})
    if not isinstance(promotions, dict):
        return ["milestone_promotions must be a mapping"]
    errors: list[str] = []
    for milestone, promotion in promotions.items():
        if milestone not in MILESTONES or not isinstance(promotion, dict):
            errors.append("milestone promotion records must be M0-M5 mappings")
            continue
        if promotion.get("state") != "passed":
            errors.append(f"{milestone} promotion must declare state: passed")
            continue
        candidate = promotion.get("candidate_sha")
        digest = promotion.get("wheel_artifact_sha256")
        if (not isinstance(candidate, str) or not SHA1.fullmatch(candidate)
                or not isinstance(digest, str) or not SHA256.fullmatch(digest)
                or not isinstance(promotion.get("hosted_proof"), str)
                or not promotion["hosted_proof"]):
            errors.append(f"{milestone} promotion requires hosted proof, candidate SHA, and wheel digest")
            continue
        if milestone == "M0":
            for command in registry:
                if command.get("introducing_milestone") != "M0" or command.get("state") != "EXISTS":
                    continue
                if (command.get("last_source_validation_sha") != candidate
                        or command.get("last_wheel_validation_sha") != candidate):
                    errors.append(f"M0 promotion requires source/wheel bindings for {command.get('id')}")
    for command in registry:
        if command.get("state") != "EXISTS":
            continue
        milestone = command.get("introducing_milestone")
        predecessor = _previous_milestone(milestone)
        if predecessor is None:
            continue
        promotion = promotions.get(predecessor)
        if not isinstance(promotion, dict) or promotion.get("state") != "passed":
            errors.append(f"{command.get('id')}: EXISTS requires predecessor {predecessor} promotion")
            continue
        evidence = command.get("merged_introducer_evidence")
        introducer_sha = evidence.get("sha") if isinstance(evidence, dict) else None
        if (not isinstance(introducer_sha, str) or not SHA1.fullmatch(introducer_sha)
                or command.get("introducing_pr") in {None, "", "pending"}
                or command.get("component_binding") != command.get("id")
                or command.get("last_source_validation_sha") != introducer_sha
                or command.get("last_wheel_validation_sha") != introducer_sha):
            errors.append(f"{command.get('id')}: EXISTS requires merged introducer and exact component/source/wheel bindings")
    return errors


def _wheel_origin_preflight(
    python: str, root: Path
) -> tuple[str | None, list[str], Path, dict[str, str]]:
    """Prepare a wheel-only interpreter invocation outside candidate source."""
    interpreter = Path(python)
    if not interpreter.is_absolute() or not interpreter.is_file():
        return "built-wheel interpreter must be an existing absolute file", [], root, {}
    if root == interpreter or root in interpreter.parents:
        return "built-wheel interpreter is lexically inside checkout", [], root, {}
    wheel_root = interpreter.parent.parent
    if not wheel_root.is_dir():
        return "built-wheel interpreter has no environment root", [], root, {}
    environment = {
        key: value for key, value in os.environ.items()
        if key not in {"PYTHONHOME", "PYTHONPATH", "PYTHONUSERBASE"}
    }
    environment["PYTHONNOUSERSITE"] = "1"
    return None, [str(interpreter), "-I"], wheel_root, environment


def _wheel_origin_error(result: subprocess.CompletedProcess[str] | Any, root: Path, wheel_root: Path) -> str | None:
    """Reject a wheel interpreter that did not import an installed wheel package."""
    if result.returncode:
        return "built-wheel origin preflight could not import pdd"
    try:
        payload = json.loads(result.stdout)
    except json.JSONDecodeError:
        return "built-wheel origin preflight returned ambiguous JSON"
    if not isinstance(payload, dict) or not isinstance(payload.get("prefix"), str) or not isinstance(payload.get("pdd_file"), str):
        return "built-wheel origin preflight returned malformed JSON"
    try:
        prefix = Path(payload["prefix"]).resolve(strict=True)
        expected_prefix = wheel_root.resolve(strict=True)
        package = Path(payload["pdd_file"]).resolve(strict=True)
    except OSError:
        return "built-wheel origin preflight returned an unresolved package path"
    if prefix != expected_prefix:
        return "built-wheel sys.prefix does not match the lexical venv root"
    if root == package or root in package.parents:
        return "built-wheel origin resolves to checkout source"
    if prefix not in package.parents or "site-packages" not in package.parts:
        return "built-wheel origin is outside its environment site-packages"
    return None


def _wheel_binding_errors(wheel_python: str, wheel_artifact: Path | None,
                         candidate_sha: str | None, root: Path) -> list[str]:
    """Bind an isolated installation to the exact candidate wheel file.

    PEP 610 is written by pip for a direct local-wheel install.  Requiring its
    archive hash prevents a convenient but stale wheel environment from being
    offered as evidence for the candidate currently under review.
    """
    if wheel_artifact is None or not wheel_artifact.is_file() or wheel_artifact.is_symlink():
        return ["built-wheel proof requires a regular --wheel-artifact"]
    if candidate_sha is None or not SHA1.fullmatch(candidate_sha):
        return ["built-wheel proof requires an exact lowercase --candidate-sha"]
    digest = hashlib.sha256(wheel_artifact.read_bytes()).hexdigest()
    preflight, launcher, cwd, environment = _wheel_origin_preflight(wheel_python, root)
    if preflight:
        return [preflight]
    program = (
        "import importlib.metadata,json,pathlib; "
        "dist=importlib.metadata.distribution('pdd-cli'); "
        "paths=[pathlib.Path(dist.locate_file(item)) for item in (dist.files or ()) "
        "if str(item).endswith('direct_url.json')]; "
        "print(json.dumps({'direct_url': json.loads(paths[0].read_text()) if len(paths)==1 else None}))"
    )
    try:
        result = subprocess.run([*launcher, "-c", program], cwd=cwd, env=environment,
                                text=True, capture_output=True, check=False)
    except OSError as error:
        return [f"built-wheel PEP 610 preflight failed: {error}"]
    if result.returncode:
        return ["built-wheel PEP 610 preflight could not inspect pdd-cli"]
    try:
        direct_url = json.loads(result.stdout).get("direct_url")
        installed_hash = direct_url["archive_info"]["hash"]
    except (AttributeError, KeyError, TypeError, json.JSONDecodeError):
        return ["built-wheel installation lacks an unambiguous PEP 610 direct-url binding"]
    if installed_hash != f"sha256={digest}":
        return ["built-wheel PEP 610 digest does not bind the supplied wheel artifact"]
    return []


def _candidate_checkout_errors(candidate_sha: str | None, root: Path) -> list[str]:
    """Bind the runtime candidate label to this checkout without mutating it."""
    if candidate_sha is None or not (root / ".git").exists():
        return []
    try:
        result = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"],
                                text=True, capture_output=True, check=False)
    except OSError as error:
        return [f"candidate checkout preflight failed: {error}"]
    if result.returncode or result.stdout.strip() != candidate_sha:
        return ["candidate SHA does not match the checkout that built the wheel"]
    return []


def _focused_test_proof_errors(proof_path: Path | None, environment: str,
                               candidate_sha: str | None,
                               wheel_artifact: Path | None) -> tuple[list[str], dict[str, Any] | None]:
    """Require a candidate-bound successful result for both focused M0 tests."""
    if proof_path is None or not proof_path.is_file() or proof_path.is_symlink():
        return [f"{environment} focused-test proof must be a regular file"], None
    try:
        proof = json.loads(proof_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        return [f"{environment} focused-test proof is unreadable: {error}"], None
    if not isinstance(proof, dict):
        return [f"{environment} focused-test proof must be a JSON object"], None
    errors: list[str] = []
    if proof.get("candidate_sha") != candidate_sha:
        errors.append(f"{environment} focused-test proof does not bind candidate SHA")
    if proof.get("environment") != environment:
        errors.append(f"{environment} focused-test proof has wrong environment")
    if proof.get("focused_test_targets") != list(M0_FOCUSED_TEST_TARGETS):
        errors.append(f"{environment} focused-test proof has wrong focused test identities")
    if proof.get("finalizer_node") != M0_FINALIZER_NODE:
        errors.append(f"{environment} focused-test proof has wrong finalizer node")
    outcomes = proof.get("outcomes")
    if not isinstance(outcomes, dict):
        errors.append(f"{environment} focused-test proof lacks outcomes")
    else:
        for identity in ("focused_suite", "finalizer_node"):
            outcome = outcomes.get(identity)
            if not isinstance(outcome, dict) or outcome.get("status") != "passed" or outcome.get("exit_code") != 0:
                errors.append(f"{environment} focused-test proof lacks successful {identity} outcome")
    if environment == "wheel":
        digest = hashlib.sha256(wheel_artifact.read_bytes()).hexdigest() if wheel_artifact and wheel_artifact.is_file() else None
        if proof.get("wheel_artifact_sha256") != digest:
            errors.append("wheel focused-test proof does not bind wheel digest")
    return errors, proof


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


def verify(plan: Path, state_path: Path, *, root: Path | None = None,
           validate_cli: bool = True, wheel_python: str | None = None,
           expected_protected_base: str | None = None,
           candidate_sha: str | None = None,
           wheel_artifact: Path | None = None,
           source_focused_proof: Path | None = None,
           wheel_focused_proof: Path | None = None) -> list[str]:
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
    if not isinstance(base, str) or not SHA1.fullmatch(base):
        _error(errors, "state must record an exact lowercase 40-character protected base SHA")
    if expected_protected_base is not None:
        if not SHA1.fullmatch(expected_protected_base):
            _error(errors, "expected protected base must be an exact lowercase 40-character SHA")
        elif base != expected_protected_base:
            _error(errors, "state protected base disagrees with expected protected base")
    candidate_sha = _resolved_candidate_sha(root, candidate_sha)
    if candidate_sha is not None and not SHA1.fullmatch(candidate_sha):
        _error(errors, "candidate SHA must be an exact lowercase 40-character SHA")
    if wheel_python:
        for message in _wheel_binding_errors(wheel_python, wheel_artifact, candidate_sha, root):
            _error(errors, message)
        for message in _candidate_checkout_errors(candidate_sha, root):
            _error(errors, message)
    if source_focused_proof is not None or wheel_focused_proof is not None:
        for message, _proof in (
                _focused_test_proof_errors(source_focused_proof, "source", candidate_sha, None),
                _focused_test_proof_errors(wheel_focused_proof, "wheel", candidate_sha, wheel_artifact)):
            for detail in message:
                _error(errors, detail)

    preflight = state.get("preflight")
    if not isinstance(preflight, dict):
        _error(errors, "state missing protected-base preflight")
    elif (preflight.get("protected_base_ref") != "origin/main"
          or preflight.get("protected_base_sha") != base
          or preflight.get("source_checkout_clean") not in {True, "pending-m0-validation"}):
        _error(errors, "state protected-base preflight is malformed or disagrees with state base")
    integration = state.get("integration")
    if not isinstance(integration, dict) or integration.get("base_sha") != base:
        _error(errors, "state integration topology must bind the protected base")
    scoreboard = state.get("scoreboard", {})
    current_milestone = scoreboard.get("milestone", "M0") if isinstance(scoreboard, dict) else "M0"
    if current_milestone not in MILESTONES:
        _error(errors, "scoreboard milestone must use M0-M5 vocabulary")
    elif current_milestone == "M0":
        if state.get("active_blocker") != "m0-executable-baseline":
            _error(errors, "M0 active blocker must be m0-executable-baseline")
    else:
        promotions = state.get("milestone_promotions", {})
        if (not isinstance(promotions, dict) or not isinstance(promotions.get("M0"), dict)
                or promotions["M0"].get("state") != "passed"):
            _error(errors, "post-M0 current milestone requires an M0 passed promotion")
        if (not isinstance(state.get("active_blocker"), str)
                or state.get("active_blocker") == "m0-executable-baseline"):
            _error(errors, "post-M0 current milestone requires a non-M0 active blocker")
    for required in ("integration", "tracks"):
        if required not in state:
            _error(errors, f"state missing integration topology: {required}")
    for message in _m0_diff_errors(state, root, base, candidate_sha):
        _error(errors, message)

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
        if _milestone_before(command.get("earliest_invocable_milestone"), command.get("introducing_milestone")):
            _error(errors, f"{command_id}: earliest invocable milestone precedes introducing milestone")
        if command.get("state") == "EXISTS" and command.get("introducing_pr") in {None, "", "pending"}:
            _error(errors, f"{command_id}: active EXISTS command has pending introducer")
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
    invoked: dict[str, list[str | None]] = {}
    for step in steps:
        if not isinstance(step, dict):
            _error(errors, "validation step must be a mapping")
            continue
        commands = step.get("validation_commands", [])
        milestone = step.get("milestone")
        if milestone not in MILESTONES:
            _error(errors, f"{step.get('id', '<unknown>')}: validation step milestone must use M0-M5 vocabulary")
        if step.get("executable") is True and not commands:
            _error(errors, f"{step.get('id', '<unknown>')}: executable step has empty validation commands")
        if not isinstance(commands, list):
            _error(errors, f"{step.get('id', '<unknown>')}: validation_commands must be a list")
            continue
        if step.get("executable") is True:
            for item in commands:
                if isinstance(item, str):
                    invoked.setdefault(item, []).append(milestone if isinstance(milestone, str) else None)
    for command_id in _walk_references({key: value for key, value in state.items() if key not in {"command_registry", "validation_steps"}}):
        invoked.setdefault(command_id, []).append(None)
    for command_id, invocation_milestones in invoked.items():
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
        elif command.get("state") == "EXISTS":
            for invocation_milestone in invocation_milestones:
                if _milestone_before(invocation_milestone, command.get("earliest_invocable_milestone")):
                    _error(errors, f"{command_id}: EXISTS command is invoked before earliest invocable milestone")

    _validate_plan_commands(plan_text, registry, errors)

    for name, (command_id, expected_argv) in FUTURE_COMPONENTS.items():
        if name not in plan_text and command_id not in set(state.get("required_to_build_components", [])):
            continue
        command = by_id.get(command_id)
        if command is None:
            _error(errors, f"missing plan-named future component: {command_id}")
            continue
        if command.get("argv") != expected_argv:
            _error(errors, f"{command_id}: future component argv must remain exact")
        if (_milestone_before(current_milestone, command.get("introducing_milestone"))
                and command.get("state") != "TO_BUILD"):
            _error(errors, f"{command_id}: future component must remain TO_BUILD before its milestone")
    m4_command = by_id.get(M4_COMMAND[0])
    if m4_command is not None and m4_command.get("argv") != M4_COMMAND[1]:
        _error(errors, "production-global-sync-verifier: M4 command must remain exact")
    for message in _promotion_errors(state, registry):
        _error(errors, message)

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
        for key, expected in (("protected_base_sha", base), ("milestone_order", MILESTONES), ("active_blocker", state.get("active_blocker"))):
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
    parser.add_argument("--wheel-artifact", type=Path, help="Exact candidate PDD wheel installed into --wheel-python")
    parser.add_argument("--candidate-sha", help="Exact lowercase Git SHA that produced --wheel-artifact")
    parser.add_argument("--source-focused-proof", type=Path, help="Successful source focused-suite proof JSON")
    parser.add_argument("--wheel-focused-proof", type=Path, help="Successful wheel focused-suite proof JSON")
    parser.add_argument("--expected-protected-base", help="PR kickoff/protected-base SHA expected by this run")
    parser.add_argument("--output", type=Path, help="Write the checked candidate/wheel binding report as JSON")
    parser.add_argument("--semantic-only", action="store_true", help="Skip source/wheel Click help probes")
    args = parser.parse_args()
    errors = verify(args.plan, args.state, root=args.root, validate_cli=not args.semantic_only,
                    wheel_python=args.wheel_python, wheel_artifact=args.wheel_artifact,
                    candidate_sha=args.candidate_sha,
                    expected_protected_base=args.expected_protected_base,
                    source_focused_proof=args.source_focused_proof,
                    wheel_focused_proof=args.wheel_focused_proof)
    if args.output:
        report = {
            "candidate_sha": args.candidate_sha,
            "expected_protected_base": args.expected_protected_base,
            "wheel_artifact": str(args.wheel_artifact) if args.wheel_artifact else None,
            "wheel_artifact_sha256": hashlib.sha256(args.wheel_artifact.read_bytes()).hexdigest()
            if args.wheel_artifact and args.wheel_artifact.is_file() else None,
            "source_focused_proof": _focused_test_proof_errors(
                args.source_focused_proof, "source", args.candidate_sha, None)[1],
            "wheel_focused_proof": _focused_test_proof_errors(
                args.wheel_focused_proof, "wheel", args.candidate_sha, args.wheel_artifact)[1],
            "passed": not errors,
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, sort_keys=True) + "\n", encoding="utf-8")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("global-sync execution contract passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
