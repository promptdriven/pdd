#!/usr/bin/env python3
"""Read-only repository-wide PDD source/artifact alignment audit.

This checker intentionally does not import PDD runtime modules.  It validates the
checked-in prompt program directly so it remains useful when the sync commands
themselves are the subject of the audit.
"""

from __future__ import annotations

import argparse
import ast
from dataclasses import asdict, dataclass
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re
import subprocess
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
PROMPTS_ROOT = ROOT / "pdd" / "prompts"
ARCHITECTURE_PATH = ROOT / "architecture.json"
EXPECTED_MANAGED_PATH = ROOT / ".pdd" / "expected-managed.json"
CLASSIFICATIONS_PATH = ROOT / ".pdd" / "repository-sync-classifications.json"
OWNERSHIP_PATH = ROOT / ".pdd" / "sync-ownership.json"
VERIFICATION_PROFILES_PATH = ROOT / ".pdd" / "verification-profiles.json"
VERIFICATION_PROFILE_ROTATIONS_PATH = ROOT / ".pdd" / "verification-profile-rotations.json"
REQUIREMENT_ID = re.compile(r"\bREQ-[A-Za-z0-9_.:-]+\b")

DIRECT_LANGUAGES = {
    "python": ".py",
    "typescript": ".ts",
    "typescriptreact": ".tsx",
}
REQUIRED_ARCHITECTURE_FIELDS = {
    "reason",
    "description",
    "dependencies",
    "priority",
    "filename",
    "filepath",
    "tags",
    "interface",
}
SUPPORTED_INTERFACE_TYPES = {
    "api",
    "cli",
    "command",
    "component",
    "config",
    "entrypoint",
    "frontend",
    "graphql",
    "job",
    "message",
    "module",
    "page",
}


@dataclass(frozen=True, order=True)
class Finding:
    """One deterministic audit finding."""

    category: str
    subject: str
    detail: str


@dataclass(frozen=True)
class PromptMetadata:
    """Architecture metadata asserted by a prompt header."""

    reason: str | None
    interface: dict[str, Any] | None
    dependencies: tuple[str, ...] | None
    interface_error: str | None = None


@dataclass(frozen=True)
class ParameterSpec:
    """Static callable-parameter shape used for interface comparison."""

    name: str
    kind: str
    annotation: str | None
    default: str | None


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _git_tracked_paths() -> set[str]:
    completed = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=ROOT,
        check=True,
        capture_output=True,
    )
    return {
        item.decode("utf-8")
        for item in completed.stdout.split(b"\0")
        if item
    }


def _metadata_header(text: str) -> str:
    """Return only the leading metadata header, excluding body examples."""

    lines = text.splitlines(keepends=True)
    if lines and lines[0].strip() == "---":
        for index, line in enumerate(lines[1:], start=1):
            if line.strip() == "---":
                lines = lines[index + 1 :]
                break

    header: list[str] = []
    started = False
    open_pdd_tag: str | None = None
    in_erb_comment = False
    in_xml_comment = False
    for line in lines:
        stripped = line.lstrip()
        if open_pdd_tag is not None:
            header.append(line)
            if re.search(rf"</{re.escape(open_pdd_tag)}>\s*$", stripped, re.I):
                open_pdd_tag = None
            continue
        if in_erb_comment:
            in_erb_comment = "--%>" not in stripped
            continue
        if in_xml_comment:
            in_xml_comment = "-->" not in stripped
            continue
        if stripped.startswith("<%--"):
            in_erb_comment = "--%>" not in stripped
            continue
        if stripped.startswith("<!--"):
            in_xml_comment = "-->" not in stripped
            continue
        if not stripped.strip():
            if started:
                header.append(line)
            continue
        tag_match = re.match(r"<(pdd-(?:reason|interface|dependency))(?:\s[^>]*)?>", stripped, re.I)
        if tag_match:
            tag = tag_match.group(1)
            started = True
            header.append(line)
            if not re.search(rf"</{re.escape(tag)}>\s*$", stripped, re.I):
                open_pdd_tag = tag
            continue
        # Includes and prompt comments are part of the declarative header even
        # when a metadata block precedes them.  They are intentionally omitted
        # from the returned text, but must not terminate metadata discovery.
        if stripped.startswith("%") or stripped.startswith("<include"):
            continue
        break
    return "".join(header)


def _tag_values(header: str, tag: str) -> list[str]:
    pattern = re.compile(
        rf"<{re.escape(tag)}(?:\s[^>]*)?>\s*(.*?)\s*</{re.escape(tag)}>",
        re.DOTALL | re.IGNORECASE,
    )
    return [match.strip() for match in pattern.findall(header)]


def parse_prompt_metadata(path: Path) -> PromptMetadata:
    """Parse optional prompt-owned architecture assertions."""

    header = _metadata_header(path.read_text(encoding="utf-8"))
    reasons = _tag_values(header, "pdd-reason")
    interfaces = _tag_values(header, "pdd-interface")
    dependency_values = _tag_values(header, "pdd-dependency")

    interface: dict[str, Any] | None = None
    interface_error: str | None = None
    if interfaces:
        if len(interfaces) > 1:
            interface_error = "multiple <pdd-interface> blocks"
        else:
            raw = interfaces[0]
            candidates = [raw]
            candidate = raw
            for _ in range(3):
                unescaped = candidate.replace("{{", "{").replace("}}", "}")
                if unescaped == candidate:
                    break
                candidates.append(unescaped)
                candidate = unescaped
            for candidate in candidates:
                try:
                    parsed = json.loads(candidate)
                except json.JSONDecodeError as exc:
                    interface_error = str(exc)
                    continue
                if not isinstance(parsed, dict):
                    interface_error = "interface JSON must be an object"
                    continue
                interface = parsed
                interface_error = None
                break

    dependencies: tuple[str, ...] | None = None
    if re.search(r"<pdd-dependency(?:\s[^>]*)?>", header, re.IGNORECASE):
        dependencies = tuple(value for value in dependency_values if value)

    return PromptMetadata(
        reason=re.sub(r"\s+", " ", reasons[0]).strip() if reasons else None,
        interface=interface,
        dependencies=dependencies,
        interface_error=interface_error,
    )


def _expected_prompts() -> set[str]:
    payload = _read_json(EXPECTED_MANAGED_PATH)
    units = payload.get("units") if isinstance(payload, dict) else None
    if payload.get("schema_version") != 1 or not isinstance(units, list):
        raise ValueError(".pdd/expected-managed.json has an unsupported schema")
    expected: set[str] = set()
    for row in units:
        if not isinstance(row, dict) or set(row) != {"prompt_path", "language_id"}:
            raise ValueError("expected-managed unit has an invalid shape")
        prompt_path = str(row["prompt_path"])
        if prompt_path in expected:
            raise ValueError(f"duplicate expected-managed prompt: {prompt_path}")
        expected.add(prompt_path)
    return expected


def _expected_units() -> set[tuple[str, str]]:
    payload = _read_json(EXPECTED_MANAGED_PATH)
    return {
        (str(row["prompt_path"]), str(row["language_id"]))
        for row in payload["units"]
    }


def _prompt_requirements(prompt_path: str) -> list[str]:
    raw = (ROOT / prompt_path).read_bytes()
    explicit = sorted(set(REQUIREMENT_ID.findall(raw.decode("utf-8"))))
    return explicit or [f"CONTRACT-SHA256:{hashlib.sha256(raw).hexdigest()}"]


def _verification_profile_findings(
    expected_units: set[tuple[str, str]],
) -> tuple[int, list[Finding]]:
    payload = _read_json(VERIFICATION_PROFILES_PATH)
    rows = payload.get("profiles") if isinstance(payload, dict) else None
    if (
        not isinstance(payload, dict)
        or payload.get("schema_version") != 1
        or not isinstance(rows, list)
    ):
        return 0, [
            Finding(
                "verification-profile",
                VERIFICATION_PROFILES_PATH.relative_to(ROOT).as_posix(),
                "unsupported profile registry schema",
            )
        ]
    findings: list[Finding] = []
    actual_units: set[tuple[str, str]] = set()
    for row in rows:
        if not isinstance(row, dict):
            findings.append(
                Finding("verification-profile", "<invalid>", "profile row must be an object")
            )
            continue
        prompt_path = str(row.get("prompt_path") or "")
        language_id = str(row.get("language_id") or "")
        subject = f"{prompt_path}:{language_id}"
        identity = (prompt_path, language_id)
        if identity in actual_units:
            findings.append(
                Finding("verification-profile", subject, "duplicate verification profile")
            )
        actual_units.add(identity)
        if identity not in expected_units or not (ROOT / prompt_path).is_file():
            findings.append(
                Finding("verification-profile", subject, "profile does not identify a managed prompt")
            )
            continue
        requirements = _prompt_requirements(prompt_path)
        if row.get("required_requirement_ids") != requirements:
            findings.append(
                Finding(
                    "verification-profile",
                    subject,
                    "required requirement identities do not match prompt bytes",
                )
            )
        obligations = row.get("obligations")
        if not isinstance(obligations, list) or not obligations:
            findings.append(
                Finding("verification-profile", subject, "profile has no obligations")
            )
            continue
        for obligation in obligations:
            if not isinstance(obligation, dict) or obligation.get("requirement_ids") != requirements:
                findings.append(
                    Finding(
                        "verification-profile",
                        subject,
                        "obligation requirement identities do not match prompt bytes",
                    )
                )
    for prompt_path, language_id in sorted(expected_units - actual_units):
        findings.append(
            Finding(
                "verification-profile",
                f"{prompt_path}:{language_id}",
                "managed prompt has no verification profile",
            )
        )
    for prompt_path, language_id in sorted(actual_units - expected_units):
        findings.append(
            Finding(
                "verification-profile",
                f"{prompt_path}:{language_id}",
                "verification profile is outside the managed inventory",
            )
        )
    return len(rows), findings


def _requirement_rotation_findings() -> tuple[int, list[Finding]]:
    """Validate the exact dormant transition dataset against origin/main."""

    findings: list[Finding] = []
    try:
        base_ref = subprocess.run(
            ["git", "merge-base", "HEAD", "origin/main"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        base_bytes = subprocess.run(
            ["git", "show", f"{base_ref}:.pdd/verification-profiles.json"],
            cwd=ROOT,
            check=True,
            capture_output=True,
        ).stdout
    except subprocess.CalledProcessError:
        return 0, [
            Finding("requirement-rotation", "origin/main", "protected base is unavailable")
        ]
    head_bytes = VERIFICATION_PROFILES_PATH.read_bytes()
    base = {
        (str(row["prompt_path"]), str(row["language_id"])): row
        for row in json.loads(base_bytes)["profiles"]
    }
    head = {
        (str(row["prompt_path"]), str(row["language_id"])): row
        for row in json.loads(head_bytes)["profiles"]
    }
    base_policy_sha = hashlib.sha256(base_bytes).hexdigest()
    head_policy_sha = hashlib.sha256(head_bytes).hexdigest()
    expected: list[dict[str, str]] = []
    for identity in sorted(base):
        before = base[identity]["required_requirement_ids"]
        after = head[identity]["required_requirement_ids"]
        if before == after:
            continue
        if not (
            len(before) == len(after) == 1
            and str(before[0]).startswith("CONTRACT-SHA256:")
            and str(after[0]).startswith("CONTRACT-SHA256:")
        ):
            findings.append(
                Finding("requirement-rotation", ":".join(identity), "transition is not a single opaque identity")
            )
            continue
        prompt_path, language_id = identity
        base_prompt = subprocess.run(
            ["git", "show", f"{base_ref}:{prompt_path}"],
            cwd=ROOT,
            check=True,
            capture_output=True,
        ).stdout
        head_prompt = (ROOT / prompt_path).read_bytes()
        expected.append(
            {
                "prompt_path": prompt_path,
                "language_id": language_id,
                "from_requirement_id": before[0],
                "to_requirement_id": after[0],
                "policy_path": ".pdd/verification-profiles.json",
                "base_policy_sha256": base_policy_sha,
                "head_policy_sha256": head_policy_sha,
                "base_prompt_sha256": hashlib.sha256(base_prompt).hexdigest(),
                "head_prompt_sha256": hashlib.sha256(head_prompt).hexdigest(),
            }
        )
    payload = _read_json(VERIFICATION_PROFILE_ROTATIONS_PATH)
    actual = payload.get("requirement_rotations") if isinstance(payload, dict) else None
    if actual != expected:
        findings.append(
            Finding(
                "requirement-rotation",
                VERIFICATION_PROFILE_ROTATIONS_PATH.relative_to(ROOT).as_posix(),
                "dormant transition rows do not exactly match protected-base prompt/profile changes",
            )
        )
    return len(actual) if isinstance(actual, list) else 0, findings


def _classifications() -> dict[str, Any]:
    payload = _read_json(CLASSIFICATIONS_PATH)
    if not isinstance(payload, dict) or payload.get("schema_version") != 1:
        raise ValueError("repository sync classifications have an unsupported schema")
    return payload


def _architecture_entries() -> list[dict[str, Any]]:
    payload = _read_json(ARCHITECTURE_PATH)
    if not isinstance(payload, list) or not all(isinstance(row, dict) for row in payload):
        raise ValueError("architecture.json must contain a list of objects")
    return payload


def _direct_artifact(prompt_relative: str) -> tuple[str, str] | None:
    """Return (language, artifact path) when the conventional artifact exists."""

    for language, extension in DIRECT_LANGUAGES.items():
        suffix = f"_{language}.prompt"
        if not prompt_relative.endswith(suffix):
            continue
        stem = prompt_relative[: -len(suffix)]
        artifact = f"pdd/{stem}{extension}"
        if (ROOT / artifact).is_file():
            return language, artifact
    return None


def _path_is_contained(relative: str) -> bool:
    try:
        candidate = (ROOT / relative).resolve(strict=False)
        candidate.relative_to(ROOT.resolve())
    except (OSError, ValueError):
        return False
    return not PurePosixPath(relative).is_absolute() and ".." not in PurePosixPath(relative).parts


def _interface_shape_findings(subject: str, interface: Any) -> list[Finding]:
    findings: list[Finding] = []
    if not isinstance(interface, dict):
        return [Finding("interface", subject, "interface must be a JSON object")]
    interface_type = interface.get("type")
    if interface_type not in SUPPORTED_INTERFACE_TYPES:
        findings.append(
            Finding("interface", subject, f"unsupported interface type {interface_type!r}")
        )
    elif interface_type not in interface or not isinstance(interface[interface_type], dict):
        findings.append(
            Finding("interface", subject, f"missing object for interface type {interface_type!r}")
        )
    elif interface_type == "module":
        module = interface[interface_type]
        public_sections = (
            "functions",
            "classes",
            "constants",
            "types",
            "typeAliases",
            "dataclasses",
            "enums",
            "protocols",
            "exceptions",
        )
        if not any(section in module for section in public_sections):
            findings.append(
                Finding("interface", subject, "module must declare a public interface section")
            )
        for section in public_sections:
            if section in module and not isinstance(module[section], list):
                findings.append(
                    Finding("interface", subject, f"module.{section} must be a list")
                )
        for section in public_sections:
            rows = module.get(section, [])
            if not isinstance(rows, list):
                continue
            for row in rows:
                if isinstance(row, dict) and row.get("returns") == "unspecified":
                    findings.append(
                        Finding(
                            "interface",
                            subject,
                            f"module.{section} contains an unspecified public return contract",
                        )
                    )
    return findings


def _function_parameters(node: ast.FunctionDef | ast.AsyncFunctionDef) -> tuple[ParameterSpec, ...]:
    args = node.args
    result: list[ParameterSpec] = []
    positional = list(args.posonlyargs) + list(args.args)
    defaults: list[ast.AST | None] = [None] * (len(positional) - len(args.defaults)) + list(
        args.defaults
    )
    for index, (argument, default) in enumerate(zip(positional, defaults)):
        result.append(
            ParameterSpec(
                argument.arg,
                "positional-only" if index < len(args.posonlyargs) else "positional",
                ast.unparse(argument.annotation) if argument.annotation is not None else None,
                ast.unparse(default) if default is not None else None,
            )
        )
    if args.vararg:
        result.append(
            ParameterSpec(
                args.vararg.arg,
                "variadic-positional",
                ast.unparse(args.vararg.annotation) if args.vararg.annotation is not None else None,
                None,
            )
        )
    for argument, default in zip(args.kwonlyargs, args.kw_defaults):
        result.append(
            ParameterSpec(
                argument.arg,
                "keyword-only",
                ast.unparse(argument.annotation) if argument.annotation is not None else None,
                ast.unparse(default) if default is not None else None,
            )
        )
    if args.kwarg:
        result.append(
            ParameterSpec(
                args.kwarg.arg,
                "variadic-keyword",
                ast.unparse(args.kwarg.annotation) if args.kwarg.annotation is not None else None,
                None,
            )
        )
    return tuple(result)


def _python_symbols(
    path: Path,
) -> tuple[
    set[str],
    dict[str, set[str]],
    dict[str, ast.FunctionDef | ast.AsyncFunctionDef],
]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    functions: set[str] = set()
    classes: dict[str, set[str]] = {}
    callables: dict[str, ast.FunctionDef | ast.AsyncFunctionDef] = {}
    imported: set[str] = set()
    declared_exports: set[str] = set()
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            functions.add(node.name)
            callables[node.name] = node
        elif isinstance(node, ast.ClassDef):
            classes[node.name] = {
                child.name
                for child in node.body
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
            }
            callables.update(
                {
                    f"{node.name}.{child.name}": child
                    for child in node.body
                    if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
                }
            )
        elif isinstance(node, ast.ImportFrom):
            imported.update(alias.asname or alias.name for alias in node.names if alias.name != "*")
        elif isinstance(node, ast.Import):
            imported.update(alias.asname or alias.name.split(".", 1)[0] for alias in node.names)
        elif isinstance(node, ast.Assign) and any(
            isinstance(target, ast.Name) and target.id == "__all__" for target in node.targets
        ):
            if isinstance(node.value, (ast.List, ast.Tuple, ast.Set)):
                declared_exports.update(
                    item.value
                    for item in node.value.elts
                    if isinstance(item, ast.Constant) and isinstance(item.value, str)
                )
    functions.update(imported & declared_exports)
    return functions, classes, callables


def _python_public_symbols(path: Path) -> set[str]:
    """Collect public top-level names, including explicit re-exports."""

    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    declared: set[str] | None = None
    for node in tree.body:
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        if not any(isinstance(target, ast.Name) and target.id == "__all__" for target in targets):
            continue
        if isinstance(node.value, (ast.List, ast.Tuple, ast.Set)):
            values = {
                item.value
                for item in node.value.elts
                if isinstance(item, ast.Constant) and isinstance(item.value, str)
            }
            if len(values) == len(node.value.elts):
                declared = values
        break
    names: set[str] = set()
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names.add(node.name)
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            names.update(target.id for target in targets if isinstance(target, ast.Name))
        elif isinstance(node, ast.ImportFrom):
            names.update(alias.asname or alias.name for alias in node.names if alias.name != "*")
        elif isinstance(node, ast.Import):
            names.update(alias.asname or alias.name.split(".", 1)[0] for alias in node.names)
    names.discard("__all__")
    return names & declared if declared is not None else {name for name in names if not name.startswith("_")}


def _declared_signature(
    signature: str,
) -> tuple[tuple[ParameterSpec, ...], str | None] | None:
    value = signature.strip()
    if value in {"", "exported", "inferred", "(...)", "()"} and value != "()":
        return None
    if value.startswith("async "):
        value = value[len("async ") :].lstrip()
    if not value.startswith("("):
        return None
    try:
        parsed = ast.parse(f"def __pdd{value}:\n    pass\n")
    except SyntaxError:
        return None
    function = parsed.body[0]
    if not isinstance(function, ast.FunctionDef):
        return None
    returns = ast.unparse(function.returns) if function.returns is not None else None
    return _function_parameters(function), returns


def _module_literal_symbols(path: Path) -> dict[str, ast.AST]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    symbols: dict[str, ast.AST] = {}
    for node in tree.body:
        if not isinstance(node, (ast.Assign, ast.AnnAssign)) or node.value is None:
            continue
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        for target in targets:
            if not isinstance(target, ast.Name):
                continue
            try:
                ast.literal_eval(node.value)
            except (ValueError, TypeError):
                continue
            symbols[target.id] = node.value
    return symbols


def _normalized_default(
    value: str | None, symbols: dict[str, ast.AST] | None = None
) -> tuple[str, Any] | None:
    if value is None:
        return None
    try:
        node = ast.parse(value, mode="eval").body
    except SyntaxError:
        return ("source", value.strip())
    if isinstance(node, ast.Name) and symbols and node.id in symbols:
        node = symbols[node.id]
    try:
        literal = ast.literal_eval(node)
    except (ValueError, TypeError):
        return ("ast", ast.dump(node, include_attributes=False))
    if isinstance(literal, float) and literal == 0.0:
        return ("zero", math.copysign(1.0, literal))
    if isinstance(literal, bool):
        return ("bool", literal)
    return ("literal", literal)


def _canonical_annotation(value: str | None) -> Any:
    if value is None:
        return None
    try:
        node = ast.parse(value, mode="eval").body
    except SyntaxError:
        return value.replace(" ", "")
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return _canonical_annotation(node.value)

    generic_names = {"List": "list", "Dict": "dict", "Tuple": "tuple", "Set": "set"}

    def canonical(item: ast.AST) -> Any:
        if isinstance(item, ast.Name):
            if item.id == "PathLike":
                return ("union", ("Path", "str"))
            return generic_names.get(item.id, item.id)
        if isinstance(item, ast.Attribute):
            return item.attr
        if isinstance(item, ast.Constant):
            if item.value is None:
                return "None"
            if isinstance(item.value, str):
                return _canonical_annotation(item.value)
            return repr(item.value)
        if isinstance(item, ast.BinOp) and isinstance(item.op, ast.BitOr):
            members: list[Any] = []

            def gather(union_item: ast.AST) -> None:
                if isinstance(union_item, ast.BinOp) and isinstance(union_item.op, ast.BitOr):
                    gather(union_item.left)
                    gather(union_item.right)
                else:
                    members.append(canonical(union_item))

            gather(item)
            return ("union", tuple(sorted(members, key=repr)))
        if isinstance(item, ast.Subscript):
            base = canonical(item.value)
            slice_items = item.slice.elts if isinstance(item.slice, ast.Tuple) else [item.slice]
            parameters = tuple(canonical(child) for child in slice_items)
            if base == "Optional" and len(parameters) == 1:
                return ("union", tuple(sorted((parameters[0], "None"), key=repr)))
            if base == "Union":
                return ("union", tuple(sorted(parameters, key=repr)))
            return (base, parameters)
        return ast.dump(item, include_attributes=False)

    return canonical(node)


def _python_api_endpoints(path: Path) -> set[tuple[str, str]]:
    """Collect literal FastAPI router endpoints without importing application code."""

    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    prefixes: dict[str, str] = {}
    for node in tree.body:
        if not isinstance(node, ast.Assign) or not isinstance(node.value, ast.Call):
            continue
        if not any(isinstance(target, ast.Name) for target in node.targets):
            continue
        callee = ast.unparse(node.value.func)
        if callee.rsplit(".", 1)[-1] != "APIRouter":
            continue
        prefix = ""
        for keyword in node.value.keywords:
            if keyword.arg == "prefix" and isinstance(keyword.value, ast.Constant):
                if isinstance(keyword.value.value, str):
                    prefix = keyword.value.value
        for target in node.targets:
            if isinstance(target, ast.Name):
                prefixes[target.id] = prefix

    endpoints: set[tuple[str, str]] = set()
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for decorator in node.decorator_list:
            if not isinstance(decorator, ast.Call) or not isinstance(decorator.func, ast.Attribute):
                continue
            method = decorator.func.attr.upper()
            if method not in {
                "GET",
                "POST",
                "PUT",
                "PATCH",
                "DELETE",
                "OPTIONS",
                "HEAD",
                "WEBSOCKET",
            }:
                continue
            if not isinstance(decorator.func.value, ast.Name):
                continue
            router_name = decorator.func.value.id
            if router_name not in prefixes or not decorator.args:
                continue
            route = decorator.args[0]
            if not isinstance(route, ast.Constant) or not isinstance(route.value, str):
                continue
            path_value = prefixes[router_name].rstrip("/") + "/" + route.value.lstrip("/")
            endpoints.add((method, path_value.rstrip("/") or "/"))
    return endpoints


def _python_interface_findings(
    prompt_relative: str,
    artifact_relative: str,
    interface: dict[str, Any],
) -> list[Finding]:
    if interface.get("type") == "api":
        endpoints = _python_api_endpoints(ROOT / artifact_relative)
        findings: list[Finding] = []
        for item in interface.get("api", {}).get("endpoints", []):
            if not isinstance(item, dict):
                findings.append(Finding("interface", prompt_relative, "API endpoint entry is malformed"))
                continue
            method = str(item.get("method") or "").upper()
            path = str(item.get("path") or "").rstrip("/") or "/"
            if (method, path) not in endpoints:
                findings.append(
                    Finding(
                        "interface-code",
                        prompt_relative,
                        f"declared endpoint {method} {path} is absent from {artifact_relative}",
                    )
                )
        return findings
    if interface.get("type") != "module":
        return []
    functions, classes, callables = _python_symbols(ROOT / artifact_relative)
    public_symbols = _python_public_symbols(ROOT / artifact_relative)
    literal_symbols = _module_literal_symbols(ROOT / artifact_relative)
    module = interface.get("module", {})
    findings: list[Finding] = []
    for item in module.get("classes", []):
        if isinstance(item, dict) and item.get("name") not in public_symbols:
            findings.append(
                Finding(
                    "interface-code",
                    prompt_relative,
                    f"declared class {item.get('name')!r} is absent from {artifact_relative}",
                )
            )
    for section in (
        "constants",
        "types",
        "typeAliases",
        "dataclasses",
        "enums",
        "protocols",
        "exceptions",
    ):
        for item in module.get(section, []):
            name = item if isinstance(item, str) else item.get("name") if isinstance(item, dict) else None
            if not isinstance(name, str):
                findings.append(
                    Finding("interface", prompt_relative, f"module {section} entry is malformed")
                )
            elif name not in public_symbols:
                findings.append(
                    Finding(
                        "interface-code",
                        prompt_relative,
                        f"declared {section} symbol {name!r} is absent from {artifact_relative}",
                    )
                )
    for item in module.get("functions", []):
        if not isinstance(item, dict) or not isinstance(item.get("name"), str):
            findings.append(
                Finding("interface", prompt_relative, "module function entry is malformed")
            )
            continue
        name = item["name"]
        if "." in name:
            class_name, method_name = name.split(".", 1)
            exists = class_name in classes and method_name in classes[class_name]
        else:
            # Older architecture metadata sometimes puts callable classes in
            # module.functions.  Accept the symbol while the repository
            # ratchets those declarations into module.classes.
            exists = name in functions or name in classes
        if not exists:
            findings.append(
                Finding(
                    "interface-code",
                    prompt_relative,
                    f"declared callable {name!r} is absent from {artifact_relative}",
                )
            )
            continue
        declared = item.get("signature")
        actual_node = callables.get(name)
        if not isinstance(declared, str) or actual_node is None:
            continue
        parsed_signature = _declared_signature(declared)
        if parsed_signature is None:
            findings.append(
                Finding(
                    "interface-signature",
                    prompt_relative,
                    f"declared signature for {name!r} is not statically parseable: {declared!r}",
                )
            )
            continue
        declared_params, declared_return = parsed_signature
        actual_params = tuple(
            parameter
            for parameter in _function_parameters(actual_node)
            if not ("." in name and parameter.name in {"self", "cls"})
        )
        if tuple((p.name, p.kind) for p in declared_params) != tuple(
            (p.name, p.kind) for p in actual_params
        ):
            findings.append(
                Finding(
                    "interface-signature",
                    prompt_relative,
                    f"parameter shape for {name!r} differs from {artifact_relative}",
                )
            )
            continue
        for expected, actual in zip(declared_params, actual_params):
            if expected.annotation is not None and _canonical_annotation(
                expected.annotation
            ) != _canonical_annotation(actual.annotation):
                findings.append(
                    Finding(
                        "interface-signature",
                        prompt_relative,
                        f"annotation for {name}.{expected.name} is {actual.annotation!r}, declared {expected.annotation!r}",
                    )
                )
            if expected.default is not None and _normalized_default(
                expected.default, literal_symbols
            ) != _normalized_default(actual.default, literal_symbols):
                findings.append(
                    Finding(
                        "interface-signature",
                        prompt_relative,
                        f"default for {name}.{expected.name} is {actual.default!r}, declared {expected.default!r}",
                    )
                )
        actual_return = ast.unparse(actual_node.returns) if actual_node.returns is not None else None
        # An explicit prompt-owned return contract remains useful when legacy
        # implementation code has no annotation.  Compare only when code also
        # makes an explicit claim; absence is not evidence of disagreement.
        if actual_return is not None and declared_return is not None and _canonical_annotation(
            declared_return
        ) != _canonical_annotation(actual_return):
            findings.append(
                Finding(
                    "interface-signature",
                    prompt_relative,
                    f"return annotation for {name!r} is {actual_return!r}, declared {declared_return!r}",
                )
            )
    return findings


def _balanced_typescript_object(text: str, marker: re.Pattern[str]) -> str | None:
    match = marker.search(text)
    if not match:
        return None
    start = text.find("{", match.end())
    if start < 0:
        return None
    depth = 0
    quote: str | None = None
    escaped = False
    for index in range(start, len(text)):
        char = text[index]
        if quote:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == quote:
                quote = None
            continue
        if char in {'"', "'", "`"}:
            quote = char
        elif char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1 : index]
    return None


def _typescript_props(
    path: Path, component_name: str | None = None
) -> dict[str, tuple[str, bool]]:
    text = path.read_text(encoding="utf-8")
    if component_name:
        node_props = re.search(
            rf"(?:export\s+)?const\s+{re.escape(component_name)}\s*:\s*"
            r"React\.FC<NodeProps<(?P<data>\w+)>>\s*=\s*\(\s*\{(?P<fields>[^}]*)\}",
            text,
            re.S,
        )
        if node_props:
            standard = {
                "data": node_props.group("data"),
                "selected": "boolean",
                "xPos": "number",
                "yPos": "number",
            }
            names = {
                item.strip().split(":", 1)[0].strip()
                for item in node_props.group("fields").split(",")
                if item.strip()
            }
            return {name: (standard[name], True) for name in names if name in standard}
    markers = (
        *(
            (
                re.compile(rf"(?:export\s+)?interface\s+{re.escape(component_name)}Props\s*"),
                re.compile(rf"(?:export\s+)?type\s+{re.escape(component_name)}Props\s*=\s*"),
            )
            if component_name
            else ()
        ),
        re.compile(r"(?:export\s+)?interface\s+\w*Props\s*"),
        re.compile(r"(?:export\s+)?type\s+\w*Props\s*=\s*"),
    )
    body = next(
        (block for marker in markers if (block := _balanced_typescript_object(text, marker))),
        None,
    )
    if body is None:
        return {}
    props: dict[str, tuple[str, bool]] = {}
    for line in body.splitlines():
        match = re.match(r"^\s*(\w+)(\?)?\s*:\s*(.*?)\s*;\s*(?://.*)?$", line)
        if match:
            props[match.group(1)] = (re.sub(r"\s+", " ", match.group(3)).strip(), match.group(2) is None)
    return props


def _normalized_typescript(value: str) -> str:
    """Normalize superficial TypeScript declaration whitespace."""

    normalized = re.sub(r"\s+", " ", value).strip()
    normalized = re.sub(r"\s*([(),:?=<>\[\]{}|])\s*", r"\1", normalized)
    return normalized


def _typescript_exports(
    path: Path,
) -> tuple[dict[str, tuple[str | None, str | None]], set[str]]:
    """Collect exported function signatures and named type declarations."""

    text = path.read_text(encoding="utf-8")
    functions: dict[str, tuple[str | None, str | None]] = {}
    marker = re.compile(r"\bexport\s+(?:async\s+)?function\s+(\w+)\s*\(")
    for match in marker.finditer(text):
        start = match.end() - 1
        depth = 0
        quote: str | None = None
        escaped = False
        end: int | None = None
        for index in range(start, len(text)):
            char = text[index]
            if quote:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == quote:
                    quote = None
                continue
            if char in {'"', "'", "`"}:
                quote = char
            elif char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    end = index
                    break
        if end is None:
            continue
        trailer = text[end + 1 :]
        return_match = re.match(r"\s*(?::\s*([^\n{=]+))?\s*\{", trailer)
        if return_match is None:
            continue
        parameters = text[start : end + 1]
        return_type = return_match.group(1)
        functions[match.group(1)] = (
            _normalized_typescript(parameters),
            _normalized_typescript(return_type) if return_type else None,
        )
    const_marker = re.compile(
        r"\bexport\s+const\s+(\w+)\s*(?::\s*([^=\n]+(?:<[^\n]+>)?))?\s*=\s*(?:async\s*)?"
    )
    for match in const_marker.finditer(text):
        name = match.group(1)
        if "React.FC" in (match.group(2) or ""):
            functions[name] = (None, None)
            continue
        cursor = match.end()
        if cursor >= len(text) or text[cursor] != "(":
            # A React.FC annotation still proves that the named export is a
            # callable even when its destructured parameter is not recoverable.
            continue
        depth = 0
        quote: str | None = None
        escaped = False
        end: int | None = None
        for index in range(cursor, len(text)):
            char = text[index]
            if quote:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == quote:
                    quote = None
                continue
            if char in {'"', "'", "`"}:
                quote = char
            elif char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    end = index
                    break
        if end is None:
            continue
        trailer = text[end + 1 :]
        arrow = re.match(r"\s*(?::\s*([^=\n]+))?\s*=>", trailer)
        if arrow is None:
            continue
        functions[name] = (
            _normalized_typescript(text[cursor : end + 1]),
            _normalized_typescript(arrow.group(1)) if arrow.group(1) else None,
        )
    types = set(
        re.findall(r"\bexport\s+(?:interface|type|class|enum)\s+(\w+)\b", text)
    )
    return functions, types


def _typescript_interface_findings(
    prompt_relative: str,
    artifact_relative: str,
    interface: dict[str, Any],
) -> list[Finding]:
    if interface.get("type") == "module":
        actual_functions, actual_types = _typescript_exports(ROOT / artifact_relative)
        module = interface.get("module", {})
        findings: list[Finding] = []
        for item in module.get("functions", []):
            if not isinstance(item, dict) or not isinstance(item.get("name"), str):
                findings.append(
                    Finding("interface", prompt_relative, "module function entry is malformed")
                )
                continue
            name = item["name"]
            if name not in actual_functions:
                findings.append(
                    Finding(
                        "interface-code",
                        prompt_relative,
                        f"declared exported function {name!r} is absent from {artifact_relative}",
                    )
                )
                continue
            signature = item.get("signature")
            if not isinstance(signature, str) or signature in {"exported", "inferred"}:
                findings.append(
                    Finding(
                        "interface-signature",
                        prompt_relative,
                        f"declared signature for {name!r} is not concrete",
                    )
                )
            else:
                declared_parameters = re.split(r"\s+->\s+", signature, maxsplit=1)[0]
                actual_parameters = actual_functions[name][0]
                if actual_parameters is not None and _normalized_typescript(
                    declared_parameters
                ) != actual_parameters:
                    findings.append(
                        Finding(
                            "interface-signature",
                            prompt_relative,
                            f"parameter shape for {name!r} differs from {artifact_relative}",
                        )
                    )
            declared_return = item.get("returns")
            actual_return = actual_functions[name][1]
            if actual_return is not None and _normalized_typescript(
                str(declared_return or "")
            ) != actual_return:
                findings.append(
                    Finding(
                        "interface-signature",
                        prompt_relative,
                        f"return type for {name!r} differs from {artifact_relative}",
                    )
                )
        for type_name in module.get("types", []):
            if not isinstance(type_name, str) or type_name not in actual_types:
                findings.append(
                    Finding(
                        "interface-code",
                        prompt_relative,
                        f"declared exported type {type_name!r} is absent from {artifact_relative}",
                    )
                )
        return findings
    if interface.get("type") != "component":
        return []
    component = interface.get("component", {})
    actual = _typescript_props(ROOT / artifact_relative, str(component.get("name") or ""))
    declared_rows = component.get("props", [])
    declared: dict[str, tuple[str, bool]] = {}
    findings: list[Finding] = []
    for item in declared_rows:
        if not isinstance(item, dict) or not isinstance(item.get("name"), str):
            findings.append(Finding("interface", prompt_relative, "component prop entry is malformed"))
            continue
        declared[item["name"]] = (
            re.sub(r"\s+", " ", str(item.get("type") or "")).strip(),
            bool(item.get("required")),
        )
    if declared != actual:
        missing = sorted(set(declared) - set(actual))
        extra = sorted(set(actual) - set(declared))
        changed = sorted(name for name in set(actual) & set(declared) if actual[name] != declared[name])
        findings.append(
            Finding(
                "interface-signature",
                prompt_relative,
                "component props differ from "
                f"{artifact_relative} (missing={missing}, extra={extra}, changed={changed})",
            )
        )
    return findings


def _ownership_findings() -> list[Finding]:
    """Validate exact-path ownership rules without trusting sync runtime code."""

    payload = _read_json(OWNERSHIP_PATH)
    if not isinstance(payload, dict) or set(payload) != {"rules"} or not isinstance(
        payload["rules"], list
    ):
        return [Finding("ownership", OWNERSHIP_PATH.relative_to(ROOT).as_posix(), "invalid policy schema")]
    findings: list[Finding] = []
    patterns: set[str] = set()
    required = {"pattern", "inventory", "role", "owner"}
    allowed = required | {"preauthorize_absent"}
    for index, row in enumerate(payload["rules"]):
        subject = f"rule[{index}]"
        if not isinstance(row, dict) or not required.issubset(row) or set(row) - allowed:
            findings.append(Finding("ownership", subject, "malformed ownership rule"))
            continue
        pattern = row.get("pattern")
        if not isinstance(pattern, str) or not pattern or not _path_is_contained(pattern):
            findings.append(Finding("ownership", subject, "pattern is not a contained exact path"))
            continue
        if any(token in pattern for token in ("*", "?", "[")):
            findings.append(Finding("ownership", pattern, "glob ownership rules are forbidden"))
        if pattern in patterns:
            findings.append(Finding("ownership", pattern, "duplicate ownership rule"))
        patterns.add(pattern)
        if (
            row.get("inventory") != "HUMAN_OWNED"
            or row.get("owner") != "pdd-maintainers"
            or row.get("role") not in {"human-maintained", "excluded-project"}
            or not isinstance(row.get("preauthorize_absent", False), bool)
        ):
            findings.append(Finding("ownership", pattern, "unsupported ownership identity"))
        if not (ROOT / pattern).exists() and row.get("preauthorize_absent") is not True:
            findings.append(
                Finding("ownership", pattern, "owned path is absent without explicit preauthorization")
            )
    return findings


def _classification_findings(
    classifications: dict[str, Any],
    expected: set[str],
    entries: list[dict[str, Any]],
    tracked: set[str],
) -> list[Finding]:
    """Validate every exceptional inventory and dependency classification."""

    findings: list[Finding] = []
    expected_keys = {
        "schema_version",
        "human_owned_prompt_fixtures",
        "non_architectural_runtime_dependencies",
        "prompt_without_local_artifact",
        "special_prompt_outputs",
    }
    if set(classifications) != expected_keys:
        findings.append(Finding("classification", CLASSIFICATIONS_PATH.name, "unexpected schema keys"))
    by_filename = {str(row.get("filename")): row for row in entries}

    for section in (
        "human_owned_prompt_fixtures",
        "prompt_without_local_artifact",
        "special_prompt_outputs",
    ):
        value = classifications.get(section)
        if not isinstance(value, dict) or not all(
            isinstance(key, str) and isinstance(reason, str) and reason.strip()
            for key, reason in value.items()
        ):
            findings.append(Finding("classification", section, "must be a non-empty-reason path map"))
            continue
        for path in value:
            if not _path_is_contained(path) or not (ROOT / path).is_file():
                findings.append(Finding("classification", path, "classified path is missing or escapes root"))

    fixtures = classifications.get("human_owned_prompt_fixtures", {})
    if isinstance(fixtures, dict):
        for path in fixtures:
            if path in expected or path not in tracked:
                findings.append(
                    Finding("classification", path, "fixture must be tracked and outside managed inventory")
                )

    prompt_only = classifications.get("prompt_without_local_artifact", {})
    if isinstance(prompt_only, dict):
        for path in prompt_only:
            filename = path.removeprefix("pdd/prompts/")
            if path not in expected or _direct_artifact(filename) is not None or filename in by_filename:
                findings.append(
                    Finding("classification", path, "prompt-only classification conflicts with managed mappings")
                )

    special = classifications.get("special_prompt_outputs", {})
    if isinstance(special, dict):
        for prompt_path, artifact_path in special.items():
            filename = prompt_path.removeprefix("pdd/prompts/")
            if (
                prompt_path not in expected
                or not isinstance(artifact_path, str)
                or not _path_is_contained(artifact_path)
                or not (ROOT / artifact_path).is_file()
                or by_filename.get(filename, {}).get("filepath") != artifact_path
            ):
                findings.append(Finding("classification", prompt_path, "invalid special-output mapping"))

    rows = classifications.get("non_architectural_runtime_dependencies")
    if not isinstance(rows, list):
        return findings + [
            Finding("classification", "non_architectural_runtime_dependencies", "must be a list")
        ]
    identities: set[tuple[str, str]] = set()
    for index, row in enumerate(rows):
        subject = f"non_architectural_runtime_dependencies[{index}]"
        if not isinstance(row, dict) or set(row) != {
            "from_prompt",
            "omitted_architecture_dependencies",
            "reason",
            "runtime_artifact",
        }:
            findings.append(Finding("classification", subject, "malformed runtime dependency row"))
            continue
        from_prompt = row.get("from_prompt")
        artifact = row.get("runtime_artifact")
        omitted = row.get("omitted_architecture_dependencies")
        if (
            not isinstance(from_prompt, str)
            or from_prompt not in expected
            or not isinstance(artifact, str)
            or not _path_is_contained(artifact)
            or not (ROOT / artifact).is_file()
            or not isinstance(row.get("reason"), str)
            or len(row["reason"].strip()) < 40
            or not isinstance(omitted, list)
            or not omitted
            or not all(isinstance(item, str) for item in omitted)
        ):
            findings.append(Finding("classification", subject, "invalid runtime dependency evidence"))
            continue
        filename = from_prompt.removeprefix("pdd/prompts/")
        prompt_dependencies = parse_prompt_metadata(ROOT / from_prompt).dependencies or ()
        architecture_dependencies = by_filename.get(filename, {}).get("dependencies", [])
        artifact_text = (ROOT / artifact).read_text(encoding="utf-8")
        for dependency in omitted:
            identity = (from_prompt, dependency)
            if identity in identities:
                findings.append(Finding("classification", subject, "duplicate omitted dependency"))
            identities.add(identity)
            module_name = dependency.removesuffix("_python.prompt").replace("/", ".")
            if dependency not in by_filename:
                findings.append(Finding("classification", subject, f"unknown dependency {dependency}"))
            if dependency in prompt_dependencies or dependency in architecture_dependencies:
                findings.append(Finding("classification", subject, f"omitted edge is still registered: {dependency}"))
            if module_name.rsplit(".", 1)[-1] not in artifact_text:
                findings.append(Finding("classification", subject, f"runtime artifact lacks evidence for {dependency}"))
    return findings


def _architecture_graph_findings(entries: list[dict[str, Any]]) -> list[Finding]:
    """Require one acyclic, dependency-first architecture order."""

    findings: list[Finding] = []
    unique = {
        str(row.get("filename")): row
        for row in entries
        if isinstance(row.get("filename"), str)
    }
    priorities: dict[str, int] = {}
    seen_priorities: set[int] = set()
    for name, row in unique.items():
        priority = row.get("priority")
        if not isinstance(priority, int) or isinstance(priority, bool) or priority <= 0:
            findings.append(Finding("architecture-priority", name, "priority must be a positive integer"))
            continue
        priorities[name] = priority
        if priority in seen_priorities:
            findings.append(Finding("architecture-priority", name, f"duplicate priority {priority}"))
        seen_priorities.add(priority)
    graph = {
        name: {str(dep) for dep in row.get("dependencies", []) if str(dep) in unique}
        for name, row in unique.items()
    }
    for name, dependencies in graph.items():
        for dependency in dependencies:
            if name in priorities and dependency in priorities and priorities[dependency] >= priorities[name]:
                findings.append(
                    Finding(
                        "architecture-priority",
                        name,
                        f"dependency {dependency} must have a lower priority",
                    )
                )
    remaining = {name: set(dependencies) for name, dependencies in graph.items()}
    ready = sorted(name for name, dependencies in remaining.items() if not dependencies)
    consumed: set[str] = set()
    while ready:
        name = ready.pop(0)
        consumed.add(name)
        for candidate, dependencies in remaining.items():
            dependencies.discard(name)
            if not dependencies and candidate not in consumed and candidate not in ready:
                ready.append(candidate)
        ready.sort()
    cyclic = sorted(set(graph) - consumed)
    if cyclic:
        findings.append(
            Finding("architecture-cycle", ", ".join(cyclic), "dependency graph contains a cycle")
        )
    return findings


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _fingerprint_counts(
    entries: list[dict[str, Any]], tracked: set[str]
) -> dict[str, int]:
    """Report legacy evidence freshness without certifying or rewriting it."""

    meta_root = ROOT / ".pdd" / "meta"
    fingerprints: list[Path] = []
    run_reports = 0
    for path in sorted(meta_root.glob("*.json")):
        if path.relative_to(ROOT).as_posix() not in tracked:
            continue
        if path.name.endswith("_run.json"):
            run_reports += 1
            continue
        try:
            payload = _read_json(path)
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(payload, dict) and {"prompt_hash", "code_hash"}.issubset(payload):
            fingerprints.append(path)
    by_key = {
        str(row.get("filename", "")).removesuffix(".prompt").replace("/", "_"): row
        for row in entries
    }
    fresh = 0
    mapped = 0
    for path in fingerprints:
        payload = _read_json(path)
        row = by_key.get(path.stem)
        if row is None:
            continue
        mapped += 1
        prompt = PROMPTS_ROOT / str(row["filename"])
        artifact = ROOT / str(row["filepath"])
        current = (
            prompt.is_file()
            and artifact.is_file()
            and payload.get("prompt_hash") == _sha256(prompt)
            and payload.get("code_hash") == _sha256(artifact)
        )
        include_deps = payload.get("include_deps") or {}
        if not isinstance(include_deps, dict):
            current = False
        else:
            for relative, digest in include_deps.items():
                candidates = (PROMPTS_ROOT / str(relative), ROOT / str(relative))
                include_path = next((candidate for candidate in candidates if candidate.is_file()), None)
                if include_path is None or digest != _sha256(include_path):
                    current = False
        test_files = payload.get("test_files") or {}
        if not isinstance(test_files, dict):
            current = False
        else:
            for relative, digest in test_files.items():
                candidates = [ROOT / str(relative), ROOT / "tests" / str(relative)]
                test_path = next((candidate for candidate in candidates if candidate.is_file()), None)
                if test_path is None or digest != _sha256(test_path):
                    current = False
        if current:
            fresh += 1
    return {
        "fingerprints": len(fingerprints),
        "fingerprints_architecture_mapped": mapped,
        "fingerprints_fresh_minimum": fresh,
        "fingerprints_stale_or_unknown": len(fingerprints) - fresh,
        "legacy_run_reports": run_reports,
    }


def audit() -> tuple[dict[str, int], list[Finding]]:
    """Return deterministic counts and findings for the checked-out tree."""

    tracked = _git_tracked_paths()
    expected = _expected_prompts()
    expected_units = _expected_units()
    classifications = _classifications()
    entries = _architecture_entries()
    findings: list[Finding] = []
    findings.extend(_ownership_findings())
    findings.extend(_classification_findings(classifications, expected, entries, tracked))
    verification_profile_count, verification_findings = _verification_profile_findings(
        expected_units
    )
    findings.extend(verification_findings)
    requirement_rotation_count, requirement_rotation_findings = _requirement_rotation_findings()
    findings.extend(requirement_rotation_findings)

    actual_prompts = {
        path.relative_to(ROOT).as_posix()
        for path in PROMPTS_ROOT.rglob("*.prompt")
        if path.relative_to(ROOT).as_posix() in tracked
    }
    fixture_prompts = set(classifications.get("human_owned_prompt_fixtures", {}))
    untracked_expected = expected - actual_prompts
    unexpected_managed = actual_prompts - expected - fixture_prompts
    for path in sorted(untracked_expected):
        findings.append(Finding("inventory", path, "expected managed prompt is missing"))
    for path in sorted(unexpected_managed):
        findings.append(
            Finding("inventory", path, "tracked prompt is neither managed nor classified fixture")
        )

    by_filename: dict[str, list[dict[str, Any]]] = {}
    by_filepath: dict[str, list[dict[str, Any]]] = {}
    for index, entry in enumerate(entries):
        subject = str(entry.get("filename") or entry.get("filepath") or f"entry[{index}]")
        missing = sorted(REQUIRED_ARCHITECTURE_FIELDS - set(entry))
        if missing:
            findings.append(
                Finding("architecture", subject, f"missing fields: {', '.join(missing)}")
            )
        if not isinstance(entry.get("description"), str) or not entry["description"].strip():
            findings.append(Finding("architecture", subject, "description must be non-empty text"))
        filename = str(entry.get("filename") or "")
        filepath = str(entry.get("filepath") or "")
        by_filename.setdefault(filename, []).append(entry)
        by_filepath.setdefault(filepath, []).append(entry)

        if filename.startswith(("pdd/", "prompts/", "/")) or ".." in PurePosixPath(filename).parts:
            findings.append(
                Finding("architecture-path", subject, "filename must be relative to pdd/prompts")
            )
        prompt_path = f"pdd/prompts/{filename}"
        if prompt_path not in tracked or not (ROOT / prompt_path).is_file():
            findings.append(
                Finding("architecture-path", subject, f"prompt does not exist: {prompt_path}")
            )
            continue
        if not filepath or not _path_is_contained(filepath) or not (ROOT / filepath).exists():
            findings.append(
                Finding("architecture-path", subject, f"artifact does not exist or escapes root: {filepath}")
            )

        findings.extend(_interface_shape_findings(filename, entry.get("interface")))
        metadata = parse_prompt_metadata(ROOT / prompt_path)
        if metadata.interface_error:
            findings.append(
                Finding("prompt-metadata", filename, f"invalid <pdd-interface>: {metadata.interface_error}")
            )
        if metadata.reason is None:
            findings.append(Finding("prompt-metadata", filename, "registered prompt is missing pdd-reason"))
        if metadata.interface is None:
            findings.append(Finding("prompt-metadata", filename, "registered prompt is missing pdd-interface"))
        if entry.get("dependencies") and metadata.dependencies is None:
            findings.append(
                Finding("prompt-metadata", filename, "registered dependencies are absent from prompt metadata")
            )
        weak_prefixes = (
            "you are",
            "write ",
            "create ",
            "build ",
            "implement ",
            "generate ",
            "as ",
            "module ",
            "the click ",
            "provide ",
            "defines the verified",
            "based on",
            "(default export",
            "the prompt file",
            "1)",
        )
        architecture_reason = re.sub(r"\s+", " ", str(entry.get("reason") or "")).strip()
        if not 60 <= len(architecture_reason) <= 120 or architecture_reason.lower().startswith(
            weak_prefixes
        ):
            findings.append(
                Finding(
                    "reason-quality",
                    filename,
                    "architecture reason must state module purpose concisely (60-120 characters)",
                )
            )
        if metadata.reason is not None:
            if not 60 <= len(metadata.reason) <= 120 or metadata.reason.lower().startswith(
                weak_prefixes
            ):
                findings.append(
                    Finding(
                        "reason-quality",
                        filename,
                        "pdd-reason must state module purpose concisely (60-120 characters)",
                    )
                )
            if metadata.reason != architecture_reason:
                findings.append(
                    Finding("metadata-drift", filename, "prompt reason differs from architecture reason")
                )
        if metadata.interface is not None:
            if metadata.interface != entry.get("interface"):
                findings.append(
                    Finding("metadata-drift", filename, "prompt interface differs from architecture interface")
                )
            direct = _direct_artifact(filename)
            if direct:
                if direct[0] == "python":
                    findings.extend(
                        _python_interface_findings(filename, direct[1], metadata.interface)
                    )
                elif direct[0] in {"typescript", "typescriptreact"}:
                    findings.extend(
                        _typescript_interface_findings(filename, direct[1], metadata.interface)
                    )
        if metadata.dependencies is not None and list(metadata.dependencies) != entry.get(
            "dependencies", []
        ):
            findings.append(
                Finding("metadata-drift", filename, "prompt dependencies differ from architecture dependencies")
            )

    for filename, rows in sorted(by_filename.items()):
        if filename and len(rows) > 1:
            findings.append(
                Finding("architecture-duplicate", filename, f"registered {len(rows)} times")
            )
    for filepath, rows in sorted(by_filepath.items()):
        if filepath and len(rows) > 1:
            findings.append(
                Finding("architecture-duplicate", filepath, f"registered {len(rows)} times")
            )

    registered_prompts = {f"pdd/prompts/{name}" for name in by_filename if name}
    prompt_only = set(classifications.get("prompt_without_local_artifact", {}))
    special_outputs = classifications.get("special_prompt_outputs", {})
    for prompt_path in sorted(expected):
        prompt_relative = prompt_path.removeprefix("pdd/prompts/")
        direct = _direct_artifact(prompt_relative)
        if direct:
            metadata = parse_prompt_metadata(ROOT / prompt_path)
            if metadata.reason is None:
                findings.append(
                    Finding("prompt-metadata", prompt_relative, "direct unit is missing pdd-reason")
                )
            if metadata.interface is None:
                findings.append(
                    Finding("prompt-metadata", prompt_relative, "direct unit is missing pdd-interface")
                )
            rows = by_filename.get(prompt_relative, [])
            exact = [row for row in rows if row.get("filepath") == direct[1]]
            if len(exact) != 1:
                findings.append(
                    Finding(
                        "direct-pair",
                        prompt_relative,
                        f"expected exactly one architecture mapping to {direct[1]}",
                    )
                )
            continue
        if prompt_path in special_outputs:
            metadata = parse_prompt_metadata(ROOT / prompt_path)
            if metadata.reason is None or metadata.interface is None:
                findings.append(
                    Finding(
                        "prompt-metadata",
                        prompt_relative,
                        "special-output unit must declare pdd-reason and pdd-interface",
                    )
                )
            output = special_outputs[prompt_path]
            rows = by_filename.get(prompt_relative, [])
            if len(rows) != 1 or rows[0].get("filepath") != output:
                findings.append(
                    Finding(
                        "special-output",
                        prompt_relative,
                        f"expected architecture mapping to {output}",
                    )
                )
            continue
        if prompt_path not in registered_prompts and prompt_path not in prompt_only:
            findings.append(
                Finding(
                    "inventory",
                    prompt_path,
                    "managed prompt has no architecture entry or reviewed prompt-only classification",
                )
            )

    known_dependencies = set(by_filename)
    classified_prompt_names = {
        path.removeprefix("pdd/prompts/") for path in prompt_only
    }
    for entry in entries:
        for dependency in entry.get("dependencies", []):
            if dependency not in known_dependencies and dependency not in classified_prompt_names:
                findings.append(
                    Finding(
                        "architecture-dependency",
                        str(entry.get("filename")),
                        f"unresolved dependency {dependency!r}",
                    )
                )

    findings.extend(_architecture_graph_findings(entries))

    fingerprint_counts = _fingerprint_counts(entries, tracked)

    counts = {
        "architecture_entries": len(entries),
        "direct_prompt_artifact_pairs": sum(
            _direct_artifact(path.removeprefix("pdd/prompts/")) is not None
            for path in expected
        ),
        "expected_managed_prompts": len(expected),
        "findings": len(set(findings)),
        "prompt_only_classifications": len(prompt_only),
        "tracked_prompts": len(actual_prompts),
        "verification_profiles": verification_profile_count,
        "requirement_rotations": requirement_rotation_count,
        **fingerprint_counts,
    }
    return counts, sorted(set(findings))


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit stable JSON")
    args = parser.parse_args(list(argv) if argv is not None else None)
    counts, findings = audit()
    if args.json:
        print(
            json.dumps(
                {"counts": counts, "findings": [asdict(item) for item in findings]},
                indent=2,
                sort_keys=True,
            )
        )
    else:
        print("Repository sync audit")
        for key, value in counts.items():
            print(f"  {key}: {value}")
        for finding in findings:
            print(f"[{finding.category}] {finding.subject}: {finding.detail}")
    return 1 if findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
