#!/usr/bin/env python3
# Mirror of scripts/ci_detect_changed_modules.py — edit there, not here.
# The packaged copy exists so `from pdd.ci_detect_changed_modules import main`
# keeps working for legacy callers; scripts/ is the canonical CI entry point.
"""Detect PDD module basenames affected by a git diff.

Ported from the inline bash+python block in .github/workflows/auto-heal-drift.yml
so it can run identically on GitHub Actions and Google Cloud Build.

Usage:
    python scripts/ci_detect_changed_modules.py --diff-base 'origin/main...HEAD'
    python scripts/ci_detect_changed_modules.py --diff-base 'HEAD~1'

Prints a single line with comma-separated module identities, or an empty line
if no PDD-managed files changed. Git and canonical-ownership failures exit 2.
"""
from __future__ import annotations

import argparse
import ast
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import NamedTuple

PDD_PATH_PREFIXES = ("pdd/", "prompts/", "context/", "tests/")
# Package execution shims and CI helper scripts are not PDD dev units;
# auto-heal must not try to generate examples for them in headless CI.
EXCLUDED_MODULE_BASENAMES = {
    "__main__",
    "ci_detect_changed_modules",
    # The prompt for this script lives at pdd/prompts/scripts/..., so its
    # _prompt_basename_from_path output is path-qualified as
    # "scripts/ci_detect_changed_modules". Exclude that form too so a change
    # to the prompt itself does not trigger auto-heal against a bogus
    # pdd/scripts/ci_detect_changed_modules.py path.
    "scripts/ci_detect_changed_modules",
    # Hosted Playwright provisioning is workflow-owned, not a PDD module.
    "sync_core/playwright_toolchain",
    # Public release sync is an operational packaging helper, not a
    # prompt-managed PDD module.
    "copy_package_data_to_public",
    # These canonical PDD Cloud prompts are packaged with PDD so logical
    # prompt paths resolve, but their code files live in pdd_cloud's
    # extensions/github_pdd_app tree, not this repository's pdd/ package.
    "src/clients/github_client",
    "src/pdd_issue_runner_job",
    "src/services/pdd_issue_completion_evidence",
    # The model catalog score refresh is intentionally agent-reviewed and
    # manifest-driven. Headless auto-heal should not regenerate this module:
    # it can enter interactive agent auth while trying to rewrite the full
    # generator, and the reviewed manifest/schema/tests are the audit surface.
    "generate_model_catalog",
}

# Prompt file names follow prompts/[subdir/...]/{basename}_{language}.prompt.
_PROMPT_FILENAME = re.compile(r"^(.*)_([^_]+)\.prompt$")
_INCLUDE_OPEN_TAG = re.compile(
    r"<(?P<tag>include(?:-many)?)(?P<attrs>[^>]*)>",
    re.DOTALL,
)
_SELECT_ATTR = re.compile(r"""\bselect\s*=\s*(['"])(.*?)\1""", re.DOTALL)
_PATH_ATTR = re.compile(r"""\bpath\s*=\s*(['"])(.*?)\1""", re.DOTALL)
_PROMPT_DIRS = ("prompts/", "pdd/prompts/")
_SYNC_OWNERSHIP_PATH = ".pdd/sync-ownership.json"
_INCLUDE_PATH_SUFFIXES = (
    ".bash",
    ".csv",
    ".html",
    ".java",
    ".js",
    ".json",
    ".md",
    ".prompt",
    ".py",
    ".rb",
    ".rs",
    ".rst",
    ".sh",
    ".toml",
    ".ts",
    ".tsx",
    ".txt",
    ".yaml",
    ".yml",
)


class _ReverseDepContext(NamedTuple):
    """Shared immutable inputs and mutable parse cache for closure traversal."""

    repo_root: Path
    changed_paths: set[str]
    changed_defs_by_path: dict[str, set[str] | None]
    refs_by_path: dict[str, list[tuple[str, set[str] | None]]]


class _ModuleOwnership(NamedTuple):
    """Canonical architecture identities used at the changed-file boundary."""

    code_paths: dict[str, str]
    prompt_paths: dict[str, str]
    canonical_names: dict[str, str]
    flattened_names: dict[str, set[str]]
    leaf_names: dict[str, set[str]]


def _git_changed_files(diff_base: str) -> list[str]:
    """Return changed files restricted to PDD-managed prefixes."""
    cmd = ["git", "diff", "--name-only", diff_base, "--", *PDD_PATH_PREFIXES]
    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def _normalize_repo_path(path: str) -> str:
    """Normalize repo-relative paths for matching include references."""
    normalized = os.path.normpath(path.strip()).replace("\\", "/")
    if normalized == ".":
        return ""
    while normalized.startswith("./"):
        normalized = normalized[2:]
    return normalized


def _prompt_basename_from_path(path: str) -> str | None:
    """Return module basename from prompts/[subdir]/name_lang.prompt paths."""
    normalized = _normalize_repo_path(path)
    for prompt_dir in _PROMPT_DIRS:
        prefix = _normalize_repo_path(prompt_dir) + "/"
        if not normalized.startswith(prefix):
            continue
        relative = normalized[len(prefix):]
        match = _PROMPT_FILENAME.match(relative)
        if not match:
            return None
        return match.group(1)
    return None


def _context_basename_from_path(path: str) -> str | None:
    """Return module basename from context/[subdir]/name_example.ext paths."""
    normalized = _normalize_repo_path(path)
    for prefix in ("context/", "pdd/context/"):
        if not normalized.startswith(prefix):
            continue
        relative = normalized[len(prefix):]
        rel_path = Path(relative)
        stem = rel_path.stem
        if not stem.endswith("_example"):
            return None
        basename = stem[: -len("_example")]
        parent = rel_path.parent.as_posix()
        return f"{parent}/{basename}" if parent != "." else basename
    return None


def _test_basename_from_path(path: str) -> str | None:
    """Return module basename from tests/[subdir]/test_name.py paths."""
    normalized = _normalize_repo_path(path)
    prefix = "tests/"
    if not normalized.startswith(prefix) or not normalized.endswith(".py"):
        return None
    relative = normalized[len(prefix):]
    rel_path = Path(relative)
    if not rel_path.name.startswith("test_"):
        return None
    basename = rel_path.stem[len("test_") :]
    parent = rel_path.parent.as_posix()
    return f"{parent}/{basename}" if parent != "." else basename


def _basename_from_path(path: str) -> str | None:
    prompt_basename = _prompt_basename_from_path(path)
    if prompt_basename:
        return None if prompt_basename in EXCLUDED_MODULE_BASENAMES else prompt_basename

    normalized = _normalize_repo_path(path)
    if normalized.startswith("pdd/") and normalized.endswith(".py"):
        basename = normalized[len("pdd/") : -len(".py")]
        # Skip root package shims only; nested __init__.py files map to real
        # prompt basenames like commands/__init__ and server/routes/__init__.
        if basename == "__init__" or basename in EXCLUDED_MODULE_BASENAMES:
            return None
        return basename

    context_basename = _context_basename_from_path(path)
    if context_basename:
        return None if context_basename in EXCLUDED_MODULE_BASENAMES else context_basename

    test_basename = _test_basename_from_path(path)
    if test_basename:
        return None if test_basename in EXCLUDED_MODULE_BASENAMES else test_basename

    return None


def _architecture_modules() -> list[dict[str, object]]:
    """Load architecture module rows without importing candidate code."""
    architecture_path = Path("architecture.json")
    try:
        payload = json.loads(architecture_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot load canonical module ownership: {exc}") from exc
    if isinstance(payload, dict):
        payload = payload.get("modules", [])
    if not isinstance(payload, list):
        raise ValueError("cannot load canonical module ownership: expected a module list")
    return [row for row in payload if isinstance(row, dict)]


def _module_name_from_architecture_filename(filename: str) -> str | None:
    """Return the prompt-relative module identity from an architecture row."""
    normalized = _normalize_repo_path(filename)
    for prefix in ("prompts/", "pdd/prompts/"):
        if normalized.startswith(prefix):
            normalized = normalized[len(prefix) :]
            break
    match = _PROMPT_FILENAME.match(normalized)
    return match.group(1) if match else None


def _canonical_ownership_rows() -> list[tuple[str, str, str]]:
    """Collect canonical prompt/code rows from architecture and legacy prompts."""
    rows: list[tuple[str, str, str]] = []
    owned_names: set[str] = set()
    for row in _architecture_modules():
        filename = row.get("filename")
        filepath = row.get("filepath")
        if not isinstance(filename, str) or not isinstance(filepath, str):
            continue
        canonical = _module_name_from_architecture_filename(filename)
        code_path = _normalize_repo_path(filepath)
        if not canonical or not code_path:
            continue
        rows.append((canonical, code_path, _normalize_repo_path(filename)))
        owned_names.add(canonical)

    # A checked-in canonical prompt is also ownership evidence for older units
    # that have not yet been backfilled into architecture.json.
    for prompt_dir in _PROMPT_DIRS:
        prompt_root = Path(prompt_dir)
        if not prompt_root.is_dir():
            continue
        for prompt_path in prompt_root.rglob("*.prompt"):
            relative = prompt_path.relative_to(prompt_root).as_posix()
            canonical = _module_name_from_architecture_filename(relative)
            if not canonical or canonical in owned_names:
                continue
            code_path = f"pdd/{canonical}.py"
            if not Path(code_path).is_file():
                continue
            rows.append((canonical, code_path, relative))
            owned_names.add(canonical)
    return rows


def _module_ownership() -> _ModuleOwnership:
    """Build exact and compatibility lookups for architecture-owned modules."""
    rows = _canonical_ownership_rows()
    code_leaves: dict[str, set[str]] = {}
    for _canonical, code_path, _filename in rows:
        code_leaves.setdefault(Path(code_path).stem, set()).add(code_path)

    code_paths: dict[str, str] = {}
    prompt_paths: dict[str, str] = {}
    canonical_names: dict[str, str] = {}
    flattened_names: dict[str, set[str]] = {}
    leaf_names: dict[str, set[str]] = {}
    for canonical, code_path, filename in rows:
        target = canonical
        if "/" not in canonical and len(code_leaves.get(Path(code_path).stem, set())) > 1:
            target = str(Path(code_path).with_suffix("")).replace("\\", "/")
        code_paths[code_path] = target
        if filename:
            if filename.startswith(("prompts/", "pdd/prompts/")):
                prompt_paths[filename] = target
            else:
                prompt_paths[f"prompts/{filename}"] = target
                prompt_paths[f"pdd/prompts/{filename}"] = target
        canonical_names[canonical] = target
        flattened_names.setdefault(canonical.replace("/", "_"), set()).add(target)
        leaf_names.setdefault(canonical.rsplit("/", 1)[-1], set()).add(target)
    return _ModuleOwnership(
        code_paths, prompt_paths, canonical_names, flattened_names, leaf_names
    )


def _protected_human_pattern(row: object) -> str | None:
    """Return one strict exact human-owned path, or reject the policy row."""
    required = {"pattern", "inventory", "role", "owner"}
    if not isinstance(row, dict) or not required.issubset(row):
        return None
    if set(row) - (required | {"preauthorize_absent"}):
        return None
    if (
        row.get("inventory") != "HUMAN_OWNED"
        or row.get("owner") != "pdd-maintainers"
        or row.get("role") not in {"human-maintained", "excluded-project"}
    ):
        return None
    pattern = row.get("pattern")
    if not isinstance(pattern, str) or not pattern or pattern.startswith("/"):
        return None
    if any(token in pattern for token in ("*", "?", "[")):
        return None
    return pattern if _normalize_repo_path(pattern) == pattern else None


def _protected_human_owned_paths(diff_base: str) -> set[str]:
    """Load exact non-generated ownership only from the protected Git base."""
    base_ref = _diff_base_ref(diff_base)
    result = subprocess.run(
        ["git", "show", f"{base_ref}:{_SYNC_OWNERSHIP_PATH}"],
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        return set()
    try:
        payload = json.loads(result.stdout)
    except (json.JSONDecodeError, UnicodeDecodeError):
        return set()
    rows = payload.get("rules") if isinstance(payload, dict) else None
    if not isinstance(rows, list):
        return set()

    patterns = (_protected_human_pattern(row) for row in rows)
    return {pattern for pattern in patterns if pattern is not None}


def _resolve_candidate(candidate: str, source_path: str, ownership: _ModuleOwnership) -> str:
    """Resolve an inferred alias to one canonical target or fail closed."""
    exact = ownership.canonical_names.get(candidate)
    if exact:
        return exact
    choices = ownership.flattened_names.get(candidate, set())
    if not choices:
        choices = ownership.leaf_names.get(candidate, set())
    if len(choices) == 1:
        return next(iter(choices))
    if len(choices) > 1:
        rendered = ", ".join(sorted(choices))
        raise ValueError(
            f"ambiguous auto-heal module ownership for {source_path}: "
            f"{candidate!r} maps to {rendered}"
        )
    raise ValueError(
        f"unmapped auto-heal module candidate for {source_path}: {candidate!r}; "
        "add or correct its architecture.json ownership"
    )


def _test_import_owners(path: str, ownership: _ModuleOwnership) -> set[str]:
    """Return exact canonical owners imported by a non-conventional test."""
    try:
        tree = ast.parse(Path(path).read_text(encoding="utf-8"), filename=path)
    except (OSError, UnicodeError, SyntaxError):
        return set()

    imported_modules: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported_modules.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imported_modules.add(node.module)
            imported_modules.update(
                f"{node.module}.{alias.name}"
                for alias in node.names
                if alias.name != "*"
            )

    owners: set[str] = set()
    for imported in imported_modules:
        if imported != "pdd" and not imported.startswith("pdd."):
            continue
        code_path = f"{imported.replace('.', '/')}.py"
        owner = ownership.code_paths.get(code_path)
        if owner:
            owners.add(owner)
    return owners


def _module_from_path(path: str, ownership: _ModuleOwnership) -> set[str]:
    """Map one changed path to one or more canonical module owners."""
    normalized = _normalize_repo_path(path)
    candidate = _basename_from_path(normalized)
    if candidate is None:
        return set()
    if normalized in ownership.code_paths:
        return {ownership.code_paths[normalized]}
    if normalized in ownership.prompt_paths:
        return {ownership.prompt_paths[normalized]}

    exact = ownership.canonical_names.get(candidate)
    inferred = ownership.flattened_names.get(candidate, set())
    if not inferred:
        inferred = ownership.leaf_names.get(candidate, set())
    if exact or inferred:
        return {_resolve_candidate(candidate, normalized, ownership)}

    if normalized.startswith("tests/"):
        imported_owners = _test_import_owners(normalized, ownership)
        if imported_owners:
            return imported_owners
    return {_resolve_candidate(candidate, normalized, ownership)}


def _extract_include_paths(content: str) -> list[str]:
    """Return normalized include targets from <include> and <include-many> tags."""
    return [path for path, _selected_defs in _extract_include_refs(content)]


def _extract_include_refs(content: str) -> list[tuple[str, set[str] | None]]:
    """Return include targets with optional function selectors.

    A ``None`` selector means "conservative match": either the include has no
    select attribute, or it uses a selector type this detector cannot map to
    Python function definitions.
    """
    refs: list[tuple[str, set[str] | None]] = []
    pos = 0
    while True:
        start = content.find("<include", pos)
        if start == -1:
            break
        match = _INCLUDE_OPEN_TAG.match(content, start)
        if not match:
            pos = start + 1
            continue

        attrs = match.group("attrs") or ""
        tag = match.group("tag")
        selected_defs = _selected_defs_from_attrs(attrs)
        path_attr = _path_from_attrs(attrs) if tag == "include" else None
        if attrs.rstrip().endswith("/"):
            if path_attr is not None:
                normalized = _normalize_repo_path(path_attr)
                if _looks_like_include_target(normalized):
                    refs.append((normalized, selected_defs))
            pos = match.end()
            continue

        close_tag = f"</{tag}>"
        close_start = content.find(close_tag, match.end())
        if close_start == -1:
            pos = match.end()
            continue

        body = content[match.end() : close_start]
        # Prompt prose sometimes mentions literal <include> tags before a real
        # include block. If a candidate body contains another include opener,
        # this was prose, so advance one byte and let the real tag match next.
        if path_attr is None and "<include" in body:
            pos = start + 1
            continue

        parts = [path_attr] if path_attr is not None else re.split(r"[,\n]", body)
        for part in parts:
            normalized = _normalize_repo_path(part)
            if _looks_like_include_target(normalized):
                refs.append((normalized, selected_defs))
        pos = close_start + len(close_tag)
    return refs


def _looks_like_include_target(path: str) -> bool:
    """Return True for normalized include bodies that look like file paths."""
    if not path or "<" in path or ">" in path:
        return False
    if any(char.isspace() for char in path):
        return False
    return path.endswith(_INCLUDE_PATH_SUFFIXES)


def _selected_defs_from_attrs(attrs: str) -> set[str] | None:
    """Extract ``def:name`` selectors from include tag attributes."""
    match = _SELECT_ATTR.search(attrs)
    if not match:
        return None

    selected_defs: set[str] = set()
    for raw_selector in match.group(2).split(","):
        selector = raw_selector.strip()
        if not selector:
            continue
        if not selector.startswith("def:"):
            return None
        name = selector[len("def:") :].strip()
        if name:
            selected_defs.add(name)

    return selected_defs or None


def _path_from_attrs(attrs: str) -> str | None:
    """Return the declared include path, preserving path-over-body precedence."""
    match = _PATH_ATTR.search(attrs)
    return match.group(2).strip() if match else None


def _diff_base_ref(diff_base: str) -> str:
    """Return the left-hand git ref from a diff expression."""
    if "..." in diff_base:
        return diff_base.split("...", 1)[0]
    if ".." in diff_base:
        return diff_base.split("..", 1)[0]
    return diff_base


def _function_dumps(source: str) -> dict[str, str]:
    """Return AST dumps for Python function definitions in source."""
    tree = ast.parse(source)
    functions: dict[str, str] = {}
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            functions[node.name] = ast.dump(node, include_attributes=False)
    return functions


def _changed_python_defs(path: str, diff_base: str | None) -> set[str] | None:
    """Return changed Python function names for path, or None if unknown."""
    if diff_base is None or not path.endswith(".py"):
        return None

    try:
        current_source = Path(path).read_text(encoding="utf-8")
        current_funcs = _function_dumps(current_source)
    except (OSError, SyntaxError):
        return None

    base_ref = _diff_base_ref(diff_base)
    try:
        result = subprocess.run(
            ["git", "show", f"{base_ref}:{path}"],
            capture_output=True,
            text=True,
            timeout=30,
        )
    except Exception:
        return None

    if result.returncode != 0:
        old_funcs: dict[str, str] = {}
    else:
        try:
            old_funcs = _function_dumps(result.stdout)
        except SyntaxError:
            return None

    changed_defs = {
        name
        for name, dumped in current_funcs.items()
        if old_funcs.get(name) != dumped
    }
    changed_defs.update(name for name in old_funcs if name not in current_funcs)
    return changed_defs


def _resolved_include_targets(
    include_path: str, prompt_path: Path, repo_root: Path
) -> set[str]:
    """Return normalized, in-repository paths an include can resolve to.

    Include processing resolves a repository-relative target before trying the
    including prompt's directory. Preserve that precedence whenever a target
    exists. For a deleted target, return the distinct valid candidates so the
    caller can still detect a reverse dependency when exactly one changed path
    matches; multiple changed candidates remain deliberately ambiguous.
    """
    target = Path(include_path)
    if target.is_absolute():
        return set()

    candidates: list[str] = []
    for root in _include_resolution_roots(prompt_path, repo_root):
        try:
            resolved = (root / target).resolve()
            relative = resolved.relative_to(repo_root).as_posix()
        except (OSError, ValueError):
            continue
        normalized = _normalize_repo_path(relative)
        if not normalized or normalized in candidates:
            continue
        candidates.append(normalized)
        if resolved.exists():
            return {normalized}
    return set(candidates)


def _include_resolution_roots(prompt_path: Path, repo_root: Path) -> tuple[Path, ...]:
    """Return repository, prompt, and projected-source roots in precedence order."""
    prompt_resolved = prompt_path.resolve()
    roots = [repo_root, prompt_resolved.parent]
    try:
        relative = prompt_resolved.relative_to(repo_root)
    except ValueError:
        return tuple(roots)

    prompt_indexes = [
        index for index, part in enumerate(relative.parts) if part == "prompts"
    ]
    if prompt_indexes:
        index = prompt_indexes[-1]
        projected_file = repo_root.joinpath(
            *relative.parts[:index], *relative.parts[index + 1 :]
        )
        roots.append(projected_file.parent)
    return tuple(dict.fromkeys(roots))


def _include_matches_changed(
    selected_defs: set[str] | None,
    changed_path: str,
    changed_defs_by_path: dict[str, set[str] | None],
) -> bool:
    """Return True when selectors permit a resolved include to react."""

    if selected_defs is None:
        return True

    changed_defs = changed_defs_by_path.get(changed_path)
    if changed_defs is None:
        return True

    return bool(selected_defs & changed_defs)


def _matching_changed_path(
    include_path: str,
    prompt_path: Path,
    repo_root: Path,
    changed_paths: set[str],
) -> str | None:
    """Return the sole changed file an include resolves to, if unambiguous."""
    matched_paths = (
        _resolved_include_targets(include_path, prompt_path, repo_root)
        & changed_paths
    )
    return next(iter(matched_paths)) if len(matched_paths) == 1 else None


def _reverse_dep_basename_for_prompt(
    prompt_file: Path,
    context: _ReverseDepContext,
) -> str | None:
    """Return a prompt basename when its recursive closure reaches a change."""
    prompt_basename = _prompt_basename_from_path(prompt_file.as_posix())
    if not prompt_basename:
        return None
    if _source_reaches_changed_path(
        prompt_file,
        context,
    ):
        return prompt_basename
    return None


def _source_reaches_changed_path(
    source_file: Path,
    context: _ReverseDepContext,
) -> bool:
    """Walk one include closure iteratively with deterministic cycle protection."""
    pending = [source_file]
    visited: set[str] = set()
    while pending:
        current_file = pending.pop()
        try:
            source_path = (
                current_file.resolve().relative_to(context.repo_root).as_posix()
            )
        except (OSError, ValueError):
            continue
        if source_path in visited:
            continue
        visited.add(source_path)

        if source_path not in context.refs_by_path:
            try:
                content = current_file.read_text(encoding="utf-8")
            except (OSError, UnicodeError):
                context.refs_by_path[source_path] = []
            else:
                context.refs_by_path[source_path] = _extract_include_refs(content)

        children: dict[str, Path] = {}
        for include_path, selected_defs in context.refs_by_path[source_path]:
            changed_path = _matching_changed_path(
                include_path, current_file, context.repo_root, context.changed_paths
            )
            if changed_path is not None and _include_matches_changed(
                selected_defs, changed_path, context.changed_defs_by_path
            ):
                return True
            for target in _resolved_include_targets(
                include_path, current_file, context.repo_root
            ):
                target_file = context.repo_root / target
                if target_file.is_file() and target not in visited:
                    children[target] = target_file
        pending.extend(children[path] for path in reversed(sorted(children)))
    return False


def _reverse_dep_basenames(
    changed_files: list[str], diff_base: str | None = None
) -> set[str]:
    """Find prompts whose include tags reference any changed file.

    Catches the case where module B's example changes and module A includes it:
    A's basename must also be emitted so the healer re-generates A.
    """
    found: set[str] = set()
    if not changed_files:
        return found
    changed_paths: set[str] = set()
    for path in changed_files:
        normalized = _normalize_repo_path(path)
        if normalized:
            changed_paths.add(normalized)
    changed_defs_by_path = {
        path: _changed_python_defs(path, diff_base) for path in changed_paths
    }
    repo_root = Path.cwd().resolve()
    prompt_files: list[Path] = []
    for pdir in _PROMPT_DIRS:
        prompt_root = Path(pdir)
        if not prompt_root.exists():
            continue
        prompt_files.extend(prompt_root.rglob("*.prompt"))

    context = _ReverseDepContext(
        repo_root, changed_paths, changed_defs_by_path, {}
    )
    for prompt_file in sorted(prompt_files, key=lambda path: path.as_posix()):
        prompt_basename = _reverse_dep_basename_for_prompt(prompt_file, context)
        if prompt_basename:
            found.add(prompt_basename)
    return found


def detect(diff_base: str) -> list[str]:
    changed_files = _git_changed_files(diff_base)
    ownership = _module_ownership()
    basenames: set[str] = set()
    protected_human_paths: set[str] | None = None
    for f in changed_files:
        try:
            basenames.update(_module_from_path(f, ownership))
        except ValueError:
            if protected_human_paths is None:
                protected_human_paths = _protected_human_owned_paths(diff_base)
            if _normalize_repo_path(f) in protected_human_paths:
                continue
            raise
    for candidate in _reverse_dep_basenames(changed_files, diff_base=diff_base):
        if candidate in EXCLUDED_MODULE_BASENAMES:
            continue
        basenames.add(_resolve_candidate(candidate, "reverse include", ownership))
    return sorted(basenames)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--diff-base",
        required=True,
        help="git diff reference (e.g. 'origin/main...HEAD' or 'HEAD~1')",
    )
    args = parser.parse_args()
    try:
        basenames = detect(args.diff_base)
    except subprocess.CalledProcessError as exc:
        print(f"git diff failed: {exc}", file=sys.stderr)
        return 2
    except ValueError as exc:
        print(f"module ownership failed: {exc}", file=sys.stderr)
        return 2
    print(",".join(basenames))
    return 0


if __name__ == "__main__":
    sys.exit(main())
