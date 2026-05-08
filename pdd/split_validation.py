from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Iterable, Optional

from .get_test_command import get_test_command_for_file, TestCommand
from .get_lint_commands import get_lint_commands as _get_lint_commands_impl, LintCommand


# Module-level flag to suppress progress prints in tests
quiet_import: bool = False


# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------


@dataclass
class ValidationFailure:
    check: str
    message: str
    severity: str = "error"


@dataclass
class ValidationResult:
    passed: bool
    failures: list[ValidationFailure] = field(default_factory=list)
    failure_type: str = "none"


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------


_LANG_SUFFIXES = ("_python", "_typescript", "_go", "_rust")

_REQUIRED_TAGS = ("<pdd-reason>", "<pdd-interface>", "<pdd-dependency>")

_STDLIB_NAMES = {
    "os", "sys", "io", "re", "json", "time", "math", "asyncio", "subprocess",
    "shutil", "tempfile", "pathlib", "logging", "functools", "itertools",
    "collections", "typing", "datetime", "random", "uuid", "hashlib", "base64",
    "threading", "multiprocessing", "socket", "signal", "platform", "builtins",
    "copy", "string", "enum", "dataclasses", "warnings",
}

_CATEGORY_MAP = {
    "byte_equivalence": "extraction",
    "test_seam_resolution": "extraction",
    "parent_wiring": "extraction",
    "prompt_metadata": "metadata",
    "children_completeness": "completeness",
    "example_file": "completeness",
    "test_ownership": "completeness",
}


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _console(stderr: bool = False):
    from rich.console import Console
    return Console(stderr=stderr)


def _normalize_child(child: Any) -> SimpleNamespace:
    """Normalize a child (dataclass-like or dict) into a SimpleNamespace."""
    if isinstance(child, dict):
        prompt_file = child.get("new_prompt") or child.get("prompt_file") or ""
        code_file = child.get("new_source") or child.get("code_file") or ""
        name = child.get("name") or ""
        return SimpleNamespace(
            prompt_file=prompt_file,
            code_file=code_file,
            name=name,
        )
    prompt_file = getattr(child, "prompt_file", "") or ""
    code_file = getattr(child, "code_file", "") or ""
    name = getattr(child, "name", "") or ""
    return SimpleNamespace(
        prompt_file=str(prompt_file),
        code_file=str(code_file),
        name=str(name),
    )


def _module_stem(prompt_path: str) -> str:
    """Extract module stem from a prompt file path, stripping language suffix."""
    if not prompt_path:
        return ""
    stem = Path(prompt_path).stem
    # Strip .prompt suffix if present in stem (e.g., "foo.prompt" -> "foo")
    if stem.endswith(".prompt"):
        stem = stem[: -len(".prompt")]
    for suf in _LANG_SUFFIXES:
        if stem.endswith(suf):
            return stem[: -len(suf)]
    return stem


def _prompt_stem(prompt_path: str) -> str:
    if not prompt_path:
        return ""
    stem = Path(prompt_path).stem
    if stem.endswith(".prompt"):
        stem = stem[: -len(".prompt")]
    return stem


def _classify_failure_type(failures: list[ValidationFailure]) -> str:
    if not failures:
        return "none"
    categories = {_CATEGORY_MAP.get(f.check, "extraction") for f in failures}
    if len(categories) == 1:
        return next(iter(categories))
    return "multiple"


# ---------------------------------------------------------------------------
# Individual checks
# ---------------------------------------------------------------------------


def _check_git_status(worktree: Path) -> list[ValidationFailure]:
    failures: list[ValidationFailure] = []
    try:
        result = subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=worktree,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            failures.append(
                ValidationFailure(
                    check="byte_equivalence",
                    message=f"git status failed: {result.stderr.strip()}",
                )
            )
    except FileNotFoundError:
        failures.append(
            ValidationFailure(
                check="byte_equivalence",
                message="git executable not found",
            )
        )
    except OSError as exc:
        failures.append(
            ValidationFailure(
                check="byte_equivalence",
                message=f"Error running git status: {exc}",
            )
        )
    return failures


def _check_children_completeness(
    children: list[SimpleNamespace], worktree: Path
) -> list[ValidationFailure]:
    failures: list[ValidationFailure] = []
    extracted = 0
    missing: list[str] = []
    for child in children:
        prompt_exists = bool(child.prompt_file) and (worktree / child.prompt_file).exists()
        code_exists = bool(child.code_file) and (worktree / child.code_file).exists()
        if prompt_exists or code_exists:
            extracted += 1
        else:
            label = child.name or child.prompt_file or child.code_file or "<unknown>"
            paths = ", ".join(p for p in (child.prompt_file, child.code_file) if p) or "<no paths>"
            missing.append(f"{label} ({paths})")
    total = len(children)
    if extracted < total and missing:
        failures.append(
            ValidationFailure(
                check="children_completeness",
                message=(
                    f"Missing {total - extracted}/{total} children: "
                    + "; ".join(missing)
                ),
            )
        )
    return failures


def _check_prompt_metadata(
    children: list[SimpleNamespace], worktree: Path
) -> list[ValidationFailure]:
    failures: list[ValidationFailure] = []
    for child in children:
        if not child.prompt_file:
            continue
        prompt_path = worktree / child.prompt_file
        if not prompt_path.exists():
            continue
        try:
            content = prompt_path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as exc:
            try:
                _console(stderr=True).print(
                    f"[yellow]Warning: failed to read {prompt_path}: {exc}[/yellow]"
                )
            except Exception:
                pass
            continue
        for tag in _REQUIRED_TAGS:
            if tag not in content:
                failures.append(
                    ValidationFailure(
                        check="prompt_metadata",
                        message=f"{child.prompt_file}: missing tag {tag}",
                        severity="warning",
                    )
                )
    return failures


def _check_example_files(
    children: list[SimpleNamespace], worktree: Path
) -> list[ValidationFailure]:
    failures: list[ValidationFailure] = []
    for child in children:
        if not child.prompt_file:
            continue
        suffix = Path(child.code_file).suffix if child.code_file else ".py"
        if not suffix:
            suffix = ".py"
        stem = _module_stem(child.prompt_file)
        pstem = _prompt_stem(child.prompt_file)
        prompt_path = Path(child.prompt_file)

        candidates: list[Path] = []
        if stem:
            candidates.append(Path("examples") / f"{stem}_example{suffix}")
        if pstem and pstem != stem:
            candidates.append(Path("examples") / f"{pstem}_example{suffix}")
        candidates.append(prompt_path.with_suffix(suffix))

        # Deduplicate
        seen: set[str] = set()
        unique_candidates: list[Path] = []
        for c in candidates:
            key = str(c)
            if key not in seen:
                seen.add(key)
                unique_candidates.append(c)

        if not any((worktree / c).exists() for c in unique_candidates):
            paths_str = ", ".join(str(c) for c in unique_candidates)
            label = child.name or stem or child.prompt_file
            failures.append(
                ValidationFailure(
                    check="example_file",
                    message=f"No example file found for {label}; checked: {paths_str}",
                )
            )
    return failures


def _check_test_ownership(
    children: list[SimpleNamespace], worktree: Path
) -> list[ValidationFailure]:
    failures: list[ValidationFailure] = []

    # Build map of stem -> child for cross-reference checks
    child_stems: list[tuple[str, SimpleNamespace]] = []
    for child in children:
        stem = _module_stem(child.prompt_file) if child.prompt_file else ""
        if not stem and child.code_file:
            stem = Path(child.code_file).stem
        if stem:
            child_stems.append((stem, child))

    for stem, child in child_stems:
        if not child.code_file:
            continue
        suffix = Path(child.code_file).suffix or ".py"
        code_dir = (worktree / child.code_file).parent
        test_name = f"test_{stem}{suffix}"
        candidates = [
            code_dir / test_name,
            worktree / "tests" / test_name,
        ]
        for tf in candidates:
            if not tf.exists():
                continue
            try:
                content = tf.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError):
                continue
            for other_stem, other_child in child_stems:
                if other_stem == stem:
                    continue
                pattern = re.compile(rf"\b{re.escape(other_stem)}\b")
                if pattern.search(content):
                    failures.append(
                        ValidationFailure(
                            check="test_ownership",
                            message=(
                                f"Test file {tf} for child '{stem}' references "
                                f"other child module '{other_stem}'"
                            ),
                            severity="warning",
                        )
                    )
    return failures


# ---------------------------------------------------------------------------
# Test seam resolution
# ---------------------------------------------------------------------------


_PATCH_PATTERNS = [
    # patch("a.b") and patch.object("a.b", ...) - first string arg
    re.compile(r"""(?<![\w.])patch(?:\.object)?\s*\(\s*["']([^"']+)["']"""),
    # mocker.patch(...) and mocker.patch.object(...)
    re.compile(r"""mocker\.patch(?:\.object)?\s*\(\s*["']([^"']+)["']"""),
    # jest.mock("...") / jest.doMock("...")
    re.compile(r"""jest\.(?:mock|doMock)\s*\(\s*["']([^"']+)["']"""),
]


def _extract_patch_paths(content: str) -> list[str]:
    paths: list[str] = []
    for pat in _PATCH_PATTERNS:
        for m in pat.finditer(content):
            p = m.group(1).strip()
            if "." not in p:
                continue
            if p.startswith(".") or p.endswith("."):
                continue
            paths.append(p)
    return paths


def _collapse_paren_imports(content: str) -> str:
    """Collapse newlines inside parenthesized `from ... import (...)` groups."""
    def _collapse(match: re.Match[str]) -> str:
        head = match.group(1)
        inside = match.group(2)
        flat = re.sub(r"\s+", " ", inside)
        return f"{head}({flat})"

    pattern = re.compile(
        r"(from\s+[\w.]+\s+import\s*)\(([^)]*)\)",
        re.MULTILINE,
    )
    return pattern.sub(_collapse, content)


def _find_module_file(
    module_parts: list[str], worktree: Path
) -> Optional[Path]:
    """Locate a candidate module file in worktree or worktree/extensions."""
    if not module_parts:
        return None

    search_roots = [worktree]
    ext_dir = worktree / "extensions"
    if ext_dir.exists():
        search_roots.append(ext_dir)

    # Try various truncations: full, drop-1, drop-2 leading components
    variants: list[list[str]] = [module_parts]
    if len(module_parts) > 1:
        variants.append(module_parts[1:])
    if len(module_parts) > 2:
        variants.append(module_parts[2:])

    for parts in variants:
        if not parts:
            continue
        # Try .py and __init__.py forms
        for as_init in (False, True):
            if as_init:
                rel_parts = parts + ["__init__.py"]
            else:
                rel_parts = parts[:-1] + [parts[-1] + ".py"]
            basename = rel_parts[-1]
            for root in search_roots:
                # Direct check first
                direct = root.joinpath(*rel_parts)
                if direct.exists():
                    return direct
                # rglob basename, match trailing parts
                try:
                    for cand in root.rglob(basename):
                        if not cand.is_file():
                            continue
                        cand_parts = cand.parts[-len(rel_parts):]
                        if list(cand_parts) == rel_parts:
                            return cand
                except OSError:
                    continue
    return None


def _symbol_defined(content: str, sym: str) -> bool:
    """Check if symbol is defined or imported in file content."""
    esc = re.escape(sym)

    # def / async def / class
    if re.search(rf"^(?:async\s+)?def\s+{esc}\b", content, re.MULTILINE):
        return True
    if re.search(rf"^class\s+{esc}\b", content, re.MULTILINE):
        return True
    # Top-level assignment
    if re.search(rf"^{esc}\s*[:=]", content, re.MULTILINE):
        return True

    collapsed = _collapse_paren_imports(content)

    # from ... import ... sym ...
    # Match the imported names list
    for m in re.finditer(
        r"from\s+[\w.]+\s+import\s+([^\n#]+)",
        collapsed,
    ):
        names_part = m.group(1).strip()
        # Strip parens
        names_part = names_part.strip("()")
        # Split by commas
        for raw in names_part.split(","):
            name = raw.strip()
            if not name:
                continue
            # Handle "X as Y"
            if " as " in name:
                _, alias = name.split(" as ", 1)
                if alias.strip() == sym:
                    return True
            else:
                if name == sym:
                    return True

    # from ... import *
    if re.search(r"from\s+[\w.]+\s+import\s+\*", content):
        return True

    # Dir-walk re-export
    if re.search(r"for\s+_?\w+\s+in\s+dir\s*\(", content):
        if re.search(r"globals\s*\(\s*\)\s*\[", content) or re.search(
            r"getattr\s*\(\s*_?\w+", content
        ):
            return True

    return False


def _resolve_patch_path(
    dotted: str, worktree: Path
) -> tuple[bool, str]:
    """Resolve a dotted patch path. Returns (resolved, reason)."""
    parts = dotted.split(".")
    if len(parts) < 2:
        return True, "trivial"

    module_parts = parts[:-1]
    sym = parts[-1]

    # Stdlib optimism: any module component or trailing sym
    for p in module_parts + [sym]:
        if p in _STDLIB_NAMES:
            return True, "stdlib"

    module_file = _find_module_file(module_parts, worktree)
    if module_file is None:
        return False, "module file not found"

    try:
        content = module_file.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        return False, f"failed to read module: {exc}"

    if _symbol_defined(content, sym):
        return True, "found"

    return False, f"symbol '{sym}' not found"


def _discover_test_files(
    children: list[SimpleNamespace], worktree: Path
) -> list[Path]:
    """Discover test files relevant to the children."""
    test_files: set[Path] = set()

    for child in children:
        if not child.code_file:
            continue
        suffix = Path(child.code_file).suffix or ".py"
        stem = _module_stem(child.prompt_file) if child.prompt_file else Path(child.code_file).stem
        if not stem:
            continue
        test_name = f"test_{stem}{suffix}"
        code_path = worktree / child.code_file
        code_dir = code_path.parent

        # Co-located
        for cand in (code_dir / test_name, worktree / "tests" / test_name):
            if cand.exists() and cand.is_file():
                try:
                    test_files.add(cand.resolve())
                except OSError:
                    test_files.add(cand)

        # Walk up looking for tests/ dirs
        cur = code_dir
        for _ in range(6):
            tests_dir = cur / "tests"
            if tests_dir.is_dir():
                for ext in ("py", "ts", "tsx", "js"):
                    for tf in tests_dir.glob(f"test_*.{ext}"):
                        if tf.is_file():
                            try:
                                test_files.add(tf.resolve())
                            except OSError:
                                test_files.add(tf)
            if cur == worktree or cur.parent == cur:
                break
            cur = cur.parent

        # extensions/*/tests/
        ext_dir = worktree / "extensions"
        if ext_dir.is_dir():
            for ext_sub in ext_dir.iterdir():
                if not ext_sub.is_dir():
                    continue
                ext_tests = ext_sub / "tests"
                if not ext_tests.is_dir():
                    continue
                cand = ext_tests / test_name
                if cand.exists() and cand.is_file():
                    try:
                        test_files.add(cand.resolve())
                    except OSError:
                        test_files.add(cand)

    # Worktree tests/
    wt_tests = worktree / "tests"
    if wt_tests.is_dir():
        for ext in ("py", "ts", "tsx", "js"):
            for tf in wt_tests.glob(f"test_*.{ext}"):
                if tf.is_file():
                    try:
                        test_files.add(tf.resolve())
                    except OSError:
                        test_files.add(tf)

    return sorted(test_files)


def _check_test_seams(
    children: list[SimpleNamespace], worktree: Path
) -> list[ValidationFailure]:
    failures: list[ValidationFailure] = []
    test_files = _discover_test_files(children, worktree)

    total_paths = 0
    resolved_paths = 0

    for tf in test_files:
        try:
            content = tf.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        patch_paths = _extract_patch_paths(content)
        for p in patch_paths:
            total_paths += 1
            ok, reason = _resolve_patch_path(p, worktree)
            if ok:
                resolved_paths += 1
            else:
                failures.append(
                    ValidationFailure(
                        check="test_seam_resolution",
                        message=f"Unresolved patch path '{p}' in {tf} ({reason})",
                    )
                )

    if total_paths > 0 and not quiet_import:
        try:
            _console(stderr=True).print(
                f"[dim]Test-seam check: {resolved_paths}/{total_paths} "
                f"patch paths resolved across {len(test_files)} test files[/dim]"
            )
        except Exception:
            pass

    return failures


# ---------------------------------------------------------------------------
# Parent wiring
# ---------------------------------------------------------------------------


def _extract_top_level_definitions(content: str) -> list[str]:
    names: list[str] = []
    for m in re.finditer(
        r"^(?:async\s+)?def\s+([A-Za-z_]\w*)", content, re.MULTILINE
    ):
        names.append(m.group(1))
    for m in re.finditer(r"^class\s+([A-Za-z_]\w*)", content, re.MULTILINE):
        names.append(m.group(1))
    # Skip dunders
    return [n for n in names if not (n.startswith("__") and n.endswith("__"))]


def _check_parent_wiring(
    plan: Any, children: list[SimpleNamespace], worktree: Path
) -> list[ValidationFailure]:
    failures: list[ValidationFailure] = []
    parent_changes = getattr(plan, "parent_changes", None)
    if not parent_changes:
        return failures
    if isinstance(parent_changes, dict):
        modified_source = parent_changes.get("modified_source", "")
    else:
        modified_source = getattr(parent_changes, "modified_source", "") or ""
    if not modified_source:
        return failures

    parent_path = worktree / modified_source
    if not parent_path.exists():
        # Try package __init__.py
        as_pkg = parent_path.with_suffix("") / "__init__.py"
        if as_pkg.exists():
            parent_path = as_pkg
        else:
            return failures

    try:
        parent_content = parent_path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return failures

    for child in children:
        if not child.code_file:
            continue
        child_path = worktree / child.code_file
        if not child_path.exists():
            continue
        try:
            child_content = child_path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        helpers = _extract_top_level_definitions(child_content)
        for name in helpers:
            pattern = re.compile(rf"\b{re.escape(name)}\b")
            if not pattern.search(parent_content):
                failures.append(
                    ValidationFailure(
                        check="parent_wiring",
                        message=(
                            f"Unwired helper: '{name}' defined in "
                            f"{child.code_file} but never imported/called from "
                            f"parent {modified_source}…"
                        ),
                    )
                )
    return failures


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def validate_extraction(plan: Any, worktree: Path) -> ValidationResult:
    """Run post-extraction validation checks for the agentic split orchestrator."""
    if not isinstance(worktree, Path):
        worktree = Path(worktree)

    if not worktree.is_dir():
        failures = [
            ValidationFailure(
                check="byte_equivalence",
                message=f"worktree is not a directory: {worktree}",
            )
        ]
        return ValidationResult(
            passed=False,
            failures=failures,
            failure_type=_classify_failure_type(failures),
        )

    raw_children = getattr(plan, "children", None) or []
    all_failures: list[ValidationFailure] = []

    # Normalize children, separating defective ones (both paths empty)
    valid_children: list[SimpleNamespace] = []
    for raw in raw_children:
        norm = _normalize_child(raw)
        if not norm.prompt_file and not norm.code_file:
            label = norm.name or "<unnamed>"
            all_failures.append(
                ValidationFailure(
                    check="children_completeness",
                    message=f"Child '{label}' has no prompt_file or code_file",
                    severity="warning",
                )
            )
            continue
        valid_children.append(norm)

    # (a) git sanity
    all_failures.extend(_check_git_status(worktree))

    # (b) children completeness
    all_failures.extend(_check_children_completeness(valid_children, worktree))

    # (c) prompt metadata
    all_failures.extend(_check_prompt_metadata(valid_children, worktree))

    # (d) example files
    all_failures.extend(_check_example_files(valid_children, worktree))

    # (e) test ownership
    all_failures.extend(_check_test_ownership(valid_children, worktree))

    # (f) test seam resolution
    all_failures.extend(_check_test_seams(valid_children, worktree))

    # (g) parent wiring
    all_failures.extend(_check_parent_wiring(plan, valid_children, worktree))

    failure_type = _classify_failure_type(all_failures)
    passed = not any(f.severity == "error" for f in all_failures)
    return ValidationResult(
        passed=passed,
        failures=all_failures,
        failure_type=failure_type,
    )


def get_test_command(file: Path) -> Optional[TestCommand]:
    """Resolve the test command for the given file."""
    return get_test_command_for_file(str(file))


def get_lint_commands(file: Path) -> list[LintCommand]:
    """Resolve lint commands for the given file."""
    return _get_lint_commands_impl(file)


__all__ = [
    "LintCommand",
    "TestCommand",
    "ValidationFailure",
    "ValidationResult",
    "validate_extraction",
    "get_test_command",
    "get_lint_commands",
]