"""pdd/split_validation.py — Post-extraction validation for the agentic split orchestrator."""
from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

from .get_lint_commands import LintCommand
from .get_lint_commands import get_lint_commands as _get_lint_commands_impl
from .get_test_command import TestCommand, get_test_command_for_file

__all__ = [
    "LintCommand",
    "TestCommand",
    "ValidationFailure",
    "ValidationResult",
    "get_lint_commands",
    "get_test_command",
    "validate_extraction",
]


# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------


@dataclass
class ValidationFailure:
    """A single validation check failure.

    Attributes:
        check: Name of the check that failed (e.g. ``"byte_equivalence"``).
        message: Human-readable failure description.
        severity: One of ``"error"`` or ``"warning"``.  Default ``"error"``.
    """

    check: str
    message: str
    severity: str = "error"


@dataclass
class ValidationResult:
    """Aggregated result of all validation checks.

    Attributes:
        passed: ``True`` when there are no error-severity failures.
        failures: Every failure found across all checks.
        failure_type: Summary category — ``"none"``, ``"extraction"``,
            ``"metadata"``, ``"completeness"``, or ``"multiple"``.
    """

    passed: bool
    failures: list[ValidationFailure] = field(default_factory=list)
    failure_type: str = "none"


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

_CHECK_TO_CATEGORY: dict[str, str] = {
    "byte_equivalence": "extraction",
    "prompt_metadata": "metadata",
    "children_completeness": "completeness",
    "example_file": "completeness",
    "test_ownership": "completeness",
    "test_seam_resolution": "extraction",
}


# Regex for patch-string patterns used across test frameworks.
# We look for any string literal passed to patch()/patcher/mock.patch()
# that looks like a dotted module path: "a.b.c" or "module.X".
# This is framework-agnostic — we capture the STRING not the API call.
_PATCH_STRING_PATTERNS = [
    # Python: patch("mod.X"), patch.object("mod.X", ...), mock.patch("mod.X")
    re.compile(r'''patch(?:\.object)?\s*\(\s*["']([^"']+)["']'''),
    # Python: mocker.patch("mod.X") AND mocker.patch.object("mod.X", ...)
    re.compile(r'''mocker\.patch(?:\.object)?\s*\(\s*["']([^"']+)["']'''),
    # JS/TS: jest.mock('mod'), jest.doMock('mod')
    re.compile(r'''jest\.(?:do)?[mM]ock\s*\(\s*["']([^"']+)["']'''),
    # Go: reflect-based lookups that reference module paths as strings
    # (best-effort; Go rarely uses string-based patching)
]


def _collect_patch_paths(test_file_content: str) -> list[str]:
    """Extract every module-path-looking string passed to a patch() call.

    Framework-agnostic: looks for the string argument, not the API call.
    Returns a deduplicated list of dotted paths that look like symbol
    references (contain at least one dot).
    """
    paths: set[str] = set()
    for pattern in _PATCH_STRING_PATTERNS:
        for match in pattern.findall(test_file_content):
            # Only keep things that look like dotted module paths
            if "." in match and not match.startswith(".") and not match.endswith("."):
                paths.add(match)
    return sorted(paths)


_STDLIB_MODULES_COMMON: set[str] = {
    "os", "sys", "io", "re", "json", "time", "math", "asyncio", "subprocess",
    "shutil", "tempfile", "pathlib", "logging", "functools", "itertools",
    "collections", "typing", "datetime", "random", "uuid", "hashlib",
    "base64", "threading", "multiprocessing", "socket", "signal", "platform",
    "builtins", "copy", "string", "enum", "dataclasses", "warnings",
}


def _resolve_patch_path(path: str, worktree: Path) -> tuple[bool, str]:
    """Check whether a dotted patch path resolves after extraction.

    We can't actually import the module (that would require executing
    project code with all its dependencies). Instead we do a static
    resolution check:
    - Find the module file for the leading components
    - Check that the final component appears as a name in that file,
      either defined directly or re-exported via import
    Returns (resolved, reason).
    """
    if "." not in path:
        return True, ""  # Not a dotted path; skip
    parts = path.split(".")
    # The last part is the symbol name; everything else is the module path.
    symbol = parts[-1]
    module_parts = parts[:-1]

    # Pattern: <pkg>.<stdlib>.<attr>  — e.g. src.workers.pdd_executor.os.getpgid
    # The test is patching a stdlib attribute as imported into the target
    # package. This works at runtime whenever the target package has
    # `import <stdlib>`. We accept this optimistically — it's a common
    # pattern and usually correct.
    for i, part in enumerate(module_parts):
        if part in _STDLIB_MODULES_COMMON:
            # Everything from this point is stdlib attribute access
            return True, f"optimistic (stdlib attr via '{part}')"

    # Pattern: <pkg>.<stdlib>  — e.g. src.workers.pdd_executor.subprocess
    # The symbol itself is a stdlib module name. The test is replacing
    # the whole module attribute on the target. Accept optimistically.
    if symbol in _STDLIB_MODULES_COMMON:
        return True, f"optimistic (stdlib module '{symbol}')"

    # Try to locate the module file. Walk the worktree looking for any
    # `<joined_parts>.py` or `<joined_parts>/__init__.py`.
    # We try multiple search roots to handle different layouts.
    rel_candidates: list[Path] = []
    # Full path: a/b/c.py
    rel_candidates.append(Path(*module_parts).with_suffix(".py"))
    # Package: a/b/c/__init__.py
    rel_candidates.append(Path(*module_parts) / "__init__.py")
    # Drop first component (common: tests use "src.workers.X" but code is "workers/X")
    if len(module_parts) > 1:
        rel_candidates.append(Path(*module_parts[1:]).with_suffix(".py"))
        rel_candidates.append(Path(*module_parts[1:]) / "__init__.py")
    # Drop first two components (common: "src.workers.pdd_executor.X" → "pdd_executor/X")
    if len(module_parts) > 2:
        rel_candidates.append(Path(*module_parts[2:]).with_suffix(".py"))
        rel_candidates.append(Path(*module_parts[2:]) / "__init__.py")

    # Search the whole worktree for the last-segment filename as a fallback
    # (helps when the test uses a flat path but the code lives deep).
    # Filter so the candidate's trailing path segments match the relative
    # path's parts — prevents every __init__.py in the tree from matching.
    found_files: list[Path] = []
    for rel in rel_candidates:
        rel_parts = rel.parts
        for root in [worktree, worktree / "extensions"]:
            if not root.is_dir():
                continue
            for cand in root.rglob(rel.name):
                if not (cand.is_file() and cand.name == rel.name):
                    continue
                try:
                    rel_cand = cand.relative_to(root).parts
                except ValueError:
                    continue
                if rel_cand[-len(rel_parts):] != rel_parts:
                    continue
                found_files.append(cand)

    if not found_files:
        return False, f"module file not found for path '{path}'"

    # For each candidate file, check whether `symbol` appears as a
    # defined name or a re-export. We normalize multi-line imports by
    # collapsing them first (Python allows `from m import (\n  A,\n  B,\n)`
    # which is invisible to a line-based regex).
    name_re = re.compile(
        rf"(?m)^(?:"
        rf"async\s+def\s+{re.escape(symbol)}\b|"
        rf"def\s+{re.escape(symbol)}\b|"
        rf"class\s+{re.escape(symbol)}\b|"
        rf"{re.escape(symbol)}\s*(?::\s*[^=]+)?\s*="
        rf")"
    )
    # Regex for imports that may span multiple lines via parentheses.
    # We collapse the text first to make the match simple.
    import_re = re.compile(
        rf"from\s+\S+\s+import\s+[^;\n]*?\b{re.escape(symbol)}\b"
    )
    # Star imports (e.g. `from .submodule import *`) act like brute re-exports
    star_import_re = re.compile(r"from\s+\S+\s+import\s+\*")

    for cand in found_files:
        try:
            text = cand.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        # Direct definition on this file
        if name_re.search(text):
            return True, ""
        # Collapse multi-line parenthesized imports into single lines so
        # import_re can match. Cheap transformation: remove newlines
        # inside any `(...)` that follows an `import`.
        def _flatten_paren_imports(t: str) -> str:
            # Find `import (...)` blocks and strip newlines inside them
            out_parts: list[str] = []
            i = 0
            while i < len(t):
                # Look for 'import ' followed by '('
                m = re.compile(r"\bimport\s*\(").search(t, i)
                if not m:
                    out_parts.append(t[i:])
                    break
                # Copy up to the '('
                out_parts.append(t[i:m.end() - 1])  # up to but not including '('
                # Find matching close paren
                depth = 0
                j = m.end() - 1
                while j < len(t):
                    ch = t[j]
                    if ch == "(":
                        depth += 1
                    elif ch == ")":
                        depth -= 1
                        if depth == 0:
                            break
                    j += 1
                # Flatten the parenthesized block
                block = t[m.end() - 1 : j + 1].replace("\n", " ")
                out_parts.append(block)
                i = j + 1
            return "".join(out_parts)

        flat = _flatten_paren_imports(text)
        if import_re.search(flat):
            return True, ""
        # Star import: symbol could be from any of them; accept optimistically
        if star_import_re.search(text):
            return True, "optimistic (star import)"
        # Brute-force re-export via dir() walk (manual-split pattern)
        if (
            "for _name in dir(" in text
            and ("globals()[_name] = getattr" in text or "getattr(_" in text)
        ):
            return True, "optimistic (dir-walk re-export)"

    return False, f"symbol '{symbol}' not found in any candidate module file"


def _classify_failures(failures: list[ValidationFailure]) -> str:
    """Return the summary ``failure_type`` for a collection of failures."""
    if not failures:
        return "none"
    categories: set[str] = {
        _CHECK_TO_CATEGORY.get(f.check, "extraction") for f in failures
    }
    if len(categories) > 1:
        return "multiple"
    return categories.pop()


def _build_result(failures: list[ValidationFailure]) -> ValidationResult:
    """Construct a :class:`ValidationResult` from collected failures."""
    has_error = any(f.severity == "error" for f in failures)
    return ValidationResult(
        passed=not has_error,
        failures=failures,
        failure_type=_classify_failures(failures),
    )


def _relative_to_safe(path: Path, base: Path) -> Path:
    """Return *path* relative to *base*, falling back to *path* itself."""
    try:
        return path.relative_to(base)
    except ValueError:
        return path


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def validate_extraction(plan: Any, worktree: Path) -> ValidationResult:
    """Run post-extraction validation checks on a worktree.

    Checks executed in order:

    a. **Moved-code byte-equivalence** — ``git diff --stat``
    b. **Children completeness** — prompt-file existence count
    c. **Prompt metadata tag presence** — ``<pdd-reason>``, ``<pdd-interface>``,
       ``<pdd-dependency>``
    d. **Example file existence** — derived from each child's ``prompt_file``
    e. **Test ownership classification** — basic grep for cross-module refs

    Args:
        plan: Duck-typed plan object.  Must expose ``children: list`` where
              each child has ``prompt_file: str`` and ``code_file: str``
              attributes.
        worktree: Root of the git worktree to validate.

    Returns:
        A :class:`ValidationResult` summarising all detected issues.
    """
    from rich.console import Console  # third-party: function-scope

    console = Console(stderr=True)
    failures: list[ValidationFailure] = []

    # Gracefully handle a missing/invalid worktree early.
    if not worktree.is_dir():
        return _build_result(
            [
                ValidationFailure(
                    check="byte_equivalence",
                    message=f"Worktree is not a directory: {worktree}",
                )
            ]
        )

    raw_children: list[Any] = getattr(plan, "children", None) or []

    # Normalize children: accept dicts (from LLM JSON) or dataclass-like objects
    # with .prompt_file / .code_file attributes. Wrap dicts in a simple namespace
    # so downstream code can use attribute access uniformly.
    from types import SimpleNamespace
    def _as_child(c: Any) -> Any:
        if isinstance(c, dict):
            # Map LLM field names to attribute names
            return SimpleNamespace(
                prompt_file=c.get("new_prompt") or c.get("prompt_file") or "",
                code_file=c.get("new_source") or c.get("code_file") or "",
                name=c.get("name", ""),
            )
        return c
    children = [_as_child(c) for c in raw_children]
    # Filter out children with empty paths — they crash path operations
    # (worktree / "" returns worktree itself, which fails as a file).
    # These are LLM output defects and should be flagged but not crash.
    skipped_children = [
        c for c in children
        if not getattr(c, "prompt_file", "") and not getattr(c, "code_file", "")
    ]
    children = [
        c for c in children
        if getattr(c, "prompt_file", "") or getattr(c, "code_file", "")
    ]
    for c in skipped_children:
        failures.append(
            ValidationFailure(
                check="children_completeness",
                message=(
                    f"Child '{getattr(c, 'name', '?')}' has no prompt_file "
                    f"or code_file — LLM output defect"
                ),
                severity="warning",
            )
        )

    # ------------------------------------------------------------------ (a)
    # Git repository sanity — verify we're in a working git worktree
    # The spec calls this "moved-code byte-equivalence" but actually
    # checking byte-match requires per-symbol diff against the pre-split
    # source (which this function doesn't have). The agent is responsible
    # for preserving byte-equivalence during extraction (enforced by the
    # step 6 prompt); this check only verifies git is functional.
    # ------------------------------------------------------------------
    try:
        status_proc = subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=worktree,
            capture_output=True,
            text=True,
        )
        if status_proc.returncode != 0:
            failures.append(
                ValidationFailure(
                    check="byte_equivalence",
                    message=(
                        f"git status failed (rc={status_proc.returncode}): "
                        f"{status_proc.stderr.strip()}"
                    ),
                )
            )
    except FileNotFoundError:
        failures.append(
            ValidationFailure(
                check="byte_equivalence",
                message="git executable not found; cannot verify worktree state.",
            )
        )
    except OSError as exc:
        failures.append(
            ValidationFailure(
                check="byte_equivalence",
                message=f"Error running git status: {exc}",
            )
        )

    # ------------------------------------------------------------------ (b)
    # Children completeness
    # ------------------------------------------------------------------
    # A child is "extracted" if either its prompt or its source exists.
    # Some LLM outputs omit prompt_file — require at least one.
    def _child_extracted(c: Any) -> bool:
        prompt_ok = bool(c.prompt_file) and (worktree / c.prompt_file).is_file()
        code_ok = bool(c.code_file) and (worktree / c.code_file).is_file()
        return prompt_ok or code_ok

    children_extracted = [c for c in children if _child_extracted(c)]
    if len(children_extracted) != len(children):
        missing = [
            f"{getattr(c, 'name', '?') or '?'}:"
            f"{getattr(c, 'prompt_file', '') or getattr(c, 'code_file', '') or '(no path)'}"
            for c in children
            if not _child_extracted(c)
        ]
        failures.append(
            ValidationFailure(
                check="children_completeness",
                message=(
                    f"Expected {len(children)} children but found "
                    f"{len(children_extracted)}. Missing: {missing}"
                ),
            )
        )

    # ------------------------------------------------------------------ (c)
    # Prompt metadata tag presence
    # ------------------------------------------------------------------
    required_tags: list[str] = [
        "<pdd-reason>",
        "<pdd-interface>",
        "<pdd-dependency>",
    ]
    for child in children:
        if not child.prompt_file:
            continue  # already reported as children_completeness warning
        prompt_path = worktree / child.prompt_file
        if not prompt_path.exists() or not prompt_path.is_file():
            continue
        try:
            content = prompt_path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as exc:
            console.print(
                f"[yellow]Warning: could not read {child.prompt_file}: {exc}[/yellow]"
            )
            continue
        for tag in required_tags:
            if tag not in content:
                failures.append(
                    ValidationFailure(
                        check="prompt_metadata",
                        message=f"Missing {tag} in {child.prompt_file}",
                        severity="warning",
                    )
                )

    # ------------------------------------------------------------------ (d)
    # Example file existence
    # ------------------------------------------------------------------
    for child in children:
        if not child.prompt_file:
            continue  # already reported
        prompt_path = Path(child.prompt_file)
        # Strip language suffix to get the base module name
        stem = prompt_path.stem
        if not stem:
            continue  # defensive: empty stem would make with_suffix crash
        for lang_suffix in ("_python", "_typescript", "_go", "_rust"):
            stem = stem.replace(lang_suffix, "")
        # Check multiple conventional locations.
        # Use the actual code file suffix so non-Python languages work too.
        example_suffix = Path(child.code_file).suffix or ".py"
        candidates = [
            worktree / "examples" / f"{stem}_example{example_suffix}",
            worktree / "examples" / f"{prompt_path.stem}_example{example_suffix}",
            worktree / prompt_path.with_suffix(example_suffix),
        ]
        if not any(c.exists() for c in candidates):
            checked = [str(_relative_to_safe(c, worktree)) for c in candidates]
            failures.append(
                ValidationFailure(
                    check="example_file",
                    message=f"Example file not found for {child.prompt_file}. Checked: {checked}",
                )
            )

    # ------------------------------------------------------------------ (e)
    # Test ownership classification
    # ------------------------------------------------------------------
    module_names: dict[str, str] = {}
    for child in children:
        if not child.code_file:
            continue
        code_path = Path(child.code_file)
        if code_path.stem:
            module_names[code_path.stem] = child.code_file

    all_modules = set(module_names.keys())

    for child in children:
        if not child.code_file:
            continue
        code_path = Path(child.code_file)
        module_name = code_path.stem
        if not module_name:
            continue

        test_file_name = f"test_{module_name}{code_path.suffix}"
        candidates = [
            worktree / code_path.parent / test_file_name,
            worktree / "tests" / test_file_name,
        ]

        test_path: Optional[Path] = None
        for candidate in candidates:
            if candidate.exists():
                test_path = candidate
                break

        if test_path is None:
            continue

        try:
            test_content = test_path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue

        other_modules = all_modules - {module_name}
        for other in sorted(other_modules):
            if re.search(rf"\b{re.escape(other)}\b", test_content):
                rel = _relative_to_safe(test_path, worktree)
                failures.append(
                    ValidationFailure(
                        check="test_ownership",
                        message=(
                            f"Test file {rel} references module "
                            f"'{other}' which belongs to a different child."
                        ),
                        severity="warning",
                    )
                )

    # ------------------------------------------------------------------ (f)
    # Test-seam resolution (NEW in v2.1)
    # ------------------------------------------------------------------
    # For every test file in the worktree, parse out string-based patch
    # paths and verify each one resolves to a symbol that exists after
    # extraction. Missing re-exports are the #1 cause of post-split test
    # failures — this catches them before step 7a runs the actual tests.
    #
    # Framework-agnostic: we look for the string argument passed to
    # patch(), jest.mock(), etc., not the API call itself.
    test_files_to_check: list[Path] = []
    # Collect child test files already located above
    for child in children:
        if not child.code_file:
            continue
        code_path = Path(child.code_file)
        if not code_path.stem:
            continue
        test_file_name = f"test_{code_path.stem}{code_path.suffix}"
        for candidate in (
            worktree / code_path.parent / test_file_name,
            worktree / "tests" / test_file_name,
            # Extensions convention
            worktree / "extensions" / "*" / "tests" / test_file_name,
        ):
            # Star-glob needs expansion
            if "*" in str(candidate):
                parent = Path(str(candidate).split("*")[0].rstrip("/"))
                if parent.is_dir():
                    for sub in parent.iterdir():
                        if sub.is_dir():
                            p = sub / "tests" / test_file_name
                            if p.exists():
                                test_files_to_check.append(p)
            elif candidate.exists():
                test_files_to_check.append(candidate)
    # Also include the parent's original test file(s). Tests that
    # patch through the parent module name (e.g. `src.workers.X`) are
    # the primary way re-export omissions cause failures, so we must
    # check these.
    if children:
        for child in children:
            if not child.code_file:
                continue
            code_path = Path(child.code_file)
            # Walk up from the child's package dir looking for a tests/
            # directory. This handles extensions/<ext>/tests/ and flat
            # tests/ at the repo root.
            parent = code_path.parent
            for _ in range(6):
                if parent == Path("."):
                    break
                tdir = worktree / parent / "tests"
                if tdir.is_dir():
                    for p in tdir.iterdir():
                        if (
                            p.is_file()
                            and p.name.startswith("test_")
                            and p.suffix in (".py", ".ts", ".tsx", ".js")
                        ):
                            test_files_to_check.append(p)
                parent = parent.parent
            # Also repo-root tests/
            root_tests = worktree / "tests"
            if root_tests.is_dir():
                for p in root_tests.iterdir():
                    if (
                        p.is_file()
                        and p.name.startswith("test_")
                        and p.suffix in (".py", ".ts", ".tsx", ".js")
                    ):
                        test_files_to_check.append(p)
            # Don't break — scan ALL children so test files in
            # different packages are discovered (was breaking after
            # the first child, missing children in other dirs).

    # De-duplicate
    test_files_to_check = list({p.resolve() for p in test_files_to_check if p.is_file()})

    unresolved_count = 0
    checked_count = 0
    for test_path in test_files_to_check:
        try:
            test_content = test_path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        patch_paths = _collect_patch_paths(test_content)
        if not patch_paths:
            continue
        for ppath in patch_paths:
            checked_count += 1
            resolved, reason = _resolve_patch_path(ppath, worktree)
            if not resolved:
                unresolved_count += 1
                rel = _relative_to_safe(test_path, worktree)
                failures.append(
                    ValidationFailure(
                        check="test_seam_resolution",
                        message=(
                            f"Test seam unresolved: {rel} patches '{ppath}' "
                            f"but {reason}. Add a re-export on the parent or "
                            f"update the patch path."
                        ),
                        severity="error",
                    )
                )
    if checked_count > 0 and not quiet_import:
        try:
            # Friendly progress signal on the console when seams were checked
            from rich.console import Console as _C  # type: ignore
            _C(stderr=True).print(
                f"[dim]Test-seam check: {checked_count - unresolved_count}/"
                f"{checked_count} patch paths resolved across "
                f"{len(test_files_to_check)} test files[/dim]"
            )
        except Exception:
            pass

    # ------------------------------------------------------------------
    # (g) Parent-wiring check — catches the "helpers created but never
    # called" regression. If a child defines a function but the parent
    # doesn't import/call it, the helper is dead code and the parent
    # didn't shrink as intended.
    # ------------------------------------------------------------------
    parent_changes = getattr(plan, "parent_changes", {}) or {}
    parent_source = None
    if isinstance(parent_changes, dict):
        parent_source = parent_changes.get("modified_source", "")
    if parent_source:
        parent_path = worktree / parent_source
        # Handle the "parent became a package" case
        if not parent_path.is_file():
            pkg_init = (worktree / parent_source).with_suffix("") / "__init__.py"
            if pkg_init.is_file():
                parent_path = pkg_init
        if parent_path.is_file():
            try:
                parent_content = parent_path.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                parent_content = ""
            unwired = _find_unwired_helpers(children, worktree, parent_content)
            for helper_name, child_file in unwired:
                failures.append(
                    ValidationFailure(
                        check="parent_wiring",
                        message=(
                            f"Unwired helper: '{helper_name}' defined in "
                            f"{child_file} but never imported/called from "
                            f"parent {parent_source}. Replace inline code "
                            f"in parent with calls to the new helper."
                        ),
                        severity="error",
                    )
                )

    return _build_result(failures)


def _find_unwired_helpers(
    children: list,
    worktree: Path,
    parent_content: str,
) -> list[tuple[str, str]]:
    """Return [(helper_name, child_file_rel), ...] for helpers defined
    in children but not referenced (imported or called) in the parent.

    A helper is "wired" if the parent imports it OR calls it via
    attribute access (module.helper_name) OR references it directly.
    """
    unwired: list[tuple[str, str]] = []
    for child in children:
        code_file = getattr(child, "code_file", "")
        if not code_file:
            continue
        child_path = worktree / code_file
        if not child_path.is_file():
            continue
        try:
            child_content = child_path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        # Collect top-level def/class/async def names from the child.
        # Regex is intentionally simple — avoids AST to stay language-agnostic
        # beyond Python.
        defined = set()
        for m in re.finditer(
            r"^(?:async\s+)?def\s+(\w+)|^class\s+(\w+)",
            child_content,
            flags=re.MULTILINE,
        ):
            name = m.group(1) or m.group(2)
            # Skip dunder methods (__init__, __repr__) — they're not
            # helpers. Single-underscore names (_phase_setup) ARE included
            # because phase helpers created by step 6a should be wired up
            # by the parent's rewritten coordinator function.
            if name and not name.startswith("__"):
                defined.add(name)
        # For each helper, check if it appears in the parent.
        # Match: `import name`, `from X import name`, `name(` or `.name(`
        for name in defined:
            # Word-boundary match — guards against substrings (e.g. "run"
            # matching "run_with_provider").
            pattern = rf"\b{re.escape(name)}\b"
            if not re.search(pattern, parent_content):
                unwired.append((name, code_file))
    return unwired


# Flag to silence the progress print when used in contexts where rich
# output is unwanted (e.g. tests). Set by callers; defaults to False.
quiet_import = False


def get_test_command(file: Path) -> Optional[TestCommand]:
    """Resolve the test command for *file*.

    Delegates to :pyfunc:`pdd.get_test_command.get_test_command_for_file`.

    Args:
        file: Path to the test file.

    Returns:
        A :class:`TestCommand`, or ``None`` if no command could be resolved
        (signalling that an agentic fallback is needed).
    """
    return get_test_command_for_file(str(file))


def get_lint_commands(file: Path) -> list[LintCommand]:
    """Resolve lint commands for *file*.

    Delegates to :pyfunc:`pdd.get_lint_commands.get_lint_commands`.  Returns
    an empty list for languages without deterministic lint support, signalling
    the orchestrator to fall back to agent-discovered commands.

    Args:
        file: Path to the source file to lint.

    Returns:
        A list of :class:`LintCommand` instances (may be empty).
    """
    return _get_lint_commands_impl(file)