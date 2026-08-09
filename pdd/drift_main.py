"""Regeneration stability checks for PDD dev units (``pdd checkup drift``)."""

from __future__ import annotations

import ast
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterator, Optional

from .evidence_store import ManifestView

try:
    from .evidence_manifest import resolve_test_output_paths
except ImportError:  # pragma: no cover
    resolve_test_output_paths = None  # type: ignore[assignment,misc]

try:
    from .gate_main import run_gate_policy as _run_gate_policy_impl

    _GATE_POLICY_AVAILABLE = True
except (
    ModuleNotFoundError,
    ImportError,
):  # pragma: no cover - gate optional on this branch
    _GATE_POLICY_AVAILABLE = False

    def _run_gate_policy_impl(*_args, **_kwargs):
        class _Result:
            passed = False

        return _Result()


DEFAULT_MAX_COST_USD = 20.0
_COST_RE = re.compile(r"(?:Total\s+)?Cost:\s*\$([0-9]+(?:\.[0-9]+)?)", re.IGNORECASE)
_POLICY_VALIDATION_KEYS = ("policy", "gate", "checkup_gate", "policy_gate")
_SOURCE_TREE_ROOTS = frozenset({"src", "lib", "app"})
_SKIP_VALIDATION_STATUSES = frozenset(
    {"", "not_applicable", "not_available", "skipped"}
)
# Basename resolution is a convenience lookup, never authority to traverse an
# arbitrarily large repository-controlled tree. Explicit prompt paths bypass
# this bounded discovery path entirely.
_MAX_PROMPT_SCAN_ENTRIES = 10_000
_MAX_PROMPT_SCAN_SECONDS = 2.0


class DriftInputError(FileNotFoundError):
    """A stable, user-actionable failure while resolving drift inputs."""

    def __init__(self, code: str, message: str):
        self.code = code
        super().__init__(message)


@dataclass
class RunSnapshot:
    run_index: int
    code_sha256: str
    public_api: list[str]
    tests_passed: bool
    stories_passed: bool
    verify_passed: bool
    policy_passed: bool

    def as_dict(self) -> dict[str, Any]:
        return {
            "run_index": self.run_index,
            "code_sha256": self.code_sha256,
            "public_api": self.public_api,
            "tests_passed": self.tests_passed,
            "stories_passed": self.stories_passed,
            "verify_passed": self.verify_passed,
            "policy_passed": self.policy_passed,
        }


@dataclass
class DriftReport:
    devunit: str
    prompt_path: str
    code_path: str
    runs: int
    snapshots: list[RunSnapshot] = field(default_factory=list)
    baseline_public_api: list[str] = field(default_factory=list)
    public_api_unchanged: bool = True
    implementation_changed: bool = False
    behavior_unchanged: bool = True
    status: str = "stable"
    dry_run: bool = False
    max_cost_usd: Optional[float] = None
    total_cost_usd: float = 0.0
    cost_budget_exceeded: bool = False
    policy_check_skipped: bool = False
    policy_check_unavailable: bool = False

    @property
    def passed(self) -> bool:
        return self.status == "stable"

    @property
    def exit_code(self) -> int:
        return 0 if self.passed else 1

    def as_dict(self) -> dict[str, Any]:
        tests_passed = sum(1 for snap in self.snapshots if snap.tests_passed)
        stories_passed = sum(1 for snap in self.snapshots if snap.stories_passed)
        verify_passed = sum(1 for snap in self.snapshots if snap.verify_passed)
        policy_passed = sum(1 for snap in self.snapshots if snap.policy_passed)
        completed_runs = len(self.snapshots)
        return {
            "devunit": self.devunit,
            "prompt_path": self.prompt_path,
            "code_path": self.code_path,
            "runs": self.runs,
            "dry_run": self.dry_run,
            "status": self.status,
            "baseline_public_api": self.baseline_public_api,
            "public_api_unchanged": self.public_api_unchanged,
            "implementation_changed": self.implementation_changed,
            "behavior_unchanged": self.behavior_unchanged,
            "total_cost_usd": self.total_cost_usd,
            "cost_budget_exceeded": self.cost_budget_exceeded,
            "policy_check_skipped": self.policy_check_skipped,
            "policy_check_unavailable": self.policy_check_unavailable,
            "max_cost_usd": self.max_cost_usd,
            "tests": f"passed {tests_passed}/{completed_runs or self.runs}",
            "stories": f"passed {stories_passed}/{completed_runs or self.runs}",
            "verify": f"passed {verify_passed}/{completed_runs or self.runs}",
            "policy": f"passed {policy_passed}/{completed_runs or self.runs}",
            "snapshots": [snap.as_dict() for snap in self.snapshots],
        }


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _public_api(path: Path) -> list[str]:
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"))
    except (OSError, SyntaxError):
        return []
    names: list[str] = []
    for node in tree.body:
        if isinstance(node, ast.FunctionDef):
            names.append(f"def {node.name}")
        elif isinstance(node, ast.AsyncFunctionDef):
            names.append(f"async def {node.name}")
        elif isinstance(node, ast.ClassDef):
            names.append(f"class {node.name}")
    return sorted(names)


def _prompt_identity(prompt_path: Path) -> tuple[str, str]:
    """Return ``(basename, language)`` from a PDD prompt filename."""
    if prompt_path.suffix.lower() != ".prompt":
        raise DriftInputError(
            "drift_input_invalid",
            f"Prompt path must end in .prompt: {prompt_path}",
        )
    basename, separator, language = prompt_path.stem.rpartition("_")
    if not separator or not basename or not language:
        raise DriftInputError(
            "drift_input_invalid",
            f"Prompt filename must use <basename>_<language>.prompt: {prompt_path.name}",
        )
    return basename, language.lower()


def _resolve_code_path(
    prompt_path: Path,
    project_root: Path,
    *,
    basename: Optional[str] = None,
) -> Path:
    stem = basename or _prompt_identity(prompt_path)[0]
    candidates = [
        project_root / "pdd" / f"{stem}.py",
        project_root / "src" / f"{stem}.py",
        project_root / f"{stem}.py",
    ]
    for candidate in candidates:
        if candidate.is_file():
            return candidate.resolve()
    raise FileNotFoundError(
        f"Could not locate generated code for {prompt_path.name}; pass --code-file"
    )


def _resolve_project_file(
    raw_path: str | Path,
    project_root: Path,
    *,
    label: str,
) -> Path:
    """Resolve an existing file without allowing symlink or ``..`` escape."""
    root = project_root.resolve()
    path = Path(raw_path)
    candidate = path if path.is_absolute() else root / path
    try:
        resolved = candidate.resolve()
        resolved.relative_to(root)
    except (OSError, RuntimeError, ValueError) as exc:
        raise DriftInputError(
            "drift_input_outside_project",
            f"{label} must resolve inside project root {root}: {raw_path}",
        ) from exc
    if not resolved.is_file():
        raise DriftInputError(
            "drift_input_not_found",
            f"{label} not found: {raw_path}",
        )
    return resolved


def _active_prompt_roots(project_root: Path) -> list[Path]:
    """Return contained prompt roots declared by the active project config."""
    from .construct_paths import _find_pddrc_file, _load_pddrc_config

    root = project_root.resolve()
    candidates = [root / "prompts"]
    pddrc_path = _find_pddrc_file(root)
    if pddrc_path:
        try:
            config = _load_pddrc_config(pddrc_path)
        except ValueError as exc:
            raise DriftInputError(
                "drift_input_invalid",
                f"Could not load active .pddrc: {exc}",
            ) from exc
        contexts = config.get("contexts", {})
        if isinstance(contexts, dict):
            for context in contexts.values():
                if not isinstance(context, dict):
                    continue
                defaults = context.get("defaults", {})
                if not isinstance(defaults, dict):
                    continue
                configured = defaults.get("prompts_dir")
                if isinstance(configured, str) and configured.strip():
                    candidates.append(pddrc_path.parent / configured)

    contained: list[tuple[Path, Path]] = []
    for candidate in candidates:
        try:
            resolved = candidate.resolve()
            resolved.relative_to(root)
        except (OSError, RuntimeError, ValueError):
            continue
        if not resolved.is_dir():
            continue
        contained.append((candidate, resolved))

    # Scan each physical tree once. A canonical ``prompts/`` root commonly
    # contains several context-specific roots such as ``prompts/services``.
    roots: list[Path] = []
    resolved_roots: list[Path] = []
    for candidate, resolved in sorted(contained, key=lambda item: len(item[1].parts)):
        if any(resolved.is_relative_to(parent) for parent in resolved_roots):
            continue
        resolved_roots.append(resolved)
        roots.append(candidate)
    return roots


def _path_shaped_devunit(devunit: str) -> bool:
    return (
        Path(devunit).is_absolute()
        or "/" in devunit
        or "\\" in devunit
        or devunit.lower().endswith(".prompt")
    )


def _normalized_devunit_parts(devunit: str) -> tuple[str, ...]:
    if devunit != devunit.strip() or "\\" in devunit:
        raise DriftInputError(
            "drift_input_invalid",
            f"Invalid dev unit name: {devunit!r}",
        )
    parts = tuple(devunit.split("/"))
    if not parts or any(part in {"", ".", ".."} for part in parts):
        raise DriftInputError(
            "drift_input_invalid",
            f"Invalid dev unit name: {devunit!r}",
        )
    return parts


def _candidate_matches_devunit(
    candidate: Path,
    prompt_root: Path,
    devunit_parts: tuple[str, ...],
) -> bool:
    try:
        relative = candidate.relative_to(prompt_root)
    except ValueError:
        return False
    basename, _language = _prompt_identity(candidate)
    identity = (*relative.parent.parts, basename)
    if len(devunit_parts) == 1:
        return basename.casefold() == devunit_parts[0].casefold()
    if len(identity) < len(devunit_parts):
        return False
    return tuple(part.casefold() for part in identity[-len(devunit_parts) :]) == tuple(
        part.casefold() for part in devunit_parts
    )


def _owning_prompt_root(prompt_path: Path, roots: list[Path]) -> Path:
    owners: list[Path] = []
    for root in roots:
        try:
            prompt_path.relative_to(root.resolve())
        except ValueError:
            continue
        owners.append(root)
    if not owners:
        return prompt_path.parent
    return min(owners, key=lambda path: len(path.resolve().parts))


def _bounded_prompt_candidates(roots: list[Path]) -> Iterator[tuple[Path, Path]]:
    """Yield nested prompt candidates within bounded resolver work.

    The drift CLI accepts a short dev-unit name, so recursive discovery is
    useful, but must not let a hostile or accidentally huge prompt tree consume
    unbounded time or memory.  Bounds are global across configured roots and
    fail closed with an explicit-path remediation.
    """
    deadline = time.monotonic() + _MAX_PROMPT_SCAN_SECONDS
    scanned_entries = 0
    for prompt_root in roots:
        root = prompt_root.resolve()
        for directory, dirnames, filenames in os.walk(root, followlinks=False):
            dirnames.sort()
            filenames.sort()
            for _name in dirnames:
                scanned_entries += 1
                if (
                    scanned_entries > _MAX_PROMPT_SCAN_ENTRIES
                    or time.monotonic() > deadline
                ):
                    raise DriftInputError(
                        "drift_input_resolution_limit",
                        "Prompt discovery exceeded its safe scan limit; "
                        "pass an explicit path to the prompt file.",
                    )
            for _name in filenames:
                scanned_entries += 1
                if (
                    scanned_entries > _MAX_PROMPT_SCAN_ENTRIES
                    or time.monotonic() > deadline
                ):
                    raise DriftInputError(
                        "drift_input_resolution_limit",
                        "Prompt discovery exceeded its safe scan limit; "
                        "pass an explicit path to the prompt file.",
                    )
            for filename in filenames:
                if filename.endswith(".prompt"):
                    yield Path(directory) / filename, prompt_root


def _resolve_prompt_input(
    devunit: str,
    project_root: Path,
) -> tuple[Path, Path]:
    """Resolve explicit prompt paths or unambiguous basenames in active roots."""
    roots = _active_prompt_roots(project_root)
    if _path_shaped_devunit(devunit) and devunit.lower().endswith(".prompt"):
        prompt = _resolve_project_file(devunit, project_root, label="Prompt file")
        _prompt_identity(prompt)
        return prompt, _owning_prompt_root(prompt, roots)
    if _path_shaped_devunit(devunit) and Path(devunit).is_absolute():
        _resolve_project_file(devunit, project_root, label="Prompt file")
        raise DriftInputError(
            "drift_input_invalid",
            f"Prompt path must end in .prompt: {devunit}",
        )

    devunit_parts = _normalized_devunit_parts(devunit)
    matches: dict[Path, tuple[Path, Path]] = {}
    project_root_resolved = project_root.resolve()
    for candidate, prompt_root in _bounded_prompt_candidates(roots):
        if not candidate.is_file():
            continue
        try:
            resolved = candidate.resolve()
            resolved.relative_to(project_root_resolved)
            if not _candidate_matches_devunit(candidate, prompt_root, devunit_parts):
                continue
        except (DriftInputError, OSError, RuntimeError, ValueError):
            continue
        matches.setdefault(resolved, (candidate, prompt_root))

    if not matches:
        raise DriftInputError(
            "drift_input_not_found",
            f"Could not resolve prompt for dev unit {devunit!r}",
        )
    if len(matches) > 1:
        choices = sorted(
            candidate.relative_to(project_root).as_posix()
            for candidate, _prompt_root in matches.values()
        )
        rendered = ", ".join(choices)
        raise DriftInputError(
            "drift_input_ambiguous",
            f"Ambiguous prompt for dev unit {devunit!r}; use an explicit path: {rendered}",
        )
    resolved, (_candidate, prompt_root) = next(iter(matches.items()))
    return resolved, prompt_root


def _derive_code_from_prompt(
    prompt_path: Path,
    prompt_root: Path,
    project_root: Path,
) -> Path:
    """Use the shared PDD path resolver, then retain the flat legacy fallback."""
    basename, language = _prompt_identity(prompt_path)
    try:
        relative_prompt = prompt_path.relative_to(prompt_root.resolve())
    except ValueError as exc:
        raise DriftInputError(
            "drift_input_outside_project",
            f"Prompt file is not contained by its active prompt root: {prompt_path}",
        ) from exc
    qualified_basename = (relative_prompt.parent / basename).as_posix()
    try:
        from .sync_determine_operation import AmbiguousModuleError, get_pdd_file_paths

        paths = get_pdd_file_paths(
            qualified_basename,
            language,
            prompts_dir=str(prompt_root),
        )
        resolved_prompt = paths.get("prompt")
        if (
            resolved_prompt is not None
            and resolved_prompt.resolve() != prompt_path.resolve()
        ):
            raise DriftInputError(
                "drift_input_ambiguous",
                "Resolved code belongs to a different prompt; pass --code-file: "
                f"{resolved_prompt}",
            )
        resolved = paths.get("code")
        if resolved is not None and resolved.is_file():
            try:
                return _resolve_project_file(resolved, project_root, label="Code file")
            except DriftInputError:
                pass
    except AmbiguousModuleError as exc:
        raise DriftInputError("drift_input_ambiguous", str(exc)) from exc
    if qualified_basename != basename:
        raise DriftInputError(
            "drift_input_not_found",
            f"Could not locate generated code for {prompt_path.name}; pass --code-file",
        )
    return _resolve_code_path(prompt_path, project_root, basename=basename)


def _path_score(path: Path, *, expected_stem: str, devunit: str) -> int:
    score = 0
    if path.is_file():
        score += 100
    if path.suffix == ".py":
        score += 40
    if path.stem == expected_stem:
        score += 30
    if devunit in path.stem:
        score += 20
    if "/pdd/" in path.as_posix():
        score += 10
    return score


def _select_manifest_output(
    manifest: ManifestView,
    *,
    project_root: Path,
    expected_stem: str,
    devunit: str,
) -> Optional[Path]:
    best: Optional[Path] = None
    best_score = -1
    for output in manifest.outputs:
        raw = output.get("path")
        if not raw:
            continue
        candidate = Path(raw)
        if not candidate.is_absolute():
            candidate = project_root / candidate
        score = _path_score(candidate, expected_stem=expected_stem, devunit=devunit)
        if score > best_score:
            best_score = score
            best = candidate
    if best is not None and best.is_file():
        return best.resolve()
    return None


def _resolve_drift_inputs(
    devunit: str,
    project_root: Path,
    from_evidence: Optional[Path],
    code_file: Optional[Path],
) -> tuple[Path, Path, Optional[ManifestView]]:
    """Resolve the authoritative prompt/code pair for one drift invocation."""
    root = project_root.resolve()
    if from_evidence is None and not _path_shaped_devunit(devunit):
        latest = (
            project_root / ".pdd" / "evidence" / "devunits" / f"{devunit}.latest.json"
        )
        if latest.is_file():
            from_evidence = latest
    manifest = None
    if from_evidence is not None:
        if not from_evidence.is_file():
            raise DriftInputError(
                "drift_input_not_found",
                f"Evidence manifest not found: {from_evidence}",
            )
        try:
            manifest = ManifestView.from_file(from_evidence.resolve(), root)
        except (OSError, TypeError, ValueError) as exc:
            raise DriftInputError(
                "drift_input_invalid",
                f"Could not load evidence manifest {from_evidence}: {exc}",
            ) from exc

    roots = _active_prompt_roots(root)
    if manifest is not None and manifest.prompt_path is not None:
        prompt = _resolve_project_file(
            manifest.prompt_path,
            root,
            label="Evidence prompt file",
        )
        prompt_root = _owning_prompt_root(prompt, roots)
    else:
        prompt, prompt_root = _resolve_prompt_input(devunit, root)

    # An explicit code path is authoritative. Do not derive or validate a
    # manifest/default output first: that ordering was the core of issue #2001.
    if code_file is not None:
        code = _resolve_project_file(code_file, root, label="Code file")
        return prompt, code, manifest

    if manifest is not None:
        basename, _language = _prompt_identity(prompt)
        picked = _select_manifest_output(
            manifest,
            project_root=root,
            expected_stem=basename,
            devunit=devunit,
        )
        if picked is not None:
            code = _resolve_project_file(picked, root, label="Evidence code file")
            return prompt, code, manifest
    return prompt, _derive_code_from_prompt(prompt, prompt_root, root), manifest


def _parse_cost_usd(stdout: str, stderr: str) -> float:
    combined = f"{stdout}\n{stderr}"
    total = 0.0
    for match in _COST_RE.finditer(combined):
        total += float(match.group(1))
    return total


def _regenerate_code(
    prompt_path: Path,
    output_path: Path,
    *,
    model: Optional[str],
    project_root: Path,
) -> float:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        output_rel = output_path.relative_to(project_root)
    except ValueError:
        output_rel = output_path

    cmd = [
        sys.executable,
        "-m",
        "pdd",
        "generate",
        str(prompt_path.relative_to(project_root)),
        "--output",
        str(output_rel),
    ]
    if model:
        cmd.extend(["--model", model])
    completed = subprocess.run(
        cmd,
        cwd=project_root,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            f"pdd generate failed ({completed.returncode}): {completed.stderr.strip()}"
        )
    return _parse_cost_usd(completed.stdout, completed.stderr)


def _discover_tests(code_path: Path, project_root: Path) -> list[Path]:
    module = code_path.stem
    candidates = [
        project_root / "tests" / f"test_{module}.py",
        project_root / "tests" / f"test_{module.replace('_python', '')}.py",
    ]
    return [path for path in candidates if path.is_file()]


def _candidate_relative_path(code_path: Path, project_root: Path) -> Path:
    try:
        return code_path.relative_to(project_root)
    except ValueError:
        return Path(code_path.name)


def _ignore_cache_dir(_directory: str, names: list[str]) -> set[str]:
    return {name for name in names if name == "__pycache__"}


def _copy_project_subtree(source: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        shutil.rmtree(destination)
    shutil.copytree(source, destination, ignore=_ignore_cache_dir)


def _top_level_import_names(module_path: Path) -> set[str]:
    """Return top-level package/module names imported by ``module_path``."""
    try:
        tree = ast.parse(module_path.read_text(encoding="utf-8"))
    except (OSError, SyntaxError):
        return set()
    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                top = alias.name.split(".", maxsplit=1)[0]
                if top:
                    names.add(top)
        elif isinstance(node, ast.ImportFrom):
            if node.level == 0 and node.module:
                top = node.module.split(".", maxsplit=1)[0]
                if top:
                    names.add(top)
    return names


def _overlay_package_roots(
    rel: Path,
    project_root: Path,
    candidate: Path,
) -> list[Path]:
    """Directories to mirror so pytest can resolve local and cross-package imports."""
    roots: list[Path] = []
    seen: set[Path] = set()

    def add_root(path: Path) -> None:
        resolved = path.resolve()
        if resolved in seen or not path.is_dir():
            return
        seen.add(resolved)
        roots.append(path)

    if rel.parts:
        head = rel.parts[0]
        if head in _SOURCE_TREE_ROOTS:
            add_root(project_root / head)
        elif rel.parent != Path("."):
            add_root(project_root / rel.parent)

    for import_name in _top_level_import_names(candidate):
        imported = project_root / import_name
        if imported.is_dir():
            add_root(imported)
        elif import_name in _SOURCE_TREE_ROOTS:
            add_root(project_root / import_name)

    return roots


def _pytest_pythonpath(overlay_root: Path, rel: Path) -> str:
    """Build ``PYTHONPATH`` for overlay pytest (include ``src/`` roots when needed)."""
    entries = [overlay_root]
    if rel.parts and rel.parts[0] in _SOURCE_TREE_ROOTS:
        nested = overlay_root / rel.parts[0]
        if nested.is_dir():
            entries.append(nested)
    return os.pathsep.join(str(path) for path in entries)


def _copy_test_support_files(
    project_root: Path,
    overlay_root: Path,
    test_paths: list[Path],
) -> Path:
    """Mirror discovered tests, local helpers, and ``conftest.py`` files into the overlay."""
    overlay_tests = overlay_root / "tests"
    for test_path in test_paths:
        rel_test = test_path.relative_to(project_root)
        dest_test = overlay_root / rel_test
        dest_test.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(test_path, dest_test)
        for helper in test_path.parent.glob("*.py"):
            if helper.name == test_path.name or helper.name.startswith("test_"):
                continue
            rel_helper = helper.relative_to(project_root)
            dest_helper = overlay_root / rel_helper
            dest_helper.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(helper, dest_helper)

    project_tests = project_root / "tests"
    if project_tests.is_dir():
        for conftest in project_tests.rglob("conftest.py"):
            rel_conftest = conftest.relative_to(project_root)
            dest_conftest = overlay_root / rel_conftest
            dest_conftest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(conftest, dest_conftest)

    return overlay_tests


def _build_pytest_overlay(
    candidate: Path,
    code_path: Path,
    project_root: Path,
    overlay_root: Path,
) -> Optional[Path]:
    """Build an overlay with project package deps and the candidate replacing baseline."""
    rel = _candidate_relative_path(code_path, project_root)
    for source_root in _overlay_package_roots(rel, project_root, candidate):
        destination = overlay_root / source_root.relative_to(project_root)
        _copy_project_subtree(source_root, destination)

    module_dest = overlay_root / rel
    module_dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(candidate, module_dest)

    tests = _discover_tests(code_path, project_root)
    if not tests:
        return None

    return _copy_test_support_files(project_root, overlay_root, tests)


def _run_pytest_for_candidate(
    candidate: Path,
    code_path: Path,
    project_root: Path,
    sandbox_root: Path,
) -> bool:
    tests = _discover_tests(code_path, project_root)
    if not tests:
        return True

    overlay_root = sandbox_root / "pytest-overlay"
    if overlay_root.exists():
        shutil.rmtree(overlay_root)
    overlay_root.mkdir(parents=True, exist_ok=True)

    rel = _candidate_relative_path(code_path, project_root)
    overlay_tests = _build_pytest_overlay(
        candidate,
        code_path,
        project_root,
        overlay_root,
    )
    if overlay_tests is None:
        return True

    env = os.environ.copy()
    env["PYTHONPATH"] = _pytest_pythonpath(overlay_root, rel)
    cmd = [sys.executable, "-m", "pytest", "-q", str(overlay_tests)]
    completed = subprocess.run(
        cmd,
        cwd=overlay_root,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )
    return completed.returncode == 0


def _validation_key_configured(
    manifest: Optional[ManifestView], keys: tuple[str, ...]
) -> bool:
    if manifest is None:
        return False
    for key in keys:
        status = (manifest.validation.get(key) or "").strip().lower()
        if status and status not in _SKIP_VALIDATION_STATUSES:
            return True
    return False


def _stories_configured(manifest: Optional[ManifestView]) -> bool:
    return _validation_key_configured(manifest, ("detect_stories",))


def _verify_configured(manifest: Optional[ManifestView]) -> bool:
    return _validation_key_configured(manifest, ("verify",))


def _policy_configured(project_root: Path, manifest: Optional[ManifestView]) -> bool:
    policy_paths = (
        project_root / ".pdd" / "policy.yml",
        project_root / ".pdd" / "policy.yaml",
        project_root / "policy.yml",
        project_root / "policy.yaml",
    )
    if any(path.is_file() for path in policy_paths):
        return True
    return _validation_key_configured(manifest, _POLICY_VALIDATION_KEYS)


def _run_stories_check(prompt_path: Path, project_root: Path) -> tuple[bool, float]:
    from .user_story_tests import run_user_story_tests  # pylint: disable=import-outside-toplevel

    passed, _, cost, _ = run_user_story_tests(
        prompt_files=[prompt_path],
        prompts_dir=str(project_root / "prompts"),
        quiet=True,
        fail_fast=True,
    )
    return passed, cost


def _run_policy_check(
    project_root: Path,
    manifest: Optional[ManifestView],
    devunit: str,
) -> tuple[bool, bool, bool]:
    """Return ``(passed, skipped, unavailable)`` for policy evaluation."""
    if not _policy_configured(project_root, manifest):
        return True, True, False
    if not _GATE_POLICY_AVAILABLE:
        return False, False, True
    return _run_gate_policy_impl(project_root, target=devunit).passed, False, False


def _run_verify_check(
    prompt_path: Path,
    candidate: Path,
    code_path: Path,
    project_root: Path,
    work_dir: Path,
    *,
    verify_budget_usd: float,
) -> tuple[bool, float]:
    if resolve_test_output_paths is None:
        return True, 0.0

    prompt_copy = work_dir / "prompt" / prompt_path.name
    code_copy = work_dir / "code" / code_path.name
    prompt_copy.parent.mkdir(parents=True, exist_ok=True)
    code_copy.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(prompt_path, prompt_copy)
    shutil.copy2(candidate, code_copy)

    program_paths = resolve_test_output_paths(
        prompt_copy,
        code_copy,
        force=True,
        quiet=True,
    )
    if not program_paths:
        return True, 0.0

    program_source = Path(program_paths[0])
    if not program_source.is_file():
        return True, 0.0

    program_copy = work_dir / "program" / program_source.name
    program_copy.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(program_source, program_copy)

    cmd = [
        sys.executable,
        "-m",
        "pdd",
        "verify",
        str(prompt_copy),
        str(code_copy),
        str(program_copy),
        "--max-attempts",
        "1",
        "--budget",
        str(max(verify_budget_usd, 0.01)),
        "--no-agentic-fallback",
    ]
    completed = subprocess.run(
        cmd,
        cwd=project_root,
        capture_output=True,
        text=True,
        check=False,
    )
    cost = _parse_cost_usd(completed.stdout, completed.stderr)
    return completed.returncode == 0, cost


def _evaluate_candidate(
    candidate: Path,
    *,
    prompt_path: Path,
    code_path: Path,
    project_root: Path,
    manifest: Optional[ManifestView],
    devunit: str,
    sandbox_root: Path,
    work_dir: Path,
    verify_budget_usd: float,
) -> tuple[RunSnapshot, float]:
    extra_cost = 0.0
    tests_ok = _run_pytest_for_candidate(
        candidate, code_path, project_root, sandbox_root
    )

    if _stories_configured(manifest):
        stories_ok, stories_cost = _run_stories_check(prompt_path, project_root)
        extra_cost += stories_cost
    else:
        stories_ok = True

    if _verify_configured(manifest):
        verify_ok, verify_cost = _run_verify_check(
            prompt_path,
            candidate,
            code_path,
            project_root,
            work_dir,
            verify_budget_usd=verify_budget_usd,
        )
        extra_cost += verify_cost
    else:
        verify_ok = True

    policy_ok, _policy_skipped, _policy_unavailable = _run_policy_check(
        project_root,
        manifest,
        devunit,
    )

    return (
        RunSnapshot(
            run_index=0,
            code_sha256=_sha256_file(candidate),
            public_api=_public_api(candidate),
            tests_passed=tests_ok,
            stories_passed=stories_ok,
            verify_passed=verify_ok,
            policy_passed=policy_ok,
        ),
        extra_cost,
    )


def run_drift(
    devunit: str,
    project_root: Path,
    *,
    runs: int = 1,
    model: Optional[str] = None,
    from_evidence: Optional[Path] = None,
    code_file: Optional[Path] = None,
    dry_run: bool = False,
    max_cost_usd: Optional[float] = None,
) -> DriftReport:
    prompt_path, code_path, manifest = _resolve_drift_inputs(
        devunit,
        project_root,
        from_evidence,
        code_file,
    )

    if not code_path.is_file():
        raise FileNotFoundError(f"Code file not found: {code_path}")

    effective_max_cost = max_cost_usd
    if effective_max_cost is None and not dry_run:
        effective_max_cost = DEFAULT_MAX_COST_USD

    baseline_bytes = code_path.read_bytes()
    baseline_api = _public_api(code_path)
    baseline_hash = hashlib.sha256(baseline_bytes).hexdigest()

    snapshots: list[RunSnapshot] = []
    candidate_hashes: list[str] = []
    candidate_apis: list[str] = []
    total_cost = 0.0
    cost_budget_exceeded = False
    policy_check_skipped = not _policy_configured(project_root, manifest)
    policy_check_unavailable = (
        _policy_configured(project_root, manifest) and not _GATE_POLICY_AVAILABLE
    )

    with tempfile.TemporaryDirectory(prefix="pdd-drift-") as temp_name:
        temp_root = Path(temp_name)
        sandbox_root = temp_root / "sandbox"
        sandbox_root.mkdir(parents=True, exist_ok=True)

        for run_index in range(runs):
            work_dir = temp_root / f"run-{run_index + 1}"
            work_dir.mkdir(parents=True, exist_ok=True)

            if dry_run:
                candidate = code_path
            else:
                rel = _candidate_relative_path(code_path, project_root)
                candidate = temp_root / "candidates" / f"run-{run_index + 1}" / rel
                run_cost = _regenerate_code(
                    prompt_path,
                    candidate,
                    model=model,
                    project_root=project_root,
                )
                total_cost += run_cost
                if effective_max_cost is not None and total_cost > effective_max_cost:
                    cost_budget_exceeded = True
                    break

            remaining_budget = (
                max(effective_max_cost - total_cost, 0.01)
                if effective_max_cost is not None
                else 5.0
            )
            snapshot, eval_cost = _evaluate_candidate(
                candidate,
                prompt_path=prompt_path,
                code_path=code_path,
                project_root=project_root,
                manifest=manifest,
                devunit=devunit,
                sandbox_root=sandbox_root,
                work_dir=work_dir,
                verify_budget_usd=remaining_budget,
            )
            total_cost += eval_cost
            if effective_max_cost is not None and total_cost > effective_max_cost:
                cost_budget_exceeded = True
                break

            snapshot.run_index = run_index + 1
            snapshots.append(snapshot)
            candidate_hashes.append(snapshot.code_sha256)
            candidate_apis.append(snapshot.public_api)

    if code_path.read_bytes() != baseline_bytes:
        raise RuntimeError(
            f"Drift check mutated baseline code file: {code_path}. "
            "This should never happen; report a bug."
        )

    public_api_unchanged = bool(candidate_apis) and all(
        api == baseline_api for api in candidate_apis
    )
    implementation_changed = (
        any(h != baseline_hash for h in candidate_hashes)
        or len(set(candidate_hashes)) > 1
    )
    behavior_unchanged = all(
        snap.tests_passed
        and snap.stories_passed
        and snap.verify_passed
        and snap.policy_passed
        for snap in snapshots
    )
    status = (
        "stable"
        if public_api_unchanged and behavior_unchanged and not cost_budget_exceeded
        else "unstable"
    )

    return DriftReport(
        devunit=devunit,
        prompt_path=str(prompt_path),
        code_path=str(code_path),
        runs=runs,
        snapshots=snapshots,
        baseline_public_api=baseline_api,
        public_api_unchanged=public_api_unchanged,
        implementation_changed=implementation_changed,
        behavior_unchanged=behavior_unchanged,
        status=status,
        dry_run=dry_run,
        max_cost_usd=effective_max_cost,
        total_cost_usd=total_cost,
        cost_budget_exceeded=cost_budget_exceeded,
        policy_check_skipped=policy_check_skipped,
        policy_check_unavailable=policy_check_unavailable,
    )
