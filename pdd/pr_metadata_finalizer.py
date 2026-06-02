"""Finalize PDD fingerprints at CLI-created PR boundaries."""

from __future__ import annotations

import json
import os
import subprocess
import threading
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Set, Tuple

from .architecture_registry import find_architecture_for_project
from .git_porcelain import iter_changed_paths, parse_porcelain_z
from .metadata_sync import run_metadata_sync
from .operation_log import (
    get_fingerprint_path,
    get_run_report_path,
    infer_module_identity,
    save_fingerprint,
)
from .sync_determine_operation import (
    calculate_current_hashes,
    get_extension,
    get_pdd_file_paths,
    read_fingerprint,
)


_FINALIZE_LOCK = threading.Lock()
_EXCLUDED_PARTS = {
    ".git",
    ".pdd",
    ".venv",
    "venv",
    "env",
    "__pycache__",
    "node_modules",
    ".pytest_cache",
    ".mypy_cache",
    ".ruff_cache",
    ".tox",
    ".nox",
    "dist",
    "build",
}
_KNOWN_LANGUAGES = (
    "python",
    "javascript",
    "typescript",
    "typescriptreact",
    "javascriptreact",
    "prisma",
    "java",
    "cpp",
    "c",
    "ruby",
    "go",
    "rust",
    "php",
    "swift",
    "kotlin",
    "scala",
    "csharp",
    "css",
    "html",
    "sql",
    "shell",
    "bash",
    "powershell",
    "r",
    "matlab",
    "lua",
    "perl",
    "llm",
    "md",
    "json",
    "yaml",
    "yml",
)


def _strip_current_dir_prefix(path: str) -> str:
    normalized = path.replace("\\", "/")
    while normalized.startswith("./"):
        normalized = normalized[2:]
    return normalized


@dataclass(frozen=True)
class FinalizedFingerprint:
    """Fingerprint written for one PDD module."""

    basename: str
    language: str
    prompt_path: Path
    metadata_path: Path

    @property
    def metadata_relpath(self) -> str:
        """Return the repo-relative metadata path as POSIX text."""
        return self.metadata_path.as_posix()


@dataclass(frozen=True)
class PRMetadataFinalizationResult:
    """Result for PR-boundary metadata finalization."""

    ok: bool
    finalized: Tuple[FinalizedFingerprint, ...] = ()
    touched_modules: Tuple[str, ...] = ()
    message: str = ""

    @property
    def metadata_paths(self) -> Tuple[str, ...]:
        """Return repo-relative metadata paths in finalization order."""
        return tuple(item.metadata_relpath for item in self.finalized)


@dataclass
class _ModuleInfo:
    basename: str
    language: str
    prompt_path: Path
    paths: Dict[str, object]
    relpaths: Set[str]


@contextmanager
def _pushd(path: Path) -> Iterator[None]:
    previous = Path.cwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(previous)


def is_pdd_meta_artifact(path: str) -> bool:
    """Return True for operation-log files under ``.pdd/meta``."""
    normalized = _strip_current_dir_prefix(path)
    return normalized.startswith(".pdd/meta/")


def _repo_rel(path: Path, repo_root: Path) -> str:
    try:
        return path.resolve().relative_to(repo_root.resolve()).as_posix()
    except (OSError, ValueError):
        return _strip_current_dir_prefix(path.as_posix())


def _as_abs(path_like: object, repo_root: Path) -> Optional[Path]:
    if not isinstance(path_like, Path):
        return None
    return path_like if path_like.is_absolute() else repo_root / path_like


def _normalize_changed_path(path: str, repo_root: Path) -> str:
    raw = Path(path)
    if raw.is_absolute():
        return _repo_rel(raw, repo_root)
    return _strip_current_dir_prefix(raw.as_posix())


def _git_changed_paths(repo_root: Path) -> List[str]:
    result = subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"],
        cwd=repo_root,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        return []
    return list(iter_changed_paths(parse_porcelain_z(result.stdout)))


def _prompt_roots(
    repo_root: Path,
    changed_paths: Optional[Iterable[str]] = None,
) -> List[Path]:
    candidate_roots: List[Path] = [
        repo_root / "prompts",
        repo_root / "pdd" / "prompts",
    ]
    for changed_path in changed_paths or ():
        relpath = _normalize_changed_path(changed_path, repo_root)
        if not relpath:
            continue
        parts = Path(relpath).parts
        for index, part in enumerate(parts):
            if part == "prompts":
                candidate_roots.append(repo_root.joinpath(*parts[: index + 1]))
                break

        current = (repo_root / relpath).parent
        try:
            current.relative_to(repo_root)
        except ValueError:
            continue
        while True:
            candidate_roots.append(current / "prompts")
            if current == repo_root:
                break
            current = current.parent
    return _valid_prompt_roots(repo_root, candidate_roots)


def _valid_prompt_roots(repo_root: Path, candidates: Iterable[Path]) -> List[Path]:
    roots: List[Path] = []
    seen: Set[Path] = set()
    for candidate in candidates:
        try:
            rel_parts = candidate.relative_to(repo_root).parts
            if any(part in _EXCLUDED_PARTS for part in rel_parts):
                continue
            resolved = candidate.resolve()
        except (OSError, ValueError):
            continue
        if not resolved.is_dir() or resolved in seen:
            continue
        seen.add(resolved)
        roots.append(resolved)
    return roots


def _is_relative_to(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
    except ValueError:
        return False
    return True


def _languages_for_suffix(suffix: str) -> Tuple[str, ...]:
    normalized = suffix.lower().lstrip(".")
    if not normalized:
        return ()
    languages = tuple(
        language
        for language in _KNOWN_LANGUAGES
        if get_extension(language) == normalized
    )
    return languages or (normalized,)


def _basename_variants(path: Path) -> Set[str]:
    stem = path.stem
    variants = {stem}
    if stem.startswith("test_"):
        variants.add(stem[len("test_") :])
    if stem.endswith("_example"):
        variants.add(stem[: -len("_example")])
    return {variant for variant in variants if variant}


def _prompt_candidates_for_filename(
    repo_root: Path,
    roots: Sequence[Path],
    filename: str,
) -> Iterator[Path]:
    raw = Path(_strip_current_dir_prefix(filename))
    if raw.is_absolute():
        yield raw
        return
    for root in roots:
        yield root / raw
        yield root.parent / raw
    yield repo_root / raw


def _architecture_prompt_candidates(
    repo_root: Path,
    changed: Set[str],
    roots: Sequence[Path],
) -> Iterator[Path]:
    for architecture_path in find_architecture_for_project(repo_root):
        try:
            data = json.loads(architecture_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(data, list):
            entries = data
        elif isinstance(data, dict):
            entries = data.get("modules", [])
        else:
            continue
        for entry in entries:
            if not isinstance(entry, dict):
                continue
            filepath = entry.get("filepath")
            filename = entry.get("filename")
            if not isinstance(filepath, str) or not isinstance(filename, str):
                continue
            normalized_filepath = _strip_current_dir_prefix(Path(filepath).as_posix())
            if normalized_filepath not in changed:
                continue
            yield from _prompt_candidates_for_filename(repo_root, roots, filename)


def _shape_prompt_candidates(
    repo_root: Path,
    changed: Set[str],
    roots: Sequence[Path],
) -> Iterator[Path]:
    for relpath in changed:
        path = Path(relpath)
        if path.suffix == ".prompt":
            yield repo_root / path
            continue
        languages = _languages_for_suffix(path.suffix)
        if not languages:
            continue
        base_variants = _basename_variants(path)
        for root in roots:
            path_variants = set(base_variants)
            module_root = root.parent
            try:
                relative_to_module = (repo_root / path).relative_to(module_root)
            except ValueError:
                relative_to_module = None
            if relative_to_module is not None:
                rel_without_suffix = relative_to_module.with_suffix("")
                path_variants.add(rel_without_suffix.as_posix())
                rel_parts = rel_without_suffix.parts
                if rel_parts and rel_parts[0] in {
                    "test",
                    "tests",
                    "example",
                    "examples",
                    "context",
                }:
                    path_variants.add(Path(*rel_parts[1:]).as_posix())
            for variant in path_variants:
                for language in languages:
                    yield root / f"{variant}_{language}.prompt"


def _targeted_prompt_candidates(
    repo_root: Path,
    changed_paths: Optional[Iterable[str]] = None,
) -> List[Path]:
    if changed_paths is None:
        return []
    changed = {
        _normalize_changed_path(path, repo_root)
        for path in changed_paths
        if path and not is_pdd_meta_artifact(path)
    }
    if not changed:
        return []
    roots = _prompt_roots(repo_root, changed)
    candidates = list(_shape_prompt_candidates(repo_root, changed, roots))
    candidates.extend(_architecture_prompt_candidates(repo_root, changed, roots))
    return _valid_prompt_candidates(repo_root, candidates, roots)


def _valid_prompt_candidates(
    repo_root: Path,
    candidates: Iterable[Path],
    roots: Sequence[Path],
) -> List[Path]:
    prompts: List[Path] = []
    seen: Set[Path] = set()
    resolved_roots = tuple(root.resolve() for root in roots)
    for candidate in candidates:
        try:
            rel_parts = candidate.relative_to(repo_root).parts
            if any(part in _EXCLUDED_PARTS for part in rel_parts):
                continue
            resolved = candidate.resolve()
        except (OSError, ValueError):
            continue
        if not any(_is_relative_to(resolved, root) for root in resolved_roots):
            continue
        if resolved in seen or not resolved.is_file() or resolved.suffix != ".prompt":
            continue
        seen.add(resolved)
        prompts.append(resolved)
    return prompts


def _prompt_scan_candidates(
    repo_root: Path,
    changed_paths: Optional[Iterable[str]] = None,
) -> Iterator[Path]:
    targeted = _targeted_prompt_candidates(repo_root, changed_paths)
    if targeted:
        yield from targeted
        return
    roots = _prompt_roots(repo_root, changed_paths) or [repo_root]
    for root in roots:
        for prompt_path in root.rglob("*.prompt"):
            try:
                rel_parts = prompt_path.relative_to(repo_root).parts
            except ValueError:
                rel_parts = prompt_path.parts
            if any(part in _EXCLUDED_PARTS for part in rel_parts):
                continue
            if prompt_path.is_file():
                yield prompt_path


def _nearest_prompts_dir(prompt_path: Path) -> str:
    resolved = prompt_path.resolve()
    for parent in resolved.parents:
        if parent.name == "prompts":
            return parent.as_posix()
    return prompt_path.parent.as_posix()


def _module_paths(
    basename: str,
    language: str,
    prompt_path: Path,
) -> Dict[str, object]:
    module_root = Path(_nearest_prompts_dir(prompt_path)).parent
    try:
        with _pushd(module_root):
            paths = get_pdd_file_paths(
                basename,
                language,
                prompts_dir=_nearest_prompts_dir(prompt_path),
            )
    except Exception:  # pylint: disable=broad-exception-caught
        extension = get_extension(language)
        module_name = Path(basename).name
        code_path = module_root / f"{basename}.{extension}"
        example_path = module_root / "examples" / f"{module_name}_example.{extension}"
        test_path = module_root / "tests" / f"test_{module_name}.{extension}"
        paths = {
            "prompt": prompt_path,
            "code": code_path,
            "example": example_path,
            "test": test_path,
            "test_files": [test_path],
        }
    paths["prompt"] = prompt_path

    normalized: Dict[str, object] = {}
    for key, value in paths.items():
        if key == "test_files" and isinstance(value, list):
            normalized[key] = [
                p if p.is_absolute() else module_root / p
                for p in value
                if isinstance(p, Path)
            ]
        elif isinstance(value, Path):
            normalized[key] = value if value.is_absolute() else module_root / value
    return normalized


def _relpaths_for_paths(paths: Dict[str, object], repo_root: Path) -> Set[str]:
    relpaths: Set[str] = set()
    for key, value in paths.items():
        if key == "test_files" and isinstance(value, list):
            for item in value:
                if isinstance(item, Path):
                    relpaths.add(_repo_rel(item, repo_root))
        elif isinstance(value, Path):
            relpaths.add(_repo_rel(value, repo_root))
    return relpaths


def _discover_modules(
    repo_root: Path,
    changed_paths: Optional[Iterable[str]] = None,
) -> List[_ModuleInfo]:
    modules: List[_ModuleInfo] = []
    seen: Set[Tuple[str, str, str]] = set()
    for prompt_path in _prompt_scan_candidates(repo_root, changed_paths):
        basename, language = infer_module_identity(prompt_path)
        if not basename or not language:
            continue
        paths = _module_paths(basename, language, prompt_path)
        key = (basename, language, _repo_rel(prompt_path, repo_root))
        if key in seen:
            continue
        seen.add(key)
        modules.append(
            _ModuleInfo(
                basename=basename,
                language=language,
                prompt_path=prompt_path,
                paths=paths,
                relpaths=_relpaths_for_paths(paths, repo_root),
            )
        )
    modules.sort(key=lambda item: (item.basename, item.language))
    return modules


def _changed_modules(
    repo_root: Path,
    changed_paths: Sequence[str],
) -> List[_ModuleInfo]:
    changed = {
        _normalize_changed_path(path, repo_root)
        for path in changed_paths
        if path and not is_pdd_meta_artifact(path)
    }
    if not changed:
        return []
    modules = []
    for module in _discover_modules(repo_root, changed):
        if module.relpaths.intersection(changed):
            modules.append(module)
    return modules


def _preserved_command(module: _ModuleInfo) -> str:
    previous = read_fingerprint(module.basename, module.language, paths=module.paths)
    previous_command = getattr(previous, "command", None) if previous else None
    if previous_command in {"verify", "test", "fix", "update"}:
        return str(previous_command)
    return "fix"


def _verify_fingerprint_fresh(module: _ModuleInfo) -> Optional[str]:
    fingerprint = read_fingerprint(module.basename, module.language, paths=module.paths)
    if fingerprint is None:
        return "fingerprint missing after save"

    current = calculate_current_hashes(
        module.paths,
        stored_include_deps=fingerprint.include_deps,
    )
    checks = {
        "prompt_hash": fingerprint.prompt_hash,
        "code_hash": fingerprint.code_hash,
        "example_hash": fingerprint.example_hash,
        "test_hash": fingerprint.test_hash,
        "test_files": fingerprint.test_files,
    }
    for field, actual in checks.items():
        if field in current and current[field] != actual:
            return f"{field} is stale"
    return None


def _metadata_relpath(module: _ModuleInfo, repo_root: Path) -> Path:
    path = get_fingerprint_path(
        module.basename,
        module.language,
        paths=module.paths,
    )
    absolute = path if path.is_absolute() else repo_root / path
    return Path(_repo_rel(absolute, repo_root))


def _run_report_path(module: _ModuleInfo, repo_root: Path) -> Path:
    path = get_run_report_path(
        module.basename,
        module.language,
        paths=module.paths,
    )
    return path if path.is_absolute() else repo_root / path


def _restore_run_report(path: Path, contents: Optional[bytes]) -> None:
    if contents is None or path.exists():
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(contents)


def _restore_file(path: Path, contents: Optional[bytes]) -> None:
    """Restore ``path`` to its pre-sync snapshot (issue #1317).

    ``run_metadata_sync`` rewrites the prompt (tag block) and ``architecture.json``
    (entry) as a side effect, but finalization stages ONLY fingerprints. Roll
    those incidental writes back so a code-only PR never commits — or leaves
    unstaged — a prompt/arch change that is not part of the PR. ``contents is
    None`` means the file did not exist before the sync, so remove it if the
    sync created it; otherwise overwrite only when the bytes actually changed.
    """
    if path is None:
        return
    if contents is None:
        if path.exists():
            try:
                path.unlink()
            except OSError:
                pass
        return
    try:
        if not path.exists() or path.read_bytes() != contents:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(contents)
    except OSError:
        pass


def _architecture_for_module(
    prompt_path: Path,
    arch_candidates: Sequence[Path],
) -> Optional[Path]:
    """Pick the architecture.json that actually owns ``prompt_path`` (issue #1317).

    ``find_architecture_for_project`` returns the root first, so blindly using
    ``arch_candidates[0]`` finalizes a nested subproject against the PARENT's
    architecture — a same-named prompt then inherits the parent's tags/reason.
    Choose the candidate whose directory is the *nearest* ancestor of the
    prompt instead, falling back to the root when none contains it.
    """
    try:
        prompt_resolved = prompt_path.resolve()
    except OSError:
        prompt_resolved = prompt_path
    best: Optional[Path] = None
    best_depth = -1
    for arch in arch_candidates:
        arch_dir = arch.parent
        try:
            arch_dir_resolved = arch_dir.resolve()
        except OSError:
            arch_dir_resolved = arch_dir
        if _is_relative_to(prompt_resolved, arch_dir_resolved):
            depth = len(arch_dir_resolved.parts)
            if depth > best_depth:
                best_depth = depth
                best = arch
    if best is not None:
        return best
    return arch_candidates[0] if arch_candidates else None


def _stage_fingerprint(repo_root: Path, relpath: Path) -> Optional[str]:
    result = subprocess.run(
        ["git", "add", "-f", "--", relpath.as_posix()],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode == 0:
        return None
    return result.stderr.strip() or result.stdout.strip() or "git add failed"


def stage_paths_scoped(
    repo_root: Path,
    paths: Iterable[str],
    *,
    force: bool = False,
    exclude_pdd_meta: bool = True,
) -> Tuple[bool, str]:
    """Stage exact pathspecs, optionally excluding arbitrary ``.pdd/meta`` paths."""
    for path in paths:
        normalized = _normalize_changed_path(path, repo_root)
        if not normalized:
            continue
        if exclude_pdd_meta and is_pdd_meta_artifact(normalized):
            continue
        cmd = ["git", "add"]
        if force:
            cmd.append("-f")
        if normalized.startswith("-"):
            cmd.extend(["--", normalized])
        else:
            cmd.append(normalized)
        result = subprocess.run(
            cmd,
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode != 0:
            detail = result.stderr.strip() or result.stdout.strip()
            return False, f"Failed to stage {normalized}: {detail}"
    return True, ""


def finalize_pr_metadata(  # pylint: disable=too-many-locals
    repo_root: Path,
    changed_paths: Optional[Iterable[str]] = None,
    *,
    stage: bool = True,
) -> PRMetadataFinalizationResult:
    """Finalize fingerprints for PDD modules touched by a pending PR update."""
    repo_root = Path(repo_root).resolve()
    raw_changed = (
        list(changed_paths)
        if changed_paths is not None
        else _git_changed_paths(repo_root)
    )

    with _FINALIZE_LOCK:
        with _pushd(repo_root):
            modules = _changed_modules(repo_root, raw_changed)
            if not modules:
                return PRMetadataFinalizationResult(
                    ok=True,
                    message="No PDD-owned changes detected.",
                )

            arch_candidates = find_architecture_for_project(repo_root)

            finalized: List[FinalizedFingerprint] = []
            for module in modules:
                code_path = _as_abs(module.paths.get("code"), repo_root)
                # Issue #1317 FM3: finalize each module against the architecture
                # that owns it (nearest ancestor), not the root — a nested
                # subproject sharing a prompt filename must not inherit the
                # parent's tags/reason.
                architecture_path = _architecture_for_module(
                    module.prompt_path, arch_candidates
                )
                # Issue #1317 FM2: run_metadata_sync rewrites the prompt (tag
                # block) and architecture.json (entry) as a side effect, yet
                # finalization stages ONLY fingerprints. Snapshot those files
                # (and the run report) and restore them after the sync so the
                # fingerprint hashes the as-committed content and no unstaged
                # prompt/architecture rewrite leaks into the PR.
                prompt_abs = (
                    _as_abs(module.prompt_path, repo_root) or module.prompt_path
                )
                prompt_contents = (
                    prompt_abs.read_bytes() if prompt_abs.exists() else None
                )
                arch_contents = (
                    architecture_path.read_bytes()
                    if architecture_path is not None and architecture_path.exists()
                    else None
                )
                run_report_path = _run_report_path(module, repo_root)
                run_report_contents = (
                    run_report_path.read_bytes() if run_report_path.exists() else None
                )
                try:
                    result = run_metadata_sync(
                        module.prompt_path,
                        code_path=code_path,
                        repo_root=repo_root,
                        architecture_path=architecture_path,
                    )
                except Exception as exc:  # pylint: disable=broad-exception-caught
                    return PRMetadataFinalizationResult(
                        ok=False,
                        touched_modules=tuple(m.basename for m in modules),
                        message=(
                            f"metadata finalization failed for "
                            f"{module.basename}: {exc}"
                        ),
                    )
                finally:
                    _restore_run_report(run_report_path, run_report_contents)
                    _restore_file(prompt_abs, prompt_contents)
                    if architecture_path is not None:
                        _restore_file(architecture_path, arch_contents)
                if not getattr(result, "ok", False):
                    failing = getattr(result, "failing_stage", None) or "unknown"
                    return PRMetadataFinalizationResult(
                        ok=False,
                        touched_modules=tuple(m.basename for m in modules),
                        message=(
                            f"metadata finalization failed for "
                            f"{module.basename}: stage={failing}"
                        ),
                    )

                save_fingerprint(
                    basename=module.basename,
                    language=module.language,
                    operation=_preserved_command(module),
                    paths=module.paths,
                    cost=0.0,
                    model="metadata_sync",
                )
                stale_reason = _verify_fingerprint_fresh(module)
                if stale_reason:
                    return PRMetadataFinalizationResult(
                        ok=False,
                        touched_modules=tuple(m.basename for m in modules),
                        message=(
                            f"metadata finalization failed for "
                            f"{module.basename}: {stale_reason}"
                        ),
                    )

                metadata_path = _metadata_relpath(module, repo_root)
                if stage:
                    stage_error = _stage_fingerprint(repo_root, metadata_path)
                    if stage_error:
                        return PRMetadataFinalizationResult(
                            ok=False,
                            touched_modules=tuple(m.basename for m in modules),
                            message=(
                                "metadata staging verification failed: "
                                f"missing {metadata_path.as_posix()} ({stage_error})"
                            ),
                        )
                finalized.append(
                    FinalizedFingerprint(
                        basename=module.basename,
                        language=module.language,
                        prompt_path=module.prompt_path,
                        metadata_path=metadata_path,
                    )
                )

            return PRMetadataFinalizationResult(
                ok=True,
                finalized=tuple(finalized),
                touched_modules=tuple(module.basename for module in modules),
                message=(
                    "metadata finalized for "
                    + ", ".join(item.basename for item in finalized)
                ),
            )
