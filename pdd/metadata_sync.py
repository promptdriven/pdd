from __future__ import annotations

import os
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Literal, Optional

from pydantic import BaseModel, Field
from rich.console import Console
from rich.theme import Theme

from .architecture_sync import (
    generate_tags_from_architecture,
    has_pdd_tags,
    parse_prompt_tags,
    update_architecture_from_prompt,
)
from .architecture_registry import find_architecture_for_project
from .operation_log import clear_run_report, infer_module_identity, save_fingerprint


_THEME = Theme(
    {
        "info": "cyan",
        "warning": "yellow",
        "error": "bold red",
        "success": "green",
    }
)
console = Console(theme=_THEME)


StageName = Literal["prompt", "tags", "architecture", "run_report", "fingerprint"]
StageStatusLiteral = Literal["ok", "skipped", "failed", "dry_run"]

STAGE_ORDER: List[str] = ["prompt", "tags", "architecture", "run_report", "fingerprint"]


class StageStatus(BaseModel):
    status: StageStatusLiteral
    reason: Optional[str] = None
    detail: Optional[str] = None


class MetadataSyncResult(BaseModel):
    prompt_path: Path
    code_path: Optional[Path] = None
    dry_run: bool = False
    stages: Dict[str, StageStatus] = Field(default_factory=dict)

    @property
    def ok(self) -> bool:
        for name in STAGE_ORDER:
            stage = self.stages.get(name)
            if stage is None:
                return False
            if stage.status not in ("ok", "dry_run", "skipped"):
                return False
        # Treat 'failed' anywhere as not-ok; skipped/dry_run/ok all acceptable.
        return not any(s.status == "failed" for s in self.stages.values())

    @property
    def failing_stage(self) -> Optional[str]:
        for name in STAGE_ORDER:
            stage = self.stages.get(name)
            if stage is not None and stage.status == "failed":
                return name
        return None


def _resolve_repo_root(prompt_path: Path) -> Path:
    """Walk up from prompt_path to find repo root markers."""
    markers = (".git", ".pddrc", "pyproject.toml")
    start = prompt_path.resolve().parent
    current = start
    while True:
        for marker in markers:
            if (current / marker).exists():
                return current
        if current.parent == current:
            return start
        current = current.parent


def _resolve_prompts_dir(prompt_path: Path, repo_root: Path) -> Path:
    """Find the nearest 'prompts' ancestor directory, else fall back to parent."""
    resolved = prompt_path.resolve()
    for parent in resolved.parents:
        if parent.name == "prompts":
            return parent
    fallback = repo_root / "prompts"
    if fallback.exists():
        return fallback
    return resolved.parent


def _atomic_write(path: Path, content: str) -> None:
    """Write `content` to `path` atomically by writing to temp then renaming."""
    path = path.resolve()
    parent = path.parent
    parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_path = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=str(parent))
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            fh.write(content)
        os.replace(tmp_path, path)
    except Exception:
        try:
            os.unlink(tmp_path)
        except OSError:
            pass
        raise


def _stage_log_enter(stage: str) -> None:
    console.print(f"[info][metadata-sync] → stage: {stage}[/info]")


def _stage_log_exit(stage: str, status: StageStatusLiteral, detail: Optional[str] = None) -> None:
    suffix = f" ({detail})" if detail else ""
    if status == "ok":
        console.print(f"[success][metadata-sync] ✓ {stage}: ok{suffix}[/success]")
    elif status == "dry_run":
        console.print(f"[info][metadata-sync] ⋯ {stage}: dry_run{suffix}[/info]")
    elif status == "skipped":
        console.print(f"[warning][metadata-sync] ⊘ {stage}: skipped{suffix}[/warning]")
    elif status == "failed":
        console.print(f"[error][metadata-sync] ✗ {stage}: failed{suffix}[/error]")


def _refresh_tags_content(prompt_content: str, arch_entry: Optional[Dict[str, Any]]) -> Optional[str]:
    """
    Compute refreshed prompt content with PDD tags.

    Strategy:
    - If the prompt already has tags, return None (idempotent — leave as-is).
    - Else, if we have an architecture entry, prepend generated tags.
    - Else, return None (cannot generate tags without source-of-truth data).

    This is conservative: we never duplicate tag blocks. LLM-driven enrichment
    (issue #870) plugs in here when available; for now we honor existing tags
    and only seed from architecture when missing.
    """
    if has_pdd_tags(prompt_content):
        return None
    if not arch_entry:
        return None
    tag_block = generate_tags_from_architecture(arch_entry).strip()
    if not tag_block:
        return None
    if prompt_content.startswith(tag_block):
        return None
    return tag_block + "\n\n" + prompt_content


def _load_arch_entry_for_prompt(
    prompt_path: Path, architecture_path: Optional[Path]
) -> Optional[Dict[str, Any]]:
    """Best-effort lookup of the architecture.json entry for this prompt."""
    if architecture_path is None or not architecture_path.exists():
        return None
    try:
        import json

        data = json.loads(architecture_path.read_text(encoding="utf-8"))
    except Exception:
        return None
    modules = data.get("modules") if isinstance(data, dict) else None
    if not isinstance(modules, list):
        return None
    target = prompt_path.name
    for entry in modules:
        if not isinstance(entry, dict):
            continue
        if entry.get("prompt") == target or entry.get("prompt_file") == target:
            return entry
    return None


def run_metadata_sync(
    prompt_path: Path,
    code_path: Optional[Path] = None,
    *,
    dry_run: bool = False,
    repo_root: Optional[Path] = None,
    architecture_path: Optional[Path] = None,
) -> MetadataSyncResult:
    """
    Orchestrate prompt metadata finalization in a fixed pipeline.

    Stages (in order): prompt → tags → architecture → run_report → fingerprint.

    Each stage fails soft (records 'failed' and continues) except `prompt`,
    which short-circuits the rest of the pipeline if it fails. Fingerprint is
    gated: skipped if any earlier stage failed.
    """
    prompt_path = Path(prompt_path)
    if code_path is not None:
        code_path = Path(code_path)

    result = MetadataSyncResult(
        prompt_path=prompt_path,
        code_path=code_path,
        dry_run=dry_run,
        stages={},
    )

    # Resolve repo_root
    try:
        resolved_repo_root = Path(repo_root).resolve() if repo_root else _resolve_repo_root(prompt_path)
    except (KeyboardInterrupt, SystemExit):
        raise
    except Exception:
        resolved_repo_root = prompt_path.resolve().parent

    # Resolve architecture_path
    if architecture_path is None:
        try:
            candidates = find_architecture_for_project(resolved_repo_root)
            architecture_path = candidates[0] if candidates else None
        except (KeyboardInterrupt, SystemExit):
            raise
        except Exception:
            architecture_path = None
    else:
        architecture_path = Path(architecture_path)

    prompts_dir = _resolve_prompts_dir(prompt_path, resolved_repo_root)

    # ---- Stage 1: prompt ----
    _stage_log_enter("prompt")
    prompt_content: Optional[str] = None
    try:
        if not prompt_path.exists():
            raise FileNotFoundError(f"prompt file not found: {prompt_path}")
        prompt_content = prompt_path.read_text(encoding="utf-8")
        if not prompt_content.strip():
            raise ValueError(f"prompt file is empty: {prompt_path}")
        result.stages["prompt"] = StageStatus(
            status="ok",
            detail=f"{len(prompt_content)} chars",
        )
        _stage_log_exit("prompt", "ok", f"{len(prompt_content)} chars")
    except (KeyboardInterrupt, SystemExit):
        raise
    except Exception as exc:
        reason = str(exc)
        result.stages["prompt"] = StageStatus(status="failed", reason=reason)
        _stage_log_exit("prompt", "failed", reason)
        # Short-circuit: mark remaining stages skipped.
        for stage in STAGE_ORDER[1:]:
            result.stages[stage] = StageStatus(
                status="skipped", reason=f"prompt stage failed: {reason}"
            )
            _stage_log_exit(stage, "skipped", "prompt stage failed")
        return result

    # ---- Stage 2: tags ----
    _stage_log_enter("tags")
    refreshed_prompt_content: str = prompt_content  # carry forward to architecture stage
    try:
        arch_entry = _load_arch_entry_for_prompt(prompt_path, architecture_path)
        new_content = _refresh_tags_content(prompt_content, arch_entry)
        if new_content is None or new_content == prompt_content:
            # Already has tags or nothing to do — stable / idempotent.
            existing = parse_prompt_tags(prompt_content)
            tag_count = sum(
                [
                    1 if existing.get("reason") else 0,
                    1 if existing.get("interface") else 0,
                    len(existing.get("dependencies") or []),
                ]
            )
            detail = f"existing tags preserved ({tag_count} tag(s))"
            if dry_run:
                result.stages["tags"] = StageStatus(status="dry_run", detail=detail)
                _stage_log_exit("tags", "dry_run", detail)
            else:
                result.stages["tags"] = StageStatus(status="ok", detail=detail)
                _stage_log_exit("tags", "ok", detail)
        else:
            detail = f"would prepend tag block ({len(new_content) - len(prompt_content)} chars)"
            if dry_run:
                result.stages["tags"] = StageStatus(status="dry_run", detail=detail)
                _stage_log_exit("tags", "dry_run", detail)
            else:
                _atomic_write(prompt_path, new_content)
                refreshed_prompt_content = new_content
                detail_written = f"wrote refreshed tags ({len(new_content)} chars)"
                result.stages["tags"] = StageStatus(status="ok", detail=detail_written)
                _stage_log_exit("tags", "ok", detail_written)
    except (KeyboardInterrupt, SystemExit):
        raise
    except Exception as exc:
        reason = str(exc)
        result.stages["tags"] = StageStatus(status="failed", reason=reason)
        _stage_log_exit("tags", "failed", reason)

    # ---- Stage 3: architecture ----
    _stage_log_enter("architecture")
    try:
        if architecture_path is None or not architecture_path.exists():
            reason = "no architecture.json found"
            result.stages["architecture"] = StageStatus(status="skipped", reason=reason)
            _stage_log_exit("architecture", "skipped", reason)
        else:
            arch_result = update_architecture_from_prompt(
                prompt_filename=prompt_path.name,
                prompts_dir=prompts_dir,
                architecture_path=architecture_path,
                dry_run=dry_run,
                prompt_content_override=refreshed_prompt_content,
            )
            if not arch_result.get("success", False):
                err = arch_result.get("error") or "architecture update failed"
                raise RuntimeError(err)
            updated = arch_result.get("updated", False)
            changes = arch_result.get("changes") or {}
            change_keys = list(changes.keys()) if isinstance(changes, dict) else []
            if dry_run:
                detail = (
                    f"would update fields: {change_keys}" if updated else "no changes"
                )
                result.stages["architecture"] = StageStatus(status="dry_run", detail=detail)
                _stage_log_exit("architecture", "dry_run", detail)
            else:
                detail = (
                    f"updated fields: {change_keys}" if updated else "no changes"
                )
                result.stages["architecture"] = StageStatus(status="ok", detail=detail)
                _stage_log_exit("architecture", "ok", detail)
    except (KeyboardInterrupt, SystemExit):
        raise
    except Exception as exc:
        reason = str(exc)
        result.stages["architecture"] = StageStatus(status="failed", reason=reason)
        _stage_log_exit("architecture", "failed", reason)

    # ---- Stage 4: run_report ----
    _stage_log_enter("run_report")
    try:
        basename, language = infer_module_identity(prompt_path)
        if not basename or not language:
            reason = "could not infer (basename, language) from prompt path"
            result.stages["run_report"] = StageStatus(status="skipped", reason=reason)
            _stage_log_exit("run_report", "skipped", reason)
        else:
            detail = f"basename={basename} language={language}"
            if dry_run:
                result.stages["run_report"] = StageStatus(
                    status="dry_run",
                    detail=f"would clear run report for {detail}",
                )
                _stage_log_exit("run_report", "dry_run", detail)
            else:
                clear_run_report(basename, language)
                result.stages["run_report"] = StageStatus(
                    status="ok", detail=f"cleared run report for {detail}"
                )
                _stage_log_exit("run_report", "ok", detail)
    except (KeyboardInterrupt, SystemExit):
        raise
    except Exception as exc:
        reason = str(exc)
        result.stages["run_report"] = StageStatus(status="failed", reason=reason)
        _stage_log_exit("run_report", "failed", reason)

    # ---- Stage 5: fingerprint (gated) ----
    _stage_log_enter("fingerprint")
    prior_failed = [
        name
        for name in ("prompt", "tags", "architecture", "run_report")
        if result.stages.get(name) and result.stages[name].status == "failed"
    ]
    if prior_failed:
        reason = f"earlier stage failed: {prior_failed[0]}"
        result.stages["fingerprint"] = StageStatus(status="skipped", reason=reason)
        _stage_log_exit("fingerprint", "skipped", reason)
        return result

    try:
        basename, language = infer_module_identity(prompt_path)
        if not basename or not language:
            reason = "could not infer (basename, language) for fingerprint"
            result.stages["fingerprint"] = StageStatus(status="skipped", reason=reason)
            _stage_log_exit("fingerprint", "skipped", reason)
        else:
            paths: Dict[str, Path] = {"prompt": prompt_path}
            if code_path is not None:
                paths["code"] = code_path
            detail = f"basename={basename} language={language}"
            if dry_run:
                result.stages["fingerprint"] = StageStatus(
                    status="dry_run",
                    detail=f"would finalize fingerprint for {detail}",
                )
                _stage_log_exit("fingerprint", "dry_run", detail)
            else:
                save_fingerprint(
                    basename=basename,
                    language=language,
                    operation="metadata_sync",
                    paths=paths,
                    cost=0.0,
                    model="metadata_sync",
                )
                result.stages["fingerprint"] = StageStatus(
                    status="ok", detail=f"saved fingerprint for {detail}"
                )
                _stage_log_exit("fingerprint", "ok", detail)
    except (KeyboardInterrupt, SystemExit):
        raise
    except Exception as exc:
        reason = str(exc)
        result.stages["fingerprint"] = StageStatus(status="failed", reason=reason)
        _stage_log_exit("fingerprint", "failed", reason)

    return result