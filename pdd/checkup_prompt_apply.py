"""Deterministic apply path for interactive prompt repair ``ApprovedPatch`` objects."""

from __future__ import annotations

import json
import os
import shutil
import tempfile
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping, Sequence

from .checkup_interactive_session import ApprovedPatch
from .checkup_prompt_main import run_checkup_prompt

ALLOWED_PATCH_KINDS = frozenset(
    {
        "vocab_definition",
        "contract_rule",
        "coverage_line",
        "waiver",
        "story_template",
        "append_covers",
    }
)

_FORBIDDEN_REL_PREFIXES = (
    "tests/",
    "pdd/",
    "dist/",
    ".git/",
    "context/",
)


@dataclass
class ApplyFindingRecord:
    """One row in the interactive apply log."""

    id: str
    choice: int
    patch_kind: str
    target_path: str
    status: str
    reason: str = ""

    def as_dict(self) -> dict[str, Any]:
        payload = {
            "id": self.id,
            "choice": self.choice,
            "patch_kind": self.patch_kind,
            "target_path": self.target_path,
            "status": self.status,
        }
        if self.reason:
            payload["reason"] = self.reason
        return payload


@dataclass
class ApplyRunResult:
    """Outcome of one interactive apply run."""

    run_id: str
    findings: list[ApplyFindingRecord] = field(default_factory=list)
    postflight_status: str = "pass"
    exit_code: int = 0
    log_path: Path | None = None
    backup_root: Path | None = None


def _new_run_id() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S-%fZ")


def _relative_posix_path(path: Path, repo_root: Path) -> str:
    return path.resolve().relative_to(repo_root.resolve()).as_posix()


def _is_writable_relative_path(rel: Path) -> bool:
    if rel.suffix.lower() == ".prompt" and not rel.name.lower().endswith("_llm.prompt"):
        return True
    if (
        len(rel.parts) >= 2
        and rel.parts[0] == "user_stories"
        and rel.name.startswith("story__")
        and rel.suffix.lower() == ".md"
    ):
        return True
    return False


def _validate_patch(patch: ApprovedPatch, repo_root: Path) -> Path:
    """Validate patch kind and target path; return the resolved writable path."""
    if patch.kind not in ALLOWED_PATCH_KINDS:
        raise ValueError(f"patch kind {patch.kind!r} is not allowlisted")

    target = Path(patch.target)
    if target.is_absolute():
        raise ValueError("absolute patch targets are not allowed")

    repo_root = repo_root.resolve()
    resolved = (repo_root / target).resolve()
    try:
        rel = resolved.relative_to(repo_root)
    except ValueError as exc:
        raise ValueError("patch target escapes repository root") from exc

    rel_posix = rel.as_posix()
    if ".." in rel.parts:
        raise ValueError("path traversal is not allowed")

    for prefix in _FORBIDDEN_REL_PREFIXES:
        if (
            prefix == "pdd/"
            and rel.parts[:2] == ("pdd", "prompts")
            and rel.suffix.lower() == ".prompt"
        ):
            continue
        if rel_posix == prefix.rstrip("/") or rel_posix.startswith(prefix):
            raise ValueError(f"patch target {rel_posix!r} is not writable")

    if not _is_writable_relative_path(rel):
        raise ValueError(
            "patch target must be a .prompt file (excluding *_LLM.prompt) "
            "or user_stories/story__*.md"
        )

    if not resolved.is_file():
        raise ValueError(f"patch target does not exist: {rel_posix}")

    return resolved


def _apply_patch_content(path: Path, patch: ApprovedPatch) -> str:
    """Return updated file contents for one validated patch."""
    original = path.read_text(encoding="utf-8")
    if patch.kind == "append_covers":
        suffix = "" if original.endswith("\n") or not original else "\n"
        replacement = patch.replacement
        if replacement and not replacement.endswith("\n"):
            replacement += "\n"
        return original + suffix + replacement

    lines = original.splitlines(keepends=True)
    replacement = patch.replacement
    if replacement and not replacement.endswith("\n"):
        replacement += "\n"

    anchor_line = patch.anchor.get("line")
    insert_at = len(lines)
    if anchor_line not in (None, ""):
        try:
            insert_at = max(0, int(anchor_line) - 1)
        except (TypeError, ValueError):
            insert_at = len(lines)

    if 0 <= insert_at <= len(lines):
        lines.insert(insert_at, replacement)
    else:
        lines.append(replacement)
    return "".join(lines)


def _atomic_write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        dir=path.parent,
        delete=False,
    ) as handle:
        handle.write(content)
        temp_path = Path(handle.name)
    os.replace(temp_path, path)


def _backup_file(path: Path, repo_root: Path, run_id: str) -> Path:
    rel = path.resolve().relative_to(repo_root.resolve())
    backup_root = repo_root / ".pdd" / "evidence" / "checkups" / "backups" / run_id
    dest = backup_root / rel
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(path, dest)
    return dest


def _write_apply_log(
    repo_root: Path,
    *,
    run_id: str,
    interactive: bool,
    dry_run: bool,
    findings: Sequence[ApplyFindingRecord],
    postflight_status: str,
) -> Path:
    evidence_dir = repo_root / ".pdd" / "evidence" / "checkups"
    evidence_dir.mkdir(parents=True, exist_ok=True)
    log_path = evidence_dir / f"apply-{run_id}.json"
    payload = {
        "run_id": run_id,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "interactive": interactive,
        "dry_run": dry_run,
        "findings": [record.as_dict() for record in findings],
        "postflight_status": postflight_status,
    }
    log_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return log_path


def apply_approved_patches(
    patches: Sequence[ApprovedPatch],
    *,
    repo_root: Path,
    original_target: str,
    dry_run: bool = False,
    interactive: bool = True,
    strict: bool = False,
    choices_by_finding: Mapping[str, int] | None = None,
) -> ApplyRunResult:
    """Validate, backup, atomically apply patches, log, and postflight check."""
    run_id = _new_run_id()
    repo_root = repo_root.resolve()
    choices = dict(choices_by_finding or {})
    records: list[ApplyFindingRecord] = []
    backup_root: Path | None = None
    applied_any = False
    rejected_any = False

    for patch in patches:
        finding_id = patch.finding_id or str(patch.anchor.get("finding_id", ""))
        choice = choices.get(finding_id, 0)
        try:
            target_path = _validate_patch(patch, repo_root)
            rel_target = _relative_posix_path(target_path, repo_root)
        except ValueError as exc:
            rejected_any = True
            records.append(
                ApplyFindingRecord(
                    id=finding_id,
                    choice=choice,
                    patch_kind=patch.kind,
                    target_path=str(patch.target),
                    status="rejected",
                    reason=str(exc),
                )
            )
            continue

        if dry_run:
            records.append(
                ApplyFindingRecord(
                    id=finding_id,
                    choice=choice,
                    patch_kind=patch.kind,
                    target_path=rel_target,
                    status="accepted",
                )
            )
            continue

        if backup_root is None:
            backup_root = repo_root / ".pdd" / "evidence" / "checkups" / "backups" / run_id
        _backup_file(target_path, repo_root, run_id)
        new_content = _apply_patch_content(target_path, patch)
        _atomic_write(target_path, new_content)
        applied_any = True
        records.append(
            ApplyFindingRecord(
                id=finding_id,
                choice=choice,
                patch_kind=patch.kind,
                target_path=rel_target,
                status="accepted",
            )
        )

    postflight_status = "pass"
    exit_code = 0
    if rejected_any:
        postflight_status = "rejected"
        exit_code = 2
    if not dry_run and applied_any:
        try:
            passed, _message, _cost, _model, exit_code = run_checkup_prompt(
                original_target,
                quiet=True,
                strict=strict,
                project_root=repo_root,
            )
            if exit_code == 0 and passed:
                postflight_status = "pass"
            elif exit_code == 0:
                postflight_status = "warn"
            else:
                postflight_status = "fail"
        except Exception:  # pylint: disable=broad-except
            postflight_status = "error"
            exit_code = 2
        if rejected_any and postflight_status == "pass":
            postflight_status = "rejected"
            exit_code = 2

    log_path: Path | None = None
    if interactive and (records or dry_run):
        log_path = _write_apply_log(
            repo_root,
            run_id=run_id,
            interactive=interactive,
            dry_run=dry_run,
            findings=records,
            postflight_status=postflight_status,
        )

    return ApplyRunResult(
        run_id=run_id,
        findings=records,
        postflight_status=postflight_status,
        exit_code=exit_code,
        log_path=log_path,
        backup_root=backup_root,
    )
