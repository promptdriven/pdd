"""Resolved sync unit: one canonical identity per module for the sync pipeline.

Issue #1675: agentic sync used to recompute pieces of a module's identity (cwd,
context, target) independently in different stages, which let a child
``pdd sync`` run with a ``cwd`` and ``--context`` that came from different
``.pddrc`` files. A :class:`ResolvedSyncUnit` bundles the full identity so every
stage (dry-run, fingerprint filtering, the async/durable runners, child command
building, and reproduce-local diagnostics) consumes the same resolved values
instead of recomputing them.

The cwd is discovered by the caller (``agentic_sync._resolve_module_cwd`` /
``GlobalSyncModule.cwd``); :func:`resolve_sync_unit` turns a resolved cwd into a
full unit. This module imports only from ``construct_paths`` so it can be used by
both ``agentic_sync`` and ``agentic_sync_runner`` without an import cycle.
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Optional

from .construct_paths import (
    _detect_context_from_basename,
    _find_pddrc_file,
    _load_pddrc_config,
)


@dataclass(frozen=True)
class ResolvedSyncUnit:
    """One resolved identity for a module carried through the whole sync flow.

    Path fields (``prompts_dir``, ``architecture_path``,
    ``generate_output_path``, ``test_output_path``, ``meta_path``) are advisory:
    they describe where the child ``pdd sync`` — run in ``cwd`` with ``context``
    — is expected to read/write, for diagnostics and tests. The child computes
    its real paths from ``cwd`` + ``.pddrc``; the unit's job is to make ``cwd``,
    ``pddrc_path``, ``context`` and ``target_basename`` agree so those child
    paths land in the intended project.
    """

    key: str
    target_basename: str
    cwd: Path
    pddrc_path: Optional[Path]
    context: Optional[str]
    prompts_dir: Path
    architecture_path: Optional[Path] = None
    generate_output_path: Optional[Path] = None
    test_output_path: Optional[Path] = None
    meta_path: Optional[Path] = None

    def with_cwd(self, new_cwd: Path) -> "ResolvedSyncUnit":
        """Return a copy rebased onto ``new_cwd`` (e.g. a durable worktree).

        Advisory paths that were under the old cwd are recomputed relative to
        ``new_cwd`` so durable child syncs report worktree-relative locations.
        The context name is cwd-independent (the worktree checks out the same
        ``.pddrc``) and is preserved.
        """
        old_cwd = self.cwd
        new_cwd = Path(new_cwd)

        def _rebase(p: Optional[Path]) -> Optional[Path]:
            if p is None:
                return None
            try:
                return new_cwd / p.relative_to(old_cwd)
            except ValueError:
                return p

        return ResolvedSyncUnit(
            key=self.key,
            target_basename=self.target_basename,
            cwd=new_cwd,
            pddrc_path=_rebase(self.pddrc_path),
            context=self.context,
            prompts_dir=_rebase(self.prompts_dir) or self.prompts_dir,
            architecture_path=_rebase(self.architecture_path),
            generate_output_path=_rebase(self.generate_output_path),
            test_output_path=_rebase(self.test_output_path),
            meta_path=_rebase(self.meta_path),
        )


def _context_defaults(config: Dict[str, Any], context_name: Optional[str]) -> Dict[str, Any]:
    """Return the ``defaults`` block for ``context_name`` (or ``default``)."""
    contexts = config.get("contexts", {}) if isinstance(config, dict) else {}
    entry = contexts.get(context_name or "default", {})
    if not isinstance(entry, dict):
        return {}
    defaults = entry.get("defaults", {})
    return defaults if isinstance(defaults, dict) else {}


def _resolve_unit_context(
    target_basename: str,
    pddrc_path: Optional[Path],
    config: Dict[str, Any],
    requested_context: Optional[str],
) -> Optional[str]:
    """Resolve the ``--context`` for a module against its own cwd ``.pddrc``.

    Policy (issue #1675, with the maintainer's default-only-nested refinement):
      * No governing ``.pddrc`` (or unparseable) -> ``None`` (omit; nothing to
        scope a context against).
      * The requested/global context is defined here -> use it.
      * Otherwise, if this ``.pddrc`` assigns a specific (non-default) context to
        the target -> use that.
      * Otherwise -> ``None`` (omit). A nested project that only has a default
        context, or where the target maps to default, must let the child resolve
        its own default rather than fail because a parent context does not exist
        here.
    """
    if pddrc_path is None or not config:
        return None
    available = set((config.get("contexts") or {}).keys())
    if requested_context and requested_context in available:
        return requested_context
    try:
        specific = _detect_context_from_basename(
            target_basename, config, pddrc_path=pddrc_path
        )
    except Exception:
        specific = None
    if specific and specific in available:
        return specific
    return None


def _resolve_prompts_dir(
    cwd: Path,
    pddrc_path: Optional[Path],
    config: Dict[str, Any],
    context_name: Optional[str],
) -> Path:
    """Resolve the prompts_dir for the unit (relative to the .pddrc parent)."""
    if pddrc_path is None:
        return cwd / "prompts"
    raw = _context_defaults(config, context_name).get("prompts_dir", "prompts")
    candidate = Path(raw)
    return candidate if candidate.is_absolute() else pddrc_path.parent / raw


def _resolve_output_path(
    base_dir: Path,
    config: Dict[str, Any],
    context_name: Optional[str],
    key: str,
) -> Optional[Path]:
    """Resolve an advisory output dir for a context default key, else ``None``."""
    raw = _context_defaults(config, context_name).get(key)
    if not raw:
        return None
    candidate = Path(raw)
    return candidate if candidate.is_absolute() else base_dir / raw


def resolve_sync_unit(
    key: str,
    target_basename: str,
    cwd: Path,
    *,
    requested_context: Optional[str] = None,
    architecture_path: Optional[Path] = None,
) -> ResolvedSyncUnit:
    """Build a :class:`ResolvedSyncUnit` from an already-resolved ``cwd``.

    Non-throwing: a missing or malformed ``.pddrc`` yields ``context=None`` (the
    child surfaces any parse error itself) so one bad nested config cannot abort
    unit-building for every module.
    """
    cwd = Path(cwd)
    pddrc_path = _find_pddrc_file(cwd)
    config: Dict[str, Any] = {}
    if pddrc_path is not None:
        try:
            config = _load_pddrc_config(pddrc_path)
        except Exception:
            config = {}

    context = _resolve_unit_context(
        target_basename, pddrc_path, config, requested_context
    )
    prompts_dir = _resolve_prompts_dir(cwd, pddrc_path, config, context)
    base_dir = pddrc_path.parent if pddrc_path is not None else cwd
    return ResolvedSyncUnit(
        key=key,
        target_basename=target_basename,
        cwd=cwd,
        pddrc_path=pddrc_path,
        context=context,
        prompts_dir=prompts_dir,
        architecture_path=Path(architecture_path) if architecture_path else None,
        generate_output_path=_resolve_output_path(
            base_dir, config, context, "generate_output_path"
        ),
        test_output_path=_resolve_output_path(
            base_dir, config, context, "test_output_path"
        ),
        meta_path=cwd / ".pdd" / "meta",
    )
