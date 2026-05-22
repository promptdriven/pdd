"""Pure parser for ``/pdd ...`` slash commands posted as GitHub issue
comments on an active App run.

This module is I/O-free: it does not call GitHub APIs, verify webhook
signatures, render reply Markdown, or mutate any persistent state. The
webhook handler (in the private App repo) wires this to GitHub by calling
:func:`parse_comment`, applying the resulting action via the
``/commands/jobs/{job_id}/budget`` REST endpoints, and posting the rendered
reply via ``budget_comments``.

Per R5, authorisation gates ONLY budget-mutating verbs (``budget_*`` /
``stop``). The read-only ``/pdd settings`` verb is open to anyone whose
comment is parsed (subject to bot / fenced / dedupe filters). The webhook
handler is therefore expected to **parse first, then gate by ``kind``** —
never to gate all ``/pdd ...`` comments before parsing.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Optional, Set

from .budget_settings import validate_amount
from .models import SlashCommandResult


__all__ = ["CommentInput", "parse_comment", "is_authorized", "is_duplicate"]


_MUTATING_KINDS = {"budget_set", "budget_node_set", "budget_max_set", "stop"}
_READ_ONLY_KINDS = {"settings"}

_USAGE_HINT = (
    "Unrecognised /pdd command. Try: /pdd budget N, /pdd budget node N, "
    "/pdd budget max N, /pdd settings, /pdd stop."
)


@dataclass
class CommentInput:
    """Minimal view of an ``issue_comment.created`` payload the parser needs."""

    id: int
    body: str
    user_login: str
    user_type: str
    author_association: Optional[str] = None
    created_at: Optional[str] = None


def _first_non_fenced_line(body: str) -> Optional[str]:
    """Return the first non-fenced, non-blank line of ``body``, or ``None``.

    Fenced blocks are toggled by lines starting with triple backticks or
    triple tildes. Lines inside a fenced block are skipped, so a user
    pasting a ``/pdd ...`` example inside a fenced code block does not
    trigger.
    """
    in_fence = False
    fence_marker: Optional[str] = None
    for raw_line in body.splitlines():
        stripped = raw_line.lstrip()
        if in_fence:
            if fence_marker and stripped.startswith(fence_marker):
                in_fence = False
                fence_marker = None
            continue
        if stripped.startswith("```"):
            in_fence = True
            fence_marker = "```"
            continue
        if stripped.startswith("~~~"):
            in_fence = True
            fence_marker = "~~~"
            continue
        if not stripped:
            continue
        return stripped
    return None


def parse_comment(
    comment: CommentInput, *, active_command: Optional[str] = None
) -> SlashCommandResult:
    """Parse ``comment.body`` and return a :class:`SlashCommandResult`.

    See module docstring for the authorisation contract; this function does
    NOT enforce authorisation.
    """
    # R4: bot-authored comments are always ignored.
    if (comment.user_type or "").lower() == "bot":
        return SlashCommandResult(
            kind="ignored",
            message="",
            original_comment_id=comment.id,
            metadata={},
        )

    line = _first_non_fenced_line(comment.body or "")
    if not line or not line.startswith("/pdd"):
        return SlashCommandResult(
            kind="ignored",
            message="",
            original_comment_id=comment.id,
            metadata={},
        )

    tokens = line.split()
    if not tokens or tokens[0] != "/pdd":
        return SlashCommandResult(
            kind="ignored",
            message="",
            original_comment_id=comment.id,
            metadata={},
        )

    rest = tokens[1:]
    if not rest:
        return SlashCommandResult(
            kind="invalid",
            message=_USAGE_HINT,
            original_comment_id=comment.id,
            metadata={},
        )

    verb = rest[0].lower()
    args = rest[1:]

    if verb == "settings" and not args:
        return SlashCommandResult(
            kind="settings",
            message="",
            original_comment_id=comment.id,
            metadata={},
        )
    if verb == "stop" and not args:
        return SlashCommandResult(
            kind="stop",
            message="",
            original_comment_id=comment.id,
            metadata={},
        )
    if verb == "budget":
        return _parse_budget(args, active_command=active_command, comment_id=comment.id)

    return SlashCommandResult(
        kind="invalid",
        message=_USAGE_HINT,
        original_comment_id=comment.id,
        metadata={},
    )


def _parse_budget(
    args, *, active_command: Optional[str], comment_id: int
) -> SlashCommandResult:
    if not args:
        return SlashCommandResult(
            kind="invalid",
            message=_USAGE_HINT,
            original_comment_id=comment_id,
            metadata={},
        )

    # /pdd budget node N
    if args[0].lower() == "node":
        if len(args) != 2:
            return SlashCommandResult(
                kind="invalid",
                message=_USAGE_HINT,
                original_comment_id=comment_id,
                metadata={},
            )
        try:
            amount = validate_amount(args[1])
        except ValueError as exc:
            return SlashCommandResult(
                kind="invalid",
                message=f"{exc}\n{_USAGE_HINT}",
                original_comment_id=comment_id,
                metadata={},
            )
        return SlashCommandResult(
            kind="budget_node_set",
            message="",
            original_comment_id=comment_id,
            metadata={"amount": amount},
        )

    # /pdd budget max N
    if args[0].lower() == "max":
        if len(args) != 2:
            return SlashCommandResult(
                kind="invalid",
                message=_USAGE_HINT,
                original_comment_id=comment_id,
                metadata={},
            )
        try:
            amount = validate_amount(args[1])
        except ValueError as exc:
            return SlashCommandResult(
                kind="invalid",
                message=f"{exc}\n{_USAGE_HINT}",
                original_comment_id=comment_id,
                metadata={},
            )
        return SlashCommandResult(
            kind="budget_max_set",
            message="",
            original_comment_id=comment_id,
            metadata={"amount": amount},
        )

    # /pdd budget N
    if len(args) != 1:
        return SlashCommandResult(
            kind="invalid",
            message=_USAGE_HINT,
            original_comment_id=comment_id,
            metadata={},
        )
    try:
        amount = validate_amount(args[0])
    except ValueError as exc:
        return SlashCommandResult(
            kind="invalid",
            message=f"{exc}\n{_USAGE_HINT}",
            original_comment_id=comment_id,
            metadata={},
        )
    # R6: bare /pdd budget N on a pdd-issue job aliases to /pdd budget max N.
    if active_command == "issue":
        return SlashCommandResult(
            kind="budget_max_set",
            message="",
            original_comment_id=comment_id,
            metadata={"amount": amount},
        )
    return SlashCommandResult(
        kind="budget_set",
        message="",
        original_comment_id=comment_id,
        metadata={"amount": amount},
    )


def is_authorized(
    commenter_login: str,
    *,
    issue_author_login: Optional[str] = None,
    repo_collaborators: Optional[Iterable[str]] = None,
    commenter_association: Optional[str] = None,
) -> bool:
    """Return ``True`` when ``commenter_login`` is allowed to mutate budgets.

    The caller must apply this AFTER parsing, scoped to budget-mutating
    kinds; ``/pdd settings`` is open to all and must not be gated.
    """
    if issue_author_login and commenter_login == issue_author_login:
        return True
    if repo_collaborators and commenter_login in set(repo_collaborators):
        return True
    if commenter_association and commenter_association.upper() in {
        "OWNER",
        "MEMBER",
        "COLLABORATOR",
    }:
        return True
    return False


def is_duplicate(comment_id: int, *, seen: Set[int]) -> bool:
    """Return ``True`` iff ``comment_id`` is already in ``seen``; else add it."""
    if comment_id in seen:
        return True
    seen.add(comment_id)
    return False
