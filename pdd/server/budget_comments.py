"""Pure Markdown renderers for the GitHub App's budget-control replies.

These functions are I/O-free: they take a :class:`BudgetSettings` snapshot
and return a string. Posting to GitHub, network I/O, and persistence live in
the App / webhook handler, not here.
"""

from __future__ import annotations

from typing import Optional

from .models import BudgetSettings


__all__ = [
    "render_startup",
    "render_settings",
    "render_ack",
    "render_stop",
    "render_invalid",
    "render_unauthorized",
    "render_budget_exceeded",
]


_USAGE_BLOCK = (
    "/pdd budget N\n"
    "/pdd budget node N\n"
    "/pdd budget max N\n"
    "/pdd settings\n"
    "/pdd stop"
)


def _money(value: float) -> str:
    """Format a cap-like USD amount per R10: ``$<int>`` when integer, else
    ``$<value:.2f>``.
    """
    v = float(value)
    if v.is_integer():
        return f"${int(v)}"
    return f"${v:.2f}"


def _spent_money(value: float) -> str:
    """Format spent-so-far values per R10: always two decimals."""
    return f"${float(value):.2f}"


def render_startup(settings: BudgetSettings) -> str:
    """Render the startup comment for a new GitHub App run.

    For ``pdd-issue`` (``settings.command == "issue"``), shows the per-node
    and max-total budget with the ``effective cap: min($N x node count, $M)``
    formula. For every other command, shows ``Budget cap: $N`` (or ``none``)
    plus the example block from the issue acceptance criteria.
    """
    if settings.command == "issue":
        node = (
            _money(settings.node_budget) if settings.node_budget is not None else "none"
        )
        max_total = (
            _money(settings.max_total_cap)
            if settings.max_total_cap is not None
            else "none"
        )
        effective = (
            f"min({node} x node count, {max_total})"
            if settings.node_budget is not None and settings.max_total_cap is not None
            else (
                _money(settings.effective_cap)
                if settings.effective_cap is not None
                else "none"
            )
        )
        return (
            "PDD is starting autonomous solving.\n\n"
            "Budget:\n"
            f"- node budget: {node} per node\n"
            f"- max total cap: {max_total}\n"
            f"- effective cap: {effective}\n\n"
            "You can change this run by commenting:\n"
            "/pdd budget node 50\n"
            "/pdd budget max 200"
        )
    cap_line = (
        f"Budget cap: {_money(settings.budget_cap)}"
        if settings.budget_cap is not None
        else "Budget cap: none"
    )
    return (
        f"PDD is starting `pdd {settings.command}`.\n\n"
        f"{cap_line}\n\n"
        "You can add a cap by commenting:\n"
        "/pdd budget 30\n\n"
        "Other controls:\n"
        "/pdd settings\n"
        "/pdd stop"
    )


def render_settings(settings: BudgetSettings) -> str:
    """Read-only ``Current PDD settings:`` block.

    Includes ``Command``, ``Node budget`` (only for ``pdd-issue``),
    ``Max total cap``, ``Effective cap``, ``Spent so far`` (two decimals), and
    ``Status``. Wording matches the issue's example.
    """
    lines = ["Current PDD settings:", f"- Command: pdd-{settings.command}"]
    if settings.command == "issue":
        node = (
            _money(settings.node_budget) if settings.node_budget is not None else "none"
        )
        lines.append(f"- Node budget: {node}")
        max_total = (
            _money(settings.max_total_cap)
            if settings.max_total_cap is not None
            else "none"
        )
        lines.append(f"- Max total cap: {max_total}")
        if settings.node_budget is not None and settings.max_total_cap is not None:
            lines.append(
                f"- Effective cap: min({_money(settings.node_budget)} x node count, "
                f"{_money(settings.max_total_cap)})"
            )
        elif settings.effective_cap is not None:
            lines.append(f"- Effective cap: {_money(settings.effective_cap)}")
        else:
            lines.append("- Effective cap: none")
    else:
        cap = (
            _money(settings.budget_cap) if settings.budget_cap is not None else "none"
        )
        lines.append(f"- Budget cap: {cap}")
        if settings.effective_cap is not None:
            lines.append(f"- Effective cap: {_money(settings.effective_cap)}")
        else:
            lines.append("- Effective cap: none")
    lines.append(f"- Spent so far: {_spent_money(settings.spent_so_far)}")
    lines.append(f"- Status: {settings.status.value}")
    return "\n".join(lines)


def render_ack(kind: str, *, amount: float, settings: BudgetSettings) -> str:
    """Render the one-line acknowledgement plus a settings echo."""
    head = {
        "budget_set": f"Updated budget cap to {_money(amount)}.",
        "budget_node_set": f"Updated node budget to {_money(amount)}.",
        "budget_max_set": f"Updated max total cap to {_money(amount)}.",
    }.get(kind)
    if head is None:
        raise ValueError(f"render_ack: unknown ack kind {kind!r}")
    return f"{head}\n\n{render_settings(settings)}"


def render_stop(settings: BudgetSettings) -> str:
    """One-line summary of final spend plus a brief status line."""
    return (
        f"PDD stopped. Final spend: {_spent_money(settings.spent_so_far)}\n"
        f"Status: {settings.status.value}"
    )


def render_invalid(reason: Optional[str] = None) -> str:
    """Single helpful line followed by the usage block listing all five verbs."""
    intro = reason.strip() if reason else "Unrecognised /pdd command."
    return f"{intro}\n\nUsage:\n{_USAGE_BLOCK}"


def render_unauthorized(commenter_login: str) -> str:
    """One-line message: only authors/collaborators may CHANGE budgets or
    stop the run; refer the user to ``/pdd settings`` for a read-only view.

    Per ``slash_command_parser_python.prompt`` R5, only invoked for
    budget-mutating verbs (``budget_*`` / ``stop``) — never for
    ``/pdd settings``.
    """
    return (
        f"@{commenter_login}: only the issue author and repo collaborators may "
        "change budgets or stop the run. You can still use `/pdd settings` for "
        "a read-only view."
    )


def render_budget_exceeded(settings: BudgetSettings) -> str:
    """Final ``budget_exceeded`` status comment posted when the watcher fires."""
    cap_str = (
        _money(settings.effective_cap)
        if settings.effective_cap is not None
        else "none"
    )
    return (
        "PDD stopped: budget exceeded.\n"
        f"- Spent: {_spent_money(settings.spent_so_far)}\n"
        f"- Effective cap: {cap_str}\n"
        "- Status: budget_exceeded"
    )
