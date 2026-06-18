"""Consistent status & progress messaging for the PDD CLI.

Single source of truth for *what the tool is doing right now*. Commands route
their human-facing progress through a small, fixed set of message primitives so
that — across every command — the user can always tell:

1. what is happening now              -> :meth:`StatusReporter.start` / ``step``
2. what step comes next               -> ``next_step=`` on ``start`` / ``success``
3. whether it is waiting on IO/LLM     -> :meth:`StatusReporter.waiting`
4. what succeeded or failed, and what  -> :meth:`StatusReporter.success` /
   to do about it                         :meth:`StatusReporter.failure`

Design rules (kept deliberately small so commands stay consistent):

* Five primitives only — ``START`` / ``STEP`` / ``WAITING`` / ``SUCCESS`` /
  ``FAILURE``. Each has one glyph and one semantic color role, so the same kind
  of event looks the same everywhere.
* Messages are short, skimmable, and action-oriented (say what is being done).
* Output is *non-duplicative*: an identical line emitted twice in a row is
  collapsed, so retries/loops do not spam the terminal.
* Color comes from the central :mod:`pdd.cli_theme` palette (EPIC #1540,
  workstream 1) — this module never picks raw colors.
* Machine-readable output is protected: in ``quiet`` mode nothing is printed,
  and in ``json_mode`` status goes to **stderr** so stdout stays payload-only.

The reporter also *records* every message it emits (:attr:`StatusReporter.messages`)
so tests can assert on message *shape* deterministically — no wall-clock, no
spinner-frame, no captured-ANSI assertions.
"""

from __future__ import annotations

import enum
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Iterator, List, Optional, Sequence, Tuple

from rich.console import Console

from .cli_theme import get_console

__all__ = [
    "Status",
    "StatusMessage",
    "StatusReporter",
    "from_context",
    "GLYPHS",
    "ROLES",
]


class Status(enum.Enum):
    """The five message primitives every command shares."""

    START = "start"          # a command/operation is beginning
    STEP = "step"            # the current human-readable step within it
    WAITING = "waiting"      # blocked on IO / network / LLM (slow, show progress)
    SUCCESS = "success"      # finished, with an optional next action
    FAILURE = "failure"      # failed, with cause + what to try next


# One glyph per primitive — the visual shorthand stays identical across commands.
GLYPHS = {
    Status.START: "▶",
    Status.STEP: "→",
    Status.WAITING: "…",
    Status.SUCCESS: "✓",
    Status.FAILURE: "✗",
}

# Map each primitive to a *semantic role* from the central theme (pdd/cli_theme.py)
# rather than a raw color, so status coloring tracks the brand palette.
ROLES = {
    Status.START: "command.strong",
    Status.STEP: "info",
    Status.WAITING: "muted",
    Status.SUCCESS: "success.strong",
    Status.FAILURE: "error",
}


def _escape(text: str) -> str:
    """Escape Rich markup so user/content text can't smuggle in styling."""
    return text.replace("[", r"\[")


@dataclass(frozen=True)
class StatusMessage:
    """A single status event, recorded so behavior is testable by *shape*.

    ``text`` is the plain headline (no markup). The optional fields carry the
    structured extras the UX criteria require: what it's waiting on, the next
    action on success, and — on failure — the root cause and concrete fixes.
    """

    status: Status
    text: str
    next_step: Optional[str] = None
    waiting_on: Optional[str] = None
    reason: Optional[str] = None
    suggestions: Tuple[str, ...] = ()
    command: Optional[str] = None

    @property
    def glyph(self) -> str:
        """The one glyph for this message's primitive (from :data:`GLYPHS`)."""
        return GLYPHS[self.status]

    @property
    def role(self) -> str:
        """The semantic theme role for this primitive (from :data:`ROLES`)."""
        return ROLES[self.status]

    def render_plain(self) -> str:
        """Markup-free rendering — used for logs, ``--quiet`` recall, and tests."""
        lines = [f"{self.glyph} {self._headline()}"]
        if self.waiting_on:
            lines[0] += f" (waiting on {self.waiting_on})"
        if self.reason:
            lines.append(f"  Why: {self.reason}")
        for hint in self.suggestions:
            lines.append(f"  Try: {hint}")
        if self.next_step:
            lines.append(f"  Next: {self.next_step}")
        return "\n".join(lines)

    def render_markup(self) -> str:
        """Rich-markup rendering, themed by semantic role from cli_theme."""
        role = self.role
        head = f"[{role}]{self.glyph} {_escape(self._headline())}[/{role}]"
        if self.waiting_on:
            head += f" [muted](waiting on {_escape(self.waiting_on)})[/muted]"
        lines = [head]
        if self.reason:
            lines.append(f"  [muted]Why:[/muted] {_escape(self.reason)}")
        for hint in self.suggestions:
            lines.append(f"  [warning]Try:[/warning] {_escape(hint)}")
        if self.next_step:
            lines.append(f"  [tag]Next:[/tag] {_escape(self.next_step)}")
        return "\n".join(lines)

    def _headline(self) -> str:
        if self.command and self.status is Status.START:
            return f"{self.command}: {self.text}"
        return self.text


class StatusReporter:
    """Emit consistent status messages for a single command run.

    Parameters
    ----------
    command:
        Human label for the command (e.g. ``"pdd detect"``), shown on ``start``.
    console:
        Optional Rich console. Defaults to a themed console from
        :func:`pdd.cli_theme.get_console`; when ``json_mode`` is set the default
        routes to **stderr** so machine-readable stdout is never polluted.
    quiet:
        When true, suppress all terminal output (messages are still recorded).
    json_mode:
        When true, the command emits machine-readable JSON on stdout; status is
        sent to stderr instead of being dropped, so humans still get feedback.
    """

    GLYPH_SPINNER = GLYPHS[Status.WAITING]

    def __init__(
        self,
        command: Optional[str] = None,
        *,
        console: Optional[Console] = None,
        quiet: bool = False,
        json_mode: bool = False,
    ) -> None:
        self.command = command
        self.quiet = quiet
        self.json_mode = json_mode
        if console is None:
            console = get_console(stderr=json_mode)
        self.console = console
        self.messages: List[StatusMessage] = []
        self._last_plain: Optional[str] = None

    # -- emission --------------------------------------------------------
    def emit(self, message: StatusMessage) -> StatusMessage:
        """Record ``message`` and print it unless suppressed or duplicative."""
        self.messages.append(message)
        plain = message.render_plain()
        # Non-duplicative: collapse an identical line emitted twice in a row so
        # retry loops and re-entrant steps don't spam the terminal.
        if plain == self._last_plain:
            return message
        self._last_plain = plain
        if not self.quiet:
            self.console.print(message.render_markup())
        return message

    def start(self, text: str, *, next_step: Optional[str] = None) -> StatusMessage:
        """Announce that the command/operation is beginning."""
        return self.emit(
            StatusMessage(
                Status.START, text, command=self.command, next_step=next_step
            )
        )

    def step(self, text: str) -> StatusMessage:
        """Announce the current human-readable step."""
        return self.emit(StatusMessage(Status.STEP, text))

    def success(self, text: str, *, next_step: Optional[str] = None) -> StatusMessage:
        """Report completion, with an optional next action for the user."""
        return self.emit(StatusMessage(Status.SUCCESS, text, next_step=next_step))

    def failure(
        self,
        text: str,
        *,
        reason: Optional[str] = None,
        suggestions: Sequence[str] = (),
    ) -> StatusMessage:
        """Report a failure with cause and 1-2 concrete things to try next.

        ``text`` names *what* failed (the step); ``reason`` is the root cause if
        known; ``suggestions`` are concrete next actions.
        """
        return self.emit(
            StatusMessage(
                Status.FAILURE,
                text,
                reason=reason,
                suggestions=tuple(suggestions),
            )
        )

    @contextmanager
    def waiting(self, text: str, *, on: str = "LLM") -> Iterator[StatusMessage]:
        """Show a live progress indicator while blocked on slow work.

        Use around IO/network/LLM calls so long operations never look frozen.
        Records a ``WAITING`` message (so the wait is testable) and, on an
        interactive terminal, shows a spinner for the duration. The spinner is
        automatically inert when output is suppressed, redirected, or not a TTY,
        which keeps tests free of timing- and animation-based flakiness.

        ``on`` names what is being awaited — ``"LLM"``, ``"network"``, ``"disk"``.
        """
        message = self.emit(StatusMessage(Status.WAITING, text, waiting_on=on))
        show_spinner = not self.quiet and self.console.is_terminal
        if show_spinner:
            with self.console.status(
                f"[muted]{self.GLYPH_SPINNER} {_escape(text)} (waiting on {_escape(on)})[/muted]"
            ):
                yield message
        else:
            yield message


def from_context(ctx, command: Optional[str] = None) -> StatusReporter:
    """Build a :class:`StatusReporter` from a Click context.

    Reads ``quiet`` from ``ctx.obj`` so commands inherit the global ``--quiet``
    flag without re-plumbing it. ``json_mode`` is left to the caller, since which
    invocations are machine-readable is command-specific (see
    :mod:`pdd.json_invocation`).
    """
    obj = getattr(ctx, "obj", None) or {}
    return StatusReporter(command, quiet=bool(obj.get("quiet", False)))
