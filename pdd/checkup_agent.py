"""LLM-agentic checkup session orchestration for ``pdd checkup --interactive``.

``CheckupAgent`` wraps the deterministic ``build_prompt_source_set_report``
pipeline with a planning layer (``Planner``) and an event/session layer
(``CheckupSession``) that surfaces tool results and per-finding choices to
the operator.

Flow
----
1. Planner suggests which tools to run and in what order.
2. Agent asks the operator to confirm / modify the plan (if interactive).
3. ``build_prompt_source_set_report`` runs all checks in one pass.
4. For each tool in the confirmed plan, the agent presents its findings via
   the existing ``ClickInteractiveSession`` / ``FakeInteractiveSession`` protocol.
5. Approved patches are optionally applied.

Modes
-----
interactive (default)
    Per-finding menu; operator chooses repair option, custom fix, or skip.
    During the session the operator can type ``a`` to switch to auto mode for
    all remaining findings.

auto
    Agent automatically picks the primary repair option for each finding and
    prints a summary.  No per-finding prompts.  Triggered by ``--auto`` or by
    typing ``a`` in interactive mode.

This module is intentionally free of direct LLM calls — those live in
``checkup_planner.LLMPlanner``.  Tests can inject a ``DeterministicPlanner``
and a ``RecordingCheckupSession`` to run end-to-end without network access.
"""

from __future__ import annotations

import logging
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Optional, Union

import click

from .checkup_interactive_main import (
    ClickInteractiveSession,
    apply_approved_patches,
    build_repair_options_for_finding,
    filter_interactive_findings,
    _prompt_menu_choice,
    _skip_option,
    _custom_option,
    _register_dynamic_option,
)
from .checkup_interactive_session import (
    ApprovedPatch,
    InteractiveRepairSession,
    RepairOption,
)
from .checkup_planner import DeterministicPlanner, Plan
from .checkup_prompt_main import (
    PromptSourceSetReport,
    SourceSetFinding,
    build_prompt_source_set_report,
)
from .checkup_tools import ALL_TOOLS, ToolResult

logger = logging.getLogger(__name__)

_SessionType = Union[InteractiveRepairSession, ClickInteractiveSession]


# ---------------------------------------------------------------------------
# Session event model
# ---------------------------------------------------------------------------


@dataclass
class AgentEvent:
    """One event emitted by ``CheckupAgent`` during a session."""

    kind: str
    """
    Possible kinds:
      plan_ready      — planner produced a plan
      plan_confirmed  — operator accepted or modified the plan
      tool_start      — about to present findings for one tool
      tool_done       — presented all findings for one tool
      session_done    — all tools processed; patches collected
    """
    data: dict = field(default_factory=dict)


class CheckupSession:
    """Base class / null implementation for a checkup event session."""

    def on_event(self, event: AgentEvent) -> None:  # noqa: B027
        pass

    def confirm_plan(self, plan: Plan) -> Optional[Plan]:
        """Return the confirmed plan (possibly modified), or None to abort."""
        return plan


class TerminalCheckupSession(CheckupSession):
    """Prints plan/tool events to the terminal and lets operators confirm the plan."""

    def __init__(self, *, quiet: bool = False) -> None:
        self.quiet = quiet
        self.events: list[AgentEvent] = []

    def on_event(self, event: AgentEvent) -> None:
        self.events.append(event)
        if self.quiet:
            return

        kind = event.kind
        data = event.data

        if kind == "plan_ready":
            click.echo("\nStarting agentic checkup session")
            click.echo(f"Target: {data.get('target', '')}")
            click.echo(f"Available tools: {', '.join(data.get('available_tools', []))}")
            click.echo("\nSuggested plan:")
            for line in data.get("plan_lines", []):
                click.echo(line)

        elif kind == "plan_confirmed":
            click.echo(f"\nPlan confirmed: {', '.join(data.get('tools', []))}")

        elif kind == "tool_start":
            click.echo(f"\n--- Checking: {data.get('tool', '')} ---")

        elif kind == "tool_done":
            tool = data.get("tool", "")
            status = data.get("status", "")
            n = data.get("finding_count", 0)
            click.echo(f"  {tool}: {status} ({n} finding(s))")

        elif kind == "mode_switch":
            click.echo(f"\n  [mode] Switched to {data.get('to', '?')} mode.")

        elif kind == "session_done":
            total = data.get("total_findings", 0)
            patches = data.get("patch_count", 0)
            auto = data.get("auto_applied", 0)
            auto_part = f", {auto} auto-applied" if auto else ""
            click.echo(
                f"\nAgentic checkup complete. {total} finding(s), "
                f"{patches} patch(es) queued{auto_part}."
            )

    def confirm_plan(self, plan: Plan) -> Optional[Plan]:
        click.echo("\nProceed with suggested plan? [Y/n/custom]")
        answer = click.prompt("", default="Y", show_default=False).strip().lower()
        if answer in ("n", "no"):
            return None
        if answer in ("", "y", "yes"):
            return plan
        # custom: let operator type tool names comma-separated
        raw = click.prompt("Enter tool names (comma-separated)", default=", ".join(plan.tools))
        custom_tools = [t.strip() for t in raw.split(",") if t.strip()]
        from .checkup_tools import ALL_TOOL_NAMES  # pylint: disable=import-outside-toplevel
        valid = [t for t in custom_tools if t in ALL_TOOL_NAMES]
        if not valid:
            click.echo("No valid tools selected. Aborting.", err=True)
            return None
        return Plan(tools=valid, rationale="Custom tool selection by operator.")


class RecordingCheckupSession(CheckupSession):
    """Test double: records all events and auto-confirms plans."""

    def __init__(self, *, confirm: bool = True, custom_plan: Optional[Plan] = None) -> None:
        self._confirm = confirm
        self._custom_plan = custom_plan
        self.events: list[AgentEvent] = []

    def on_event(self, event: AgentEvent) -> None:
        self.events.append(event)

    def confirm_plan(self, plan: Plan) -> Optional[Plan]:
        if not self._confirm:
            return None
        return self._custom_plan if self._custom_plan is not None else plan

    def events_of_kind(self, kind: str) -> list[AgentEvent]:
        return [e for e in self.events if e.kind == kind]


# ---------------------------------------------------------------------------
# Agent menu (extends the standard interactive menu with [a] auto shortcut)
# ---------------------------------------------------------------------------


def _prompt_agent_menu_choice(
    finding: SourceSetFinding,
    options: list[RepairOption],
) -> int:
    """Per-finding menu for the agentic session.

    Returns 1–4 (same as ``_prompt_menu_choice``) or 5 meaning "switch to auto."
    """
    click.echo(f"\n[{finding.finding_id}] {finding.message}")
    if finding.evidence:
        from .checkup_interactive_main import _truncate_excerpt  # pylint: disable=import-outside-toplevel

        click.echo(f"  {_truncate_excerpt(finding.evidence)}")

    label_a = options[0].label if options else "Option A"
    preview_a = options[0].preview if options else "(unavailable)"
    label_b = options[1].label if len(options) > 1 else "Option B"
    preview_b = options[1].preview if len(options) > 1 else "(unavailable)"

    click.echo("\nChoose one:")
    click.echo(f"[1] {label_a} — {preview_a}")
    click.echo(f"[2] {label_b} — {preview_b}")
    click.echo("[3] Write my own definition")
    click.echo("[4] Skip")
    click.echo("[a] Switch to auto mode (apply best option for all remaining)")

    raw = click.prompt("Choice", default="4", show_default=False).strip().lower()
    if raw == "a":
        return 5
    try:
        val = int(raw)
        if 1 <= val <= 4:
            return val
    except ValueError:
        pass
    return 4  # default: skip


# ---------------------------------------------------------------------------
# Agent
# ---------------------------------------------------------------------------


class CheckupAgent:
    """Orchestrates a planning → report → interactive-repair cycle.

    Parameters
    ----------
    planner:
        A ``DeterministicPlanner`` or ``LLMPlanner`` that suggests which tools
        to run and in what order.
    session:
        A ``CheckupSession`` that receives events and confirms the plan.
    repair_session_factory:
        Optional factory producing an ``InteractiveRepairSession`` for per-finding
        menus.  Defaults to ``ClickInteractiveSession`` when ``None`` and the
        ``interactive`` flag is set.
    """

    def __init__(
        self,
        planner: DeterministicPlanner,
        session: CheckupSession,
        *,
        repair_session_factory: Optional[Callable[[], _SessionType]] = None,
    ) -> None:
        self.planner = planner
        self.session = session
        self.repair_session_factory = repair_session_factory

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def run(
        self,
        target: str,
        *,
        project_root: Optional[Path] = None,
        strict: bool = False,
        apply: bool = False,
        dry_run: bool = False,
        quiet: bool = False,
        explicit_interactive: bool = True,
        auto: bool = False,
    ) -> tuple[str, float, str]:
        """Run the full agentic checkup cycle.

        Returns the same ``(message, cost, model)`` tuple as
        ``run_interactive_checkup`` so it can be used as a drop-in replacement
        in ``commands/checkup.py``.
        """
        root = project_root if project_root is not None else Path.cwd()
        prompt_path = Path(target)
        if not prompt_path.is_absolute():
            prompt_path = root / target
        if not prompt_path.is_file():
            raise click.UsageError(
                f"--interactive requires a single .prompt file target, got {target!r}."
            )

        prompt_text = prompt_path.read_text(encoding="utf-8")
        available_tools = list(ALL_TOOLS)

        # 1. Plan
        plan = self.planner.suggest(prompt_path, available_tools, prompt_text)
        self.session.on_event(
            AgentEvent(
                kind="plan_ready",
                data={
                    "target": target,
                    "available_tools": available_tools,
                    "plan_lines": plan.display_lines(),
                    "tools": plan.tools,
                    "rationale": plan.rationale,
                },
            )
        )

        # 2. Confirm plan
        confirmed_plan = self.session.confirm_plan(plan)
        if confirmed_plan is None:
            msg = "Agentic checkup aborted by operator."
            if not quiet:
                click.echo(msg)
            return msg, 0.0, ""

        self.session.on_event(
            AgentEvent(kind="plan_confirmed", data={"tools": confirmed_plan.tools})
        )

        # 3. Run report (all checks in one pass)
        report = build_prompt_source_set_report(
            prompt_path,
            target=target,
            project_root=root,
            strict=strict,
        )

        # 4. Process each tool in confirmed order
        repair_session: _SessionType
        if self.repair_session_factory is not None:
            repair_session = self.repair_session_factory()
        else:
            repair_session = ClickInteractiveSession()
        repair_session.seed(report)

        skipped = 0
        auto_applied = 0
        choices_by_finding: dict[str, int] = {}
        total_findings = 0
        _auto_mode = auto  # may flip to True mid-session via [a] shortcut

        for tool_name in confirmed_plan.tools:
            tool = ALL_TOOLS.get(tool_name)
            if tool is None:
                continue

            tool_result: ToolResult = tool.extract(report)
            self.session.on_event(
                AgentEvent(
                    kind="tool_start",
                    data={"tool": tool_name, "status": tool_result.status},
                )
            )

            # Filter findings to those in scope for this tool
            tool_findings = filter_interactive_findings(
                report,
                explicit_interactive=explicit_interactive,
            )
            tool_findings = [f for f in tool_findings if f.source_check == tool_name]

            for finding in tool_findings:
                total_findings += 1
                options = repair_session.present_finding(finding.finding_id)

                if _auto_mode:
                    # Auto mode: pick the primary repair option without prompting.
                    if options:
                        repair_session.record_choice(finding.finding_id, options[0])
                        choices_by_finding[finding.finding_id] = 1
                        if not quiet:
                            click.echo(
                                f"  [auto] [{finding.finding_id}] {finding.message[:60]}"
                                f" → {options[0].label}"
                            )
                        auto_applied += 1
                    else:
                        skip_opt = _skip_option(finding)
                        _register_dynamic_option(repair_session, finding.finding_id, skip_opt)
                        repair_session.record_choice(finding.finding_id, skip_opt)
                        choices_by_finding[finding.finding_id] = 4
                        skipped += 1
                    continue

                # Interactive mode: show menu + [a] shortcut.
                choice = _prompt_agent_menu_choice(finding, options)
                choices_by_finding[finding.finding_id] = choice if choice != 5 else 1

                if choice == 5:
                    # Switch to auto for this and all remaining findings.
                    _auto_mode = True
                    self.session.on_event(AgentEvent("mode_switch", {"to": "auto"}))
                    if not quiet:
                        click.echo("  Switching to auto mode for all remaining findings.")
                    if options:
                        repair_session.record_choice(finding.finding_id, options[0])
                        auto_applied += 1
                    else:
                        skip_opt = _skip_option(finding)
                        _register_dynamic_option(repair_session, finding.finding_id, skip_opt)
                        repair_session.record_choice(finding.finding_id, skip_opt)
                        skipped += 1
                    continue

                if choice == 4:
                    skip_opt = _skip_option(finding)
                    _register_dynamic_option(repair_session, finding.finding_id, skip_opt)
                    repair_session.record_choice(finding.finding_id, skip_opt)
                    skipped += 1
                    continue

                if choice == 3:
                    definition = repair_session.ask("Enter your definition:")
                    custom_opt = _custom_option(finding, definition)
                    _register_dynamic_option(repair_session, finding.finding_id, custom_opt)
                    repair_session.record_choice(finding.finding_id, custom_opt)
                    continue

                index = choice - 1
                if 0 <= index < len(options):
                    repair_session.record_choice(finding.finding_id, options[index])
                else:
                    click.echo(
                        f"  Warning: option {choice} unavailable for [{finding.finding_id}]. Skipping.",
                        err=True,
                    )
                    skipped += 1

            self.session.on_event(
                AgentEvent(
                    kind="tool_done",
                    data={
                        "tool": tool_name,
                        "status": tool_result.status,
                        "finding_count": len(tool_findings),
                    },
                )
            )

        patches = repair_session.approved_patches()
        self.session.on_event(
            AgentEvent(
                kind="session_done",
                data={
                    "total_findings": total_findings,
                    "patch_count": len(patches),
                    "skipped": skipped,
                    "auto_applied": auto_applied,
                },
            )
        )

        # 5. Apply patches
        postflight_exit = 0
        if apply and patches:
            postflight_exit = apply_approved_patches(
                patches,
                dry_run=dry_run,
                quiet=quiet,
                project_root=root,
                original_target=target,
                strict=strict,
                choices_by_finding=choices_by_finding,
            )

        auto_part = f", {auto_applied} auto-applied" if auto_applied else ""
        message = (
            f"Agentic checkup complete: {report.status} "
            f"({total_findings} findings, {skipped} skipped{auto_part})"
        )
        if not quiet:
            click.echo(f"\n{message}")
        if postflight_exit:
            raise click.exceptions.Exit(postflight_exit)
        return message, 0.0, ""
