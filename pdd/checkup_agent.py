"""LLM-agentic checkup session orchestration for ``pdd checkup``.

``CheckupAgent`` wraps the deterministic ``build_prompt_source_set_report``
pipeline with a planning layer (``Planner``) and an event/session layer
(``CheckupSession``).  It is built for impatient CLI users: one simple command,
grouped findings, safe defaults, useful artifacts, and a short, truthful summary.

Modes
-----
review (default, non-interactive)
    Runs the checks, groups findings, recommends safe fixes, writes a report and
    a patch preview, and prints a concise summary.  Never prompts, never edits
    files.  This is what ``pdd checkup <prompt> --planner deterministic`` does.

interactive
    Per-group confirmation ([Y]/[n]/[edit]/[a]).  The operator can type ``a`` to
    switch the rest of the session to auto mode.

auto
    Applies only low-risk fixes automatically; medium-risk fixes are saved for
    review and high-risk fixes are left as manual TODOs.  Never silently makes a
    risky change.

Safety
------
By default nothing is written to the prompt — fixes are queued / saved for
review and a patch preview is produced.  ``apply=True`` (the ``--apply`` flag)
is what actually edits files, after which the relevant checks are re-run to
verify the fix.
"""

from __future__ import annotations

import logging
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Callable, Optional, Union

import click

from .checkup_interactive_main import (
    ClickInteractiveSession,
    apply_approved_patches,
    draft_full_prompt_repair,
    draft_group_replacement,
    _custom_option,
    _register_dynamic_option,
    _skip_option,
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
from .checkup_report import (
    RISK_HIGH,
    RISK_LOW,
    RISK_MEDIUM,
    CheckupAccounting,
    FindingGroup,
    decision_for,
    descriptive_plan_lines,
    group_findings,
    humanize_group_summary,
    repair_risk_for,
    write_artifacts,
)
from .checkup_tools import ALL_TOOLS, ToolResult

logger = logging.getLogger(__name__)

_SessionType = Union[InteractiveRepairSession, ClickInteractiveSession]

MODE_REVIEW = "review"
MODE_INTERACTIVE = "interactive"
MODE_AUTO = "auto"


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
      tool_start      — a tool's result is available (status, skip_reason, count)
      tool_done       — finished presenting a tool's findings
      group           — a finding group is presented
      mode_switch     — interactive -> auto transition
      verifying       — re-running checks after applied fixes
      session_done    — final accounting + artifacts
    """
    data: dict = field(default_factory=dict)


class CheckupSession:
    """Base class / null implementation for a checkup event session."""

    def on_event(self, event: AgentEvent) -> None:  # noqa: B027
        pass

    def confirm_plan(self, plan: Plan) -> Optional[Plan]:
        """Return the confirmed plan (possibly modified), or None to abort."""
        return plan

    def decide_group(self, group: FindingGroup) -> str:
        """Return one of: 'accept', 'skip', 'edit', 'llm', 'auto'. Default: accept."""
        return "accept"

    def ask_definition(self) -> str:
        return ""

    def confirm_draft(self, group: FindingGroup, draft: str) -> bool:
        """Show an LLM-drafted fix and return whether to keep/apply it."""
        return False


class TerminalCheckupSession(CheckupSession):
    """Prints events to the terminal and drives per-group confirmation."""

    def __init__(self, *, quiet: bool = False) -> None:
        self.quiet = quiet
        self.events: list[AgentEvent] = []
        self._checks_header_done = False

    # -- rendering ---------------------------------------------------------

    def on_event(self, event: AgentEvent) -> None:
        self.events.append(event)
        if self.quiet:
            return
        getattr(self, f"_render_{event.kind}", self._render_default)(event.data)

    def _render_default(self, data: dict) -> None:  # noqa: ARG002
        pass

    def _render_plan_ready(self, data: dict) -> None:
        click.echo("\nStarting checkup")
        click.echo(f"Target: {data.get('target', '')}")
        click.echo("")
        for line in data.get("plan_lines", []):
            click.echo(line)

    def _render_plan_confirmed(self, data: dict) -> None:  # noqa: ARG002
        click.echo("\nChecks:")
        self._checks_header_done = True

    def _render_tool_start(self, data: dict) -> None:
        if not self._checks_header_done:
            click.echo("\nChecks:")
            self._checks_header_done = True
        tool = data.get("tool", "")
        status = data.get("status", "")
        reason = data.get("skip_reason", "")
        count = data.get("finding_count", 0)
        if status == "skip" and reason:
            suffix = f" — {reason}"
        elif count:
            suffix = f" — {count} finding(s)"
        else:
            suffix = ""
        click.echo(f"  {tool:<9} {status}{suffix}")

    def _render_group(self, data: dict) -> None:
        click.echo("")
        for line in data.get("summary_lines", []):
            click.echo(line)

    def _render_mode_switch(self, data: dict) -> None:
        frm = data.get("from", "interactive")
        to = data.get("to", "auto")
        click.echo(f"\nMode changed: {frm} -> {to}")
        if to == "llm-auto":
            click.echo("Letting the LLM draft and apply a fix for every remaining group.")
            click.echo("Each group costs a model call; offline groups are saved for review.")
        else:
            click.echo("Auto-applying low-risk fixes for remaining findings.")
            click.echo("Risky or ambiguous fixes will be left for review.")

    def _render_verifying(self, data: dict) -> None:
        click.echo("\nVerifying fixes...")
        for line in data.get("lines", []):
            click.echo(line)

    def _render_session_done(self, data: dict) -> None:
        click.echo("")
        for line in data.get("summary_lines", []):
            click.echo(line)

    # -- interaction -------------------------------------------------------

    def confirm_plan(self, plan: Plan) -> Optional[Plan]:
        click.echo("\nProceed with this plan? [Y]es / [n]o / [c]ustom / [q]uit")
        answer = click.prompt("", default="Y", show_default=False).strip().lower()
        if answer in ("n", "no", "q", "quit"):
            return None
        if answer in ("", "y", "yes"):
            return plan
        if answer not in ("c", "custom"):
            # Unrecognised → safest default is to proceed with the full plan.
            return plan
        raw = click.prompt("Enter tool names (comma-separated)", default=", ".join(plan.tools))
        custom = [t.strip() for t in raw.split(",") if t.strip()]
        from .checkup_tools import ALL_TOOL_NAMES  # pylint: disable=import-outside-toplevel
        valid = [t for t in custom if t in ALL_TOOL_NAMES]
        if not valid:
            click.echo("No valid tools selected. Aborting.", err=True)
            return None
        return Plan(tools=valid, rationale="Custom tool selection by operator.")

    def decide_group(self, group: FindingGroup) -> str:
        action_a = {
            "low": "Queue recommended fix",
            "medium": "Save recommended fix for review",
            "high": "Acknowledge (manual TODO)",
        }.get(group.risk, "Apply recommended fix")
        # The rationale/details are already printed inline above (the group
        # summary), so the menu stays short — no separate "view details" step.
        while True:
            click.echo("\nRepair options:")
            click.echo(f"[1] Option A: {action_a}")
            click.echo("[2] Option B: Save an alternative repair proposal")
            click.echo("[3] Keep current / skip")
            click.echo("[4] Custom fix")
            click.echo("[5] Let the LLM draft this fix now (costs a model call)")
            click.echo("[a] Auto for remaining — deterministic (apply low-risk, save the rest)")
            click.echo("[f] Let the LLM fix ALL remaining — auto, applies real fixes")
            click.echo("[q] Quit")
            answer = click.prompt("Choice", default="1", show_default=False).strip().lower()
            if answer in ("q", "quit"):
                return "quit"
            if answer in ("a", "auto"):
                return "auto"
            if answer in ("f", "fix", "fixall", "llm-auto", "llmauto"):
                return "llm_auto"
            if answer in ("", "1", "y", "yes", "option a"):
                return "accept"
            if answer in ("2", "b", "option b"):
                return "accept_alt"
            if answer in ("3", "n", "no", "skip", "keep"):
                return "skip"
            if answer in ("4", "e", "edit", "custom"):
                return "edit"
            if answer in ("5", "l", "llm", "draft"):
                return "llm"
            click.echo("Choose 1-5, a, f, or q.")

    def ask_definition(self) -> str:
        return click.prompt("Enter your definition / replacement", default="", show_default=False)

    def confirm_draft(self, group: FindingGroup, draft: str) -> bool:
        if not self.quiet:
            click.echo("\nLLM draft (review before keeping):")
            for line in str(draft).splitlines():
                click.echo(f"  {line}")
        answer = click.prompt(
            "Keep and apply this draft? [y/N]", default="n", show_default=False
        ).strip().lower()
        return answer in ("y", "yes")


class RecordingCheckupSession(CheckupSession):
    """Test double: records events, auto-confirms plans, scriptable group decisions."""

    def __init__(
        self,
        *,
        confirm: bool = True,
        custom_plan: Optional[Plan] = None,
        group_decisions: Optional[list[str]] = None,
        definition: str = "observable criteria",
        confirm_drafts: bool = True,
    ) -> None:
        self._confirm = confirm
        self._custom_plan = custom_plan
        self._group_decisions = list(group_decisions or [])
        self._definition = definition
        self._confirm_drafts = confirm_drafts
        self.events: list[AgentEvent] = []

    def on_event(self, event: AgentEvent) -> None:
        self.events.append(event)

    def confirm_plan(self, plan: Plan) -> Optional[Plan]:
        if not self._confirm:
            return None
        return self._custom_plan if self._custom_plan is not None else plan

    def decide_group(self, group: FindingGroup) -> str:
        if self._group_decisions:
            return self._group_decisions.pop(0)
        return "accept"

    def ask_definition(self) -> str:
        return self._definition

    def confirm_draft(self, group: FindingGroup, draft: str) -> bool:
        return self._confirm_drafts

    def events_of_kind(self, kind: str) -> list[AgentEvent]:
        return [e for e in self.events if e.kind == kind]


# ---------------------------------------------------------------------------
# Agent
# ---------------------------------------------------------------------------


class CheckupAgent:
    """Plan → check → group → repair → summarize, with safe defaults."""

    def __init__(
        self,
        planner: DeterministicPlanner,
        session: CheckupSession,
        *,
        repair_session_factory: Optional[Callable[[], _SessionType]] = None,
        repair_drafter: Optional[Callable[..., tuple]] = None,
        repair_drafter_full: Optional[Callable[..., tuple]] = None,
    ) -> None:
        self.planner = planner
        self.session = session
        self.repair_session_factory = repair_session_factory
        # Injectable so tests (and offline runs) never hit a real model.
        # ``repair_drafter`` drafts one group (interactive [5]); ``repair_drafter_full``
        # rewrites the whole prompt in one pass (--auto --llm-repair).
        self.repair_drafter = repair_drafter or draft_group_replacement
        self.repair_drafter_full = repair_drafter_full or draft_full_prompt_repair

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
        mode: Optional[str] = None,
        gate: bool = True,
        llm_repair: bool = False,
    ) -> tuple[str, float, str]:
        """Run the full checkup cycle. Returns ``(message, cost, model)``.

        When ``gate`` is True (default) a blocking result raises ``Exit(2)`` so the
        command line acts as a gate. Multi-file callers pass ``gate=False`` to
        collect each file's decision (via the session) and gate once at the end.
        """
        root = project_root if project_root is not None else Path.cwd()
        prompt_path = Path(target)
        if not prompt_path.is_absolute():
            prompt_path = root / target
        if not prompt_path.exists():
            raise click.UsageError(f"Prompt file not found: {target}")
        if prompt_path.is_dir():
            raise click.UsageError(
                f"Expected a single .prompt file for interactive checkup, got directory: {target}"
            )
        if prompt_path.suffix.lower() != ".prompt":
            raise click.UsageError(
                f"Expected a single .prompt file for interactive checkup, got: {target}"
            )

        if mode is None:
            mode = MODE_AUTO if auto else MODE_INTERACTIVE
        prompt_text = prompt_path.read_text(encoding="utf-8")
        available_tools = list(ALL_TOOLS)

        # 1. Plan
        plan = self.planner.suggest(prompt_path, available_tools, prompt_text)
        descriptions = {name: tool.description for name, tool in ALL_TOOLS.items()}
        self.session.on_event(
            AgentEvent(
                kind="plan_ready",
                data={
                    "target": target,
                    "available_tools": available_tools,
                    "plan_lines": descriptive_plan_lines(plan.tools, descriptions),
                    "tools": plan.tools,
                    "rationale": plan.rationale,
                },
            )
        )

        # 2. Confirm plan (only genuine interactive mode asks)
        if mode == MODE_INTERACTIVE:
            confirmed_plan = self.session.confirm_plan(plan)
        else:
            confirmed_plan = plan
        if confirmed_plan is None:
            msg = "Checkup aborted by operator."
            if not quiet:
                click.echo(msg)
            return msg, 0.0, ""
        self.session.on_event(
            AgentEvent(kind="plan_confirmed", data={"tools": confirmed_plan.tools})
        )

        # 3. Run all checks in one pass
        report = build_prompt_source_set_report(
            prompt_path, target=target, project_root=root, strict=strict
        )

        repair_session: _SessionType = (
            self.repair_session_factory()
            if self.repair_session_factory is not None
            else ClickInteractiveSession()
        )
        repair_session.seed(report)

        findings_by_id = {f.finding_id: f for f in report.findings}

        # Emit per-tool status (and collect in-scope findings for grouping).
        in_scope: list[SourceSetFinding] = []
        for tool_name in confirmed_plan.tools:
            tool = ALL_TOOLS.get(tool_name)
            if tool is None:
                continue
            tr: ToolResult = tool.extract(report)
            # The agent groups and risk-gates EVERY finding (low → apply/queue,
            # medium → save, high → manual TODO), so all findings are in scope
            # regardless of explicit_interactive. The clarification-only filter
            # belongs to the workflow-gate path (run_interactive_checkup), not
            # here — filtering here would hide coverage/contract findings from
            # auto mode and --llm-repair.
            tool_findings = [
                f for f in report.findings if f.source_check == tool_name
            ]
            self.session.on_event(
                AgentEvent(
                    kind="tool_start",
                    data={
                        "tool": tool_name,
                        "status": tr.status,
                        "skip_reason": tr.skip_reason,
                        "finding_count": len(tool_findings),
                    },
                )
            )
            self.session.on_event(
                AgentEvent(
                    kind="tool_done",
                    data={"tool": tool_name, "status": tr.status,
                          "finding_count": len(tool_findings)},
                )
            )
            in_scope.extend(tool_findings)

        # 4. Group findings and decide per group
        groups = group_findings(in_scope)
        acc = CheckupAccounting(total=sum(g.size for g in groups))
        # disposition per finding_id: "low" (queued low-risk), "manual_low"
        # (interactively accepted low-risk), "review", "manual_todo", "skip",
        # "custom" (operator edit).
        disposition: dict[str, str] = {}
        _auto = mode == MODE_AUTO
        # LLM-drafted, operator-approved patches (menu option 5/[f]). Applied
        # separately from the bulk --apply path because each was explicitly
        # confirmed in-session.
        llm_patches: list[ApprovedPatch] = []
        # True when the queued LLM patch came from the HEADLESS --auto --llm-repair
        # path, which has no in-session approval and so honors the --apply write
        # gate (preview unless --apply). The interactive [5]/[f] paths are already
        # approved in-session and write without --apply.
        _llm_apply_gated = False
        total_cost = 0.0
        last_model = ""

        # --auto --llm-repair: a single LLM pass rewrites the whole prompt so
        # ALL findings are fixed at once (not one group at a time). Preview by
        # default; written only with --apply (consistent with deterministic --auto).
        auto_llm_done = False
        if _auto and llm_repair and groups:
            for group in groups:
                self.session.on_event(
                    AgentEvent(
                        kind="group",
                        data={
                            "source_check": group.source_check,
                            "code": group.code,
                            "size": group.size,
                            "risk": group.risk,
                            "summary_lines": humanize_group_summary(group),
                        },
                    )
                )
            cost_inc, model_inc, auto_llm_done = self._full_rewrite_all(
                groups=groups,
                prompt_text=prompt_text,
                root=root,
                disposition=disposition,
                llm_patches=llm_patches,
            )
            total_cost += cost_inc
            if model_inc:
                last_model = model_inc
            if auto_llm_done:
                # Headless path: subject to the --apply write gate.
                _llm_apply_gated = True
            elif not quiet:
                click.echo(
                    "\nLLM repair unavailable (no credential / offline / out of credits) "
                    "— falling back to per-finding review."
                )

        for group in groups:
            if auto_llm_done:
                break  # every finding was handled by the single full rewrite
            risk = group.risk
            self.session.on_event(
                AgentEvent(
                    kind="group",
                    data={
                        "source_check": group.source_check,
                        "code": group.code,
                        "size": group.size,
                        "risk": risk,
                        "summary_lines": humanize_group_summary(group),
                    },
                )
            )

            decision = "accept"  # default for review / auto
            if mode == MODE_INTERACTIVE and not _auto:
                decision = self.session.decide_group(group)
                if decision == "quit":
                    # Operator quit: stop processing further groups. Nothing
                    # touched (no patch is written without --apply); the summary
                    # below reports what was decided so far.
                    self.session.on_event(AgentEvent("quit", {}))
                    if not quiet:
                        click.echo("\nQuit — remaining findings left untouched.")
                    break
                if decision == "auto":
                    _auto = True
                    self.session.on_event(
                        AgentEvent("mode_switch", {"from": "interactive", "to": "auto"})
                    )
                    decision = "accept"
                elif decision == "llm_auto":
                    # [f]: LLM-fix EVERY group in one coherent rewrite (the same
                    # reliable mechanism as --auto --llm-repair), then finish.
                    self.session.on_event(
                        AgentEvent("mode_switch", {"from": "interactive", "to": "llm-auto"})
                    )
                    cost_inc, model_inc, done = self._full_rewrite_all(
                        groups=groups,
                        prompt_text=prompt_text,
                        root=root,
                        disposition=disposition,
                        llm_patches=llm_patches,
                    )
                    total_cost += cost_inc
                    if model_inc:
                        last_model = model_inc
                    if done:
                        auto_llm_done = True
                        break
                    # Offline / no key → finish deterministically for the rest.
                    _auto = True
                    if not quiet:
                        click.echo(
                            "\nLLM repair unavailable (no credential / offline / out of "
                            "credits) — finishing with deterministic auto."
                        )
                    decision = "accept"

            # [5]: draft one group via the LLM, approved per group.
            if decision == "llm":
                cost_inc, model_inc, handled = self._draft_group(
                    group=group,
                    prompt_text=prompt_text,
                    root=root,
                    disposition=disposition,
                    llm_patches=llm_patches,
                )
                total_cost += cost_inc
                if model_inc:
                    last_model = model_inc
                if handled:
                    continue
                # Draft unavailable (offline/no key) or declined → fall back to
                # the deterministic save-for-review path.
                decision = "accept"

            definition = ""
            if decision == "edit":
                definition = self.session.ask_definition()

            self._record_group(
                group=group,
                risk=risk,
                decision=decision,
                interactive=(mode == MODE_INTERACTIVE and not _auto),
                definition=definition,
                repair_session=repair_session,
                disposition=disposition,
                acc=acc,
            )

        # 5. Collect patches; segregate by risk
        all_patches: list[ApprovedPatch] = repair_session.approved_patches()
        low_risk_patches = [
            p
            for p in all_patches
            if repair_risk_for(findings_by_id.get(p.finding_id)) == RISK_LOW
        ]
        # medium-risk approving patches feed the preview but are never applied.

        applied = False
        verification = None
        if apply and low_risk_patches:
            choices = {fid: 1 for fid in disposition}
            exit_code = apply_approved_patches(
                low_risk_patches,
                dry_run=dry_run,
                quiet=True,
                project_root=root,
                original_target=target,
                strict=strict,
                choices_by_finding=choices,
            )
            if exit_code == 0:
                if dry_run:
                    acc.patches_queued = len(low_risk_patches)
                else:
                    applied = True
                    self._tally_applied(disposition, acc, len(low_risk_patches))
                    verification = self._verify(
                        prompt_path, target, root, strict, groups, quiet
                    )
            else:
                acc.patches_failed = len(low_risk_patches)
        else:
            # nothing applied — count queued (low-risk) for the summary
            acc.patches_queued = sum(
                1 for d in disposition.values() if d in ("low", "manual_low")
            )

        # 5b. Apply LLM drafts. Interactive [5]/[f] drafts are approved in-session
        # and apply regardless of the bulk --apply flag; the headless
        # --auto --llm-repair draft (_llm_apply_gated) honors the --apply write gate
        # so a material write never happens without explicit approval. Both honor
        # --dry-run/--preview.
        if llm_patches:
            llm_finding_ids = [fid for fid, d in disposition.items() if d == "llm"]
            _preview_only = dry_run or (_llm_apply_gated and not apply)
            if _preview_only:
                acc.patches_queued += len(llm_patches)
                if _llm_apply_gated and not apply and not dry_run and not quiet:
                    click.echo(
                        "\nLLM repair drafted but not written — re-run with --apply to "
                        "apply it, or --dry-run to preview."
                    )
            else:
                code = apply_approved_patches(
                    llm_patches,
                    dry_run=False,
                    quiet=True,
                    project_root=root,
                    original_target=target,
                    strict=strict,
                    choices_by_finding={p.finding_id: 7 for p in llm_patches},
                )
                if code == 0:
                    applied = True
                    acc.drafted_by_llm = len(llm_finding_ids)
                    acc.patches_applied += len(llm_patches)
                    if verification is None:
                        verification = self._verify(
                            prompt_path, target, root, strict, groups, quiet
                        )
                else:
                    acc.patches_failed += len(llm_patches)

        # 6. Artifacts (only when there is something to write)
        artifacts = write_artifacts(
            project_root=root,
            prompt_path=prompt_path,
            target=target,
            status=report.status,
            tool_results=[ALL_TOOLS[t].extract(report) for t in confirmed_plan.tools if t in ALL_TOOLS],
            groups=groups,
            accounting=acc,
            patches=all_patches,
            applied=applied,
        )
        artifacts_display = {
            k: _relpath(v, root) for k, v in artifacts.items()
        }

        # 7. Lifecycle decision: can the next PDD step proceed?
        blocking = report.deterministic_exit_code(strict=strict) >= 2
        decision_text, can_continue = decision_for(
            report.status, strict=strict, blocking=blocking
        )

        # 8. Final summary
        self.session.on_event(
            AgentEvent(
                kind="session_done",
                data={
                    "status": report.status,
                    "accounting": _accounting_dict(acc),
                    "artifacts": artifacts_display,
                    "applied": applied,
                    "verification": verification,
                    "decision": decision_text,
                    "can_continue": can_continue,
                    "blocking": blocking,
                    "summary_lines": acc.summary_lines(
                        report.status, artifacts_display, decision=decision_text
                    ),
                    # legacy keys kept for older tests / callers
                    "total_findings": acc.total,
                    "skipped": acc.skipped_by_user,
                    "auto_applied": acc.fixed_automatically,
                    "patch_count": len(all_patches),
                },
            )
        )

        message = (
            f"Checkup complete: {report.status} "
            f"({acc.total} findings, {acc.fixed_automatically} fixed, "
            f"{acc.skipped_by_user} skipped, {acc.remaining} remaining) "
            f"— {decision_text}"
        )
        # Act as a gate: block (non-zero exit) so the next PDD step can be
        # skipped by callers / CI when the prompt is not ready. Multi-file
        # callers pass gate=False and gate once after the whole directory.
        if not can_continue and gate:
            if not quiet:
                click.echo(f"\n{message}")
            raise click.exceptions.Exit(2)
        return message, total_cost, last_model

    # ------------------------------------------------------------------
    # helpers
    # ------------------------------------------------------------------

    # Map a finding's source check to an allowlisted patch kind for the apply
    # path (see ALLOWED_PATCH_KINDS in checkup_prompt_apply).
    _LLM_PATCH_KIND_BY_SOURCE = {
        "lint": "vocab_definition",
        "contract": "contract_rule",
        "coverage": "coverage_line",
        "gate": "waiver",
        "snapshot": "contract_rule",
    }

    def _full_rewrite_all(
        self,
        *,
        groups: list,
        prompt_text: str,
        root: Path,
        disposition: dict,
        llm_patches: list,
    ) -> tuple[float, str, bool]:
        """One LLM pass rewrites the whole prompt to fix every group, queued once.

        Returns ``(cost, model, done)``. ``done`` is False when no draft is
        available (offline / no key), so callers fall back to the deterministic
        path. Shared by ``--auto --llm-repair`` and the interactive ``[f]`` option
        so both fix all findings in one coherent, reliably-verified rewrite.
        """
        if not groups:
            return 0.0, "", False
        new_text, cost, model = self.repair_drafter_full(groups, prompt_text=prompt_text)
        if not new_text:
            return cost, model, False
        rep_file = groups[0].findings[0].file
        src = rep_file if rep_file.is_absolute() else Path(root) / rep_file
        try:
            target_path = src.resolve().relative_to(Path(root).resolve())
        except ValueError:
            target_path = rep_file
        llm_patches.append(
            ApprovedPatch(
                kind="full_rewrite",
                target=target_path,
                anchor={"finding_id": "checkup:full"},
                replacement=new_text,
                finding_id="checkup:full",
            )
        )
        for group in groups:
            for finding in group.findings:
                disposition[finding.finding_id] = "llm"
        return cost, model, True

    def _draft_group(
        self,
        *,
        group: FindingGroup,
        prompt_text: str,
        root: Path,
        disposition: dict,
        llm_patches: list,
        auto_confirm: bool = False,
    ) -> tuple[float, str, bool]:
        """Draft an LLM fix for one group, confirm it, and queue it for apply.

        Returns ``(cost, model, handled)``. ``handled`` is False when no draft is
        available (offline / no key) or the operator declines, so the caller
        falls back to the deterministic save-for-review path. ``auto_confirm``
        skips the per-group approval (used by ``--auto --llm-repair``).
        """
        snippet, cost, model = self.repair_drafter(group, prompt_text=prompt_text)
        if not snippet:
            self.session.on_event(
                AgentEvent("llm_draft", {"code": group.code, "status": "unavailable"})
            )
            if not getattr(self.session, "quiet", False):
                click.echo(
                    "\nLLM draft unavailable (no credential / offline / out of credits) "
                    "— saving for review instead."
                )
            return cost, model, False

        confirmed = True if auto_confirm else self.session.confirm_draft(group, snippet)
        self.session.on_event(
            AgentEvent(
                "llm_draft",
                {
                    "code": group.code,
                    "status": "kept" if confirmed else "discarded",
                    "model": model,
                    "cost": cost,
                },
            )
        )
        if not confirmed:
            return cost, model, False

        rep = group.findings[0]
        source_path = rep.file
        if not source_path.is_absolute():
            source_path = Path(root) / source_path
        try:
            target = source_path.resolve().relative_to(Path(root).resolve())
        except ValueError:
            target = rep.file
        kind = self._LLM_PATCH_KIND_BY_SOURCE.get(group.source_check, "vocab_definition")
        # Empty anchor line → appended at end of file (see _apply_patch_content).
        llm_patches.append(
            ApprovedPatch(
                kind=kind,
                target=target,
                anchor={"finding_id": rep.finding_id, "line": ""},
                replacement=snippet,
                finding_id=rep.finding_id,
            )
        )
        for finding in group.findings:
            disposition[finding.finding_id] = "llm"
        return cost, model, True

    def _record_group(
        self,
        *,
        group: FindingGroup,
        risk: str,
        decision: str,
        interactive: bool,
        definition: str,
        repair_session: _SessionType,
        disposition: dict,
        acc: CheckupAccounting,
    ) -> None:
        """Apply one group decision to every finding in the group."""
        for finding in group.findings:
            fid = finding.finding_id
            options = repair_session.present_finding(fid)

            if decision == "skip":
                self._record_skip(repair_session, finding)
                disposition[fid] = "skip"
                acc.skipped_by_user += 1
                continue

            if decision == "edit":
                opt = _custom_option(finding, definition)
                _register_dynamic_option(repair_session, fid, opt)
                repair_session.record_choice(fid, opt)
                disposition[fid] = "custom"
                acc.fixed_manually += 1
                continue

            # decision == "accept" / "accept_alt"
            if risk == RISK_HIGH:
                # never auto-touch high-risk; leave as manual TODO
                self._record_skip(repair_session, finding)
                disposition[fid] = "manual_todo"
                acc.manual_todo += 1
                continue

            if risk == RISK_MEDIUM:
                # save for review: record the primary option so it appears in the
                # patch preview, but it will not be applied.
                if options:
                    selected = options[1] if decision == "accept_alt" and len(options) > 1 else options[0]
                    repair_session.record_choice(fid, selected)
                disposition[fid] = "review"
                acc.saved_for_review += 1
                continue

            # low risk
            if options:
                selected = options[1] if decision == "accept_alt" and len(options) > 1 else options[0]
                repair_session.record_choice(fid, selected)
                disposition[fid] = "manual_low" if interactive else "low"
            else:
                self._record_skip(repair_session, finding)
                disposition[fid] = "skip"
                acc.skipped_by_user += 1

    @staticmethod
    def _record_skip(repair_session: _SessionType, finding: SourceSetFinding) -> None:
        skip_opt = _skip_option(finding)
        _register_dynamic_option(repair_session, finding.finding_id, skip_opt)
        repair_session.record_choice(finding.finding_id, skip_opt)

    @staticmethod
    def _tally_applied(disposition: dict, acc: CheckupAccounting, n_patches: int) -> None:
        acc.patches_applied = n_patches
        for d in disposition.values():
            if d == "low":
                acc.fixed_automatically += 1
            elif d == "manual_low":
                acc.fixed_manually += 1

    def _verify(
        self,
        prompt_path: Path,
        target: str,
        root: Path,
        strict: bool,
        groups: list[FindingGroup],
        quiet: bool,
    ) -> dict:
        """Re-run checks for tools that had findings; report new status."""
        fresh = build_prompt_source_set_report(
            prompt_path, target=target, project_root=root, strict=strict
        )
        affected = {g.source_check for g in groups}
        lines: list[str] = []
        results: dict[str, str] = {}
        for tool_name in sorted(affected):
            tr = ALL_TOOLS[tool_name].extract(fresh) if tool_name in ALL_TOOLS else None
            status = tr.status if tr else "?"
            results[tool_name] = status
            note = "resolved" if status in ("pass", "skip") else "still has findings"
            lines.append(f"  {tool_name}: {status} — {note}")
        self.session.on_event(AgentEvent("verifying", {"lines": lines, "results": results}))
        return {"results": results}


# ---------------------------------------------------------------------------
# module helpers
# ---------------------------------------------------------------------------


def _relpath(path: Path, root: Path) -> str:
    try:
        return str(Path(path).relative_to(root))
    except ValueError:
        return str(path)


def _accounting_dict(acc: CheckupAccounting) -> dict:
    # asdict() covers every dataclass field automatically so newly added
    # accounting fields are never silently dropped from the event payload;
    # ``remaining`` is a derived property and must be added explicitly.
    return {**asdict(acc), "remaining": acc.remaining}


# ---------------------------------------------------------------------------
# Directory / multi-file checkup
# ---------------------------------------------------------------------------


def discover_prompt_files(directory: Path) -> list[Path]:
    """Return sorted ``*.prompt`` files under ``directory`` (recursive,
    excluding ``*_LLM.prompt`` scratch files).

    Discovery is recursive to match how ``classify_checkup_target`` recognises a
    prompt directory (it rglobs for prompts): targets like ``pdd/prompts`` keep
    prompts under ``commands/``, ``core/``, ``frontend/`` etc., and the directory
    gate must cover the whole tree rather than only the top level.
    """
    return sorted(
        p
        for p in Path(directory).rglob("*.prompt")
        if p.is_file() and not p.name.lower().endswith("_llm.prompt")
    )


def run_checkup_directory(
    planner: DeterministicPlanner,
    files: list[Path],
    *,
    project_root: Path,
    strict: bool = False,
    apply: bool = False,
    dry_run: bool = False,
    auto: bool = False,
    mode: str = MODE_REVIEW,
    quiet: bool = False,
    llm_repair: bool = False,
) -> tuple[str, float, str]:
    """Run a non-interactive checkup over many prompt files and summarise.

    Each file is checked (gate=False so individual blocks don't exit early),
    a one-line decision is printed per file, then an aggregate summary. The
    command exits 2 if any prompt blocked — one gate for the whole directory.
    """
    root = Path(project_root)
    counts = {"pass": 0, "warn": 0, "fail": 0}
    any_block = False

    if not quiet:
        click.echo(f"Checkup: {len(files)} prompt(s) under {_relpath(files[0].parent, root)}/\n")

    for prompt_file in files:
        session = RecordingCheckupSession()
        agent = CheckupAgent(planner, session)
        rel = _relpath(prompt_file, root)
        agent.run(
            rel,
            project_root=root,
            strict=strict,
            apply=apply,
            dry_run=dry_run,       # honor --dry-run/--preview for the whole set
            quiet=True,            # suppress the full per-file dump
            explicit_interactive=False,
            auto=auto,
            mode=mode,
            gate=False,            # collect, don't exit per file
            llm_repair=llm_repair,
        )
        done = session.events_of_kind("session_done")
        if not done:
            continue
        data = done[-1].data
        status = data.get("status", "?")
        decision = data.get("decision", "")
        blocking = bool(data.get("blocking"))
        counts[status] = counts.get(status, 0) + 1
        any_block = any_block or blocking
        mark = "✗" if blocking else ("!" if status == "warn" else "✓")
        if not quiet:
            click.echo(f"  {mark} {prompt_file.name}: {status} — {decision}")

    summary = (
        f"{counts.get('pass', 0)} pass, {counts.get('warn', 0)} warn, "
        f"{counts.get('fail', 0)} block over {len(files)} prompt(s)"
    )
    if not quiet:
        click.echo(f"\nSummary: {summary}")
        if any_block:
            click.echo("Decision: blocking findings → block (at least one prompt is not ready)")
        else:
            click.echo("Decision: all prompts can continue")

    if any_block:
        raise click.exceptions.Exit(2)
    return f"Checkup complete: {summary}", 0.0, ""
