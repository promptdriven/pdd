"""Example usage of pdd.server.budget primitives.

Demonstrates parsing /pdd comment commands, mutating BudgetState, formatting
startup/settings comments, and using should_halt as the executor's halt
predicate. Mirrors the contract documented in
`pdd/prompts/server/budget_python.prompt`.
"""

from rich.console import Console

# In a real application, import from the package:
# from pdd.server.budget import (
#     BudgetState, PddCommand, CommandResult, BudgetExceededError,
#     parse_pdd_command, apply_command,
#     format_startup_comment, format_settings_comment, should_halt,
# )

try:
    from pdd.server.budget import (
        BudgetState,
        PddCommand,
        CommandResult,
        BudgetExceededError,
        parse_pdd_command,
        apply_command,
        format_startup_comment,
        format_settings_comment,
        should_halt,
    )
except ImportError:
    # Minimal stubs so this example is parseable before generation.
    from dataclasses import dataclass, field
    from typing import Optional

    @dataclass
    class BudgetState:
        label_kind: str
        node_budget: Optional[float] = None
        max_total: Optional[float] = None
        spent: float = 0.0
        status: str = "running"
        stop_requested: bool = False

        def record_spend(self, amount: float) -> None:
            self.spent += max(0.0, amount)

        def effective_cap(self, node_count: int = 1) -> Optional[float]:
            if self.label_kind == "issue" and self.node_budget and self.max_total:
                return min(self.node_budget * max(node_count, 1), self.max_total)
            return self.max_total

    @dataclass
    class PddCommand:
        kind: str
        amount: Optional[float] = None
        raw: str = ""
        error: Optional[str] = None

    @dataclass
    class CommandResult:
        applied: bool = False
        reply: str = ""
        state_changed: bool = False

    class BudgetExceededError(RuntimeError):
        def __init__(self, spent: float, cap: float):
            super().__init__(f"budget exceeded: spent=${spent} cap=${cap}")
            self.spent = spent
            self.cap = cap

    def parse_pdd_command(comment_body: str):
        return None

    def apply_command(state, command):
        return CommandResult()

    def format_startup_comment(state) -> str:
        return ""

    def format_settings_comment(state) -> str:
        return ""

    def should_halt(state, node_count: int = 1) -> bool:
        return False


console = Console()


# ---------------------------------------------------------------------------
# 1. A fresh `pdd-issue` job posts a startup comment from BudgetState defaults
# ---------------------------------------------------------------------------
issue_state = BudgetState(label_kind="issue", node_budget=80.0, max_total=400.0)
console.print(format_startup_comment(issue_state))


# ---------------------------------------------------------------------------
# 2. A single-command job (e.g. `pdd-bug`) starts with no cap
# ---------------------------------------------------------------------------
bug_state = BudgetState(label_kind="bug")
console.print(format_startup_comment(bug_state))


# ---------------------------------------------------------------------------
# 3. Parsing an incoming comment and applying it to the active job
# ---------------------------------------------------------------------------
comment_body = "Thanks!\n/pdd budget max 200\n"
command = parse_pdd_command(comment_body)
if command is not None:
    result = apply_command(issue_state, command)
    console.print(result.reply)


# ---------------------------------------------------------------------------
# 4. The executor consults should_halt after each chunk of work
# ---------------------------------------------------------------------------
issue_state.record_spend(180.0)
if should_halt(issue_state, node_count=3):
    cap = issue_state.effective_cap(node_count=3)
    raise BudgetExceededError(spent=issue_state.spent, cap=cap or 0.0)


# ---------------------------------------------------------------------------
# 5. /pdd settings is read-only and reports current spend/status
# ---------------------------------------------------------------------------
settings_cmd = parse_pdd_command("/pdd settings")
if settings_cmd is not None:
    console.print(apply_command(issue_state, settings_cmd).reply)
