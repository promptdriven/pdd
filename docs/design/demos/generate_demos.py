"""Generate SVG terminal captures for EPIC #1540 design-refresh PRs 1-3.

Run with: PYTHONPATH=<worktree> <pdd-cli python> /tmp/gen_demos.py <outdir>
Each capture uses the *real* PDD modules from the worktree, so the colors,
glyphs, and message shapes are exactly what the CLI emits.
"""
import sys
import time
from pathlib import Path

from rich.console import Console
from rich.rule import Rule
from rich.text import Text

OUT = Path(sys.argv[1] if len(sys.argv) > 1 else "/tmp")
OUT.mkdir(parents=True, exist_ok=True)
WIDTH = 92


def save_clean_svg(con, name, title):
    """Export an SVG and strip trailing whitespace per line.

    Rich's SVG template leaves whitespace-only indented lines between structural
    elements; they are insignificant in SVG but trip ``git diff --check``. We
    write the capture, then rewrite it without trailing whitespace so the
    committed demos stay clean (and regeneration does not reintroduce the noise).
    """
    path = OUT / name
    con.save_svg(str(path), title=title)
    text = path.read_text(encoding="utf-8")
    cleaned = "\n".join(line.rstrip() for line in text.split("\n"))
    path.write_text(cleaned, encoding="utf-8")
    print(f"wrote {name}")


def new_console():
    # record=True so we can export SVG; force_terminal so themed colors render.
    from pdd.cli_theme import get_console
    return get_console(record=True, force_terminal=True, width=WIDTH)


# ---------------------------------------------------------------------------
# PR #1 — Command color system (pdd/cli_theme.py)
# ---------------------------------------------------------------------------
def demo_pr1():
    from pdd.cli_theme import BRAND_PALETTE, style
    con = new_console()
    con.print(Rule("[heading]PR #1 — Command color system[/heading]  one brand palette, semantic roles"))
    con.print()
    con.print("[heading]Brand palette (PromptDriven.ai Brand Guidelines v1.4)[/heading]")
    for name, hexv in BRAND_PALETTE.items():
        con.print(f"  [{hexv}]██████[/{hexv}]  [muted]{name:<16}[/muted] [muted]{hexv}[/muted]")
    con.print()
    con.print("[heading]Semantic roles — every command speaks the same color language[/heading]")
    roles = [
        ("command", "pdd sync", "commands & identifiers"),
        ("tag", "[skipped]", "tags, labels, keys"),
        ("accent", "› selection", "selections / CTAs"),
        ("success", "build passed", "success state"),
        ("warning", "drift detected", "warning state"),
        ("error", "tests failed", "error state"),
        ("info", "12 modules", "informational values"),
        ("path", "pdd/cli_theme.py", "file paths"),
        ("muted", "(skipped)", "neutral helper text"),
    ]
    for role, text, desc in roles:
        con.print(f"  [{role}]{text:<22}[/{role}]  [muted]role=[/muted][tag]{role:<10}[/tag] [muted]{desc}[/muted]")
    con.print()
    con.print("[muted]Helper:[/muted] style(\"command\", \"pdd sync\") -> " + style("command", "pdd sync"))
    save_clean_svg(con, "demo-pr1-color-system.svg", "pdd — command color system (PR #1)")


# ---------------------------------------------------------------------------
# PR #2 — Status & progress messaging (pdd/cli_status.py)
# ---------------------------------------------------------------------------
def demo_pr2():
    from pdd.cli_status import StatusReporter, Status, GLYPHS, ROLES
    con = new_console()
    con.print(Rule("[heading]PR #2 — Status & progress messaging[/heading]  five shared primitives"))
    con.print()

    con.print("[heading]The five primitives — one glyph + one semantic color each[/heading]")
    for s in Status:
        con.print(f"  [{ROLES[s]}]{GLYPHS[s]}  {s.name:<8}[/{ROLES[s]}]  [muted]{ROLES[s]}[/muted]")
    con.print()

    con.print("[heading]Before / after — `pdd detect`[/heading]")
    con.print("  [muted]BEFORE[/muted]  [muted]Change detection completed successfully.[/muted]")
    con.print("  [muted]BEFORE[/muted]  [error]Error:[/error] [muted]change.txt not found[/muted]   [muted](no start, no progress, no fix)[/muted]")
    con.print()
    con.print("  [muted]AFTER[/muted]  a real run, start -> waiting-on-LLM -> success + next action:")
    r = StatusReporter("pdd detect", console=con)
    r.start("checking 3 prompt(s) against the change description")
    with r.waiting("asking the model which prompts need changes", on="LLM"):
        pass
    r.step("writing results to changes.csv")
    r.success("2 prompt(s) need changes",
              next_step="review the changes below, then run `pdd change` on each")
    con.print()

    con.print("[heading]Actionable failure — what failed + why + what to try[/heading]")
    r2 = StatusReporter("pdd detect", console=con)
    r2.start("checking 3 prompt(s) against the change description")
    r2.failure("reading the change file",
               reason="change.txt not found",
               suggestions=["check the path to the change file",
                            "run `pdd detect --help` for the expected arguments"])
    con.print()

    con.print("[heading]Second adopter — `pdd conflicts`[/heading]")
    r3 = StatusReporter("pdd conflicts", console=con)
    r3.start("checking 'login.prompt' and 'signup.prompt' for conflicting instructions")
    with r3.waiting("comparing the two prompts for conflicts", on="LLM"):
        pass
    r3.success("1 conflict(s) found between the two prompts",
               next_step="review the conflicts below and reconcile the prompts")

    save_clean_svg(con, "demo-pr2-status-messaging.svg", "pdd — status & progress messaging (PR #2)")


# ---------------------------------------------------------------------------
# PR #3 — pdd context token visualization (pdd/commands/context.py)
# ---------------------------------------------------------------------------
def demo_pr3():
    from pdd.commands.context import _render_usage_box, _render_table, _make_painter
    from pdd.context_audit import AuditRow, ContextAudit
    con = new_console()
    con.print(Rule("[heading]PR #3 — `pdd context` token visualization[/heading]  per-source colors + glyphs"))
    con.print()

    # Build a representative audit (deterministic; pure rendering, no LLM).
    rows = [
        AuditRow(source="prompt_body", tokens=12000, status="body", note=None),
        AuditRow(source="pdd/cli_theme.py", tokens=34000, status="resolved", note=None),
        AuditRow(source="docs/brand.md", tokens=21000, status="resolved", note=None),
        AuditRow(source="examples/usage.py", tokens=9000, status="resolved", note=None),
        AuditRow(source="context/missing.json", tokens=6000, status="unresolved", note="file not found"),
        AuditRow(source="context/big.txt", tokens=5000, status="deferred", note="loaded on demand"),
    ]
    total = sum(r.tokens for r in rows)
    limit = 200000
    pct = round(100 * total / limit, 1)
    paint = _make_painter(True)

    audit = ContextAudit(
        model="claude-opus-4-8", total_tokens=total, context_limit=limit,
        percent_used=pct, rows=rows,
    )
    box = _render_usage_box(audit, paint=paint)
    con.print(Text.from_ansi(box))
    con.print()
    con.print("[heading]--table view — per-source attribution[/heading]")
    table = _render_table(audit, paint=paint)
    con.print(Text.from_ansi(table))

    save_clean_svg(con, "demo-pr3-context-tokens.svg", "pdd context — token visualization (PR #3)")


if __name__ == "__main__":
    demo_pr1()
    demo_pr2()
    demo_pr3()
    print("done ->", OUT)
