# `pdd context` token colors

Part of [EPIC #1540](EPIC-1540-design-refresh.md) — workstream 3, "`pdd context`
token visualization."

`pdd context` renders a Claude-Code `/context`-style usage box (and a `--table`
view) that attributes a hydrated prompt's tokens by source. This workstream
upgrades that view from a single-colored, glyph-only indicator to a readable,
**multi-color** one: color now distinguishes token *categories* at a glance,
while every count, ordering, glyph, and the machine-readable `--json` output
stay exactly the same.

## Categories → color (one place)

A row's category is its deterministic
[`status`](../../pdd/context_audit.py) — what a segment *is* — plus the synthetic
`free` for unused context-window space. Color tracks the category, not the
source string, so the same kind of segment always reads the same way (like
Claude Code's `/context`). The mapping lives in **one** table,
[`_CATEGORY_COLOR` in `pdd/commands/context.py`](../../pdd/commands/context.py),
built from the central palette in [`pdd/cli_theme.py`](../../pdd/cli_theme.py)
(Brand Guidelines v1.4 §3). No module hand-writes ANSI codes — every escape is
produced by `cli_theme.hex_to_ansi` / `ANSI_FAINT` / `ANSI_RESET`.

| Category      | Meaning                                            | Brand color    |
|---------------|----------------------------------------------------|----------------|
| `body`        | the prompt's own instructions (the hero)           | Electric-Cyan  |
| `resolved`    | a hydrated `<include>` source                      | Lumen-Purple   |
| `deferred`    | dynamic markup not yet realized (`<shell>`/`<web>`/`query=`) | Diff-Yellow (warn) |
| `unresolved`  | an `<include>` path that did not resolve           | Break-Red (error) |
| `unavailable` | requires PDD Cloud; counted as 0 tokens            | faint          |
| `free`        | unused context-window space (low emphasis)         | faint          |

Color flows through a single `paint(category, text)` seam: in the grid each cell
glyph is painted by its source's category (free cells use `free`); in the legend
the `glyph + source` marker is painted; in `--table` only the width-padded
`Source` cell is painted, so column alignment is unaffected by escape bytes.

## Color detection (`--color` / `--no-color` / auto)

The `--color/--no-color` flag is tri-state (default = auto):

- `--color` forces color on (even into a pipe — useful for `| less -R`).
- `--no-color` forces it off.
- **auto** (default): color only when stdout is a TTY **and** `NO_COLOR`
  (<https://no-color.org>, any value including empty) is unset. So piping,
  redirecting, and CI logs stay plain by default.

When color is off, the `paint` seam returns text unchanged, so the output is
**byte-for-byte identical** to the previous monochrome rendering — pipes and CI
logs are unaffected, and `--json` is never colored regardless of the flag.
