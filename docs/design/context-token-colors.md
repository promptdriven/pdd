# `pdd context` token colors

Part of [EPIC #1540](EPIC-1540-design-refresh.md) — workstream 3, "`pdd context`
token visualization."

`pdd context` renders a Claude-Code `/context`-style usage box (and a `--table`
view) that attributes a hydrated prompt's tokens by source. This workstream
upgrades that view from a single-colored, glyph-only indicator to a readable,
**multi-color** one: **color** distinguishes each *source* so different includes
are visually distinct, while two row states (`unresolved`, `deferred`) are
reserved as semantic colors so problems always stand out. Every count, ordering,
and the machine-readable `--json` output stay exactly the same.

## Source → color (one place)

Color tracks the *source*, not its category — so two different includes are never
the same color (the original confusion: when color tracked category, every
`resolved` include came out the same purple). Two `status` values are reserved as
**overrides** so trouble pops regardless of position, and free/unavailable stay
faint. This lives in **one** place in
[`pdd/commands/context.py`](../../pdd/commands/context.py): a `_SOURCE_CYCLE`
tuple, a `_STATUS_OVERRIDE` map, and the `_row_colors(rows)` helper that assigns
one color per row. All hues come from the central palette in
[`pdd/cli_theme.py`](../../pdd/cli_theme.py) (Brand Guidelines v1.4 §3); no module
hand-writes ANSI codes (every escape is `cli_theme.hex_to_ansi` / `ANSI_FAINT` /
`ANSI_RESET`).

**Reserved overrides** (always, whatever the source's position):

| `status`      | Meaning                                            | Color             |
|---------------|----------------------------------------------------|-------------------|
| `unresolved`  | an `<include>` path that did not resolve           | Break-Red (error) |
| `deferred`    | dynamic markup not realized (`<shell>`/`<web>`/`query=`) | Diff-Yellow (warn) |
| `unavailable` | requires PDD Cloud; counted as 0 tokens            | faint             |
| *(free space)*| unused context-window space                        | faint             |

**Every other (counted) source** takes the next color in `_SOURCE_CYCLE` —
Electric-Cyan → Prompt-Magenta → Build-Green → Lumen-Purple — assigned by its
position among counted rows (overrides don't consume a slot). Distinct sources
therefore get distinct colors; with more sources than palette entries the cycle
wraps, but neighbours always differ. Assignment is deterministic because the
core returns rows in a stable order (largest first).

Color flows through a single `paint(color, text)` seam (the `color` is an ANSI
prefix from `_row_colors`): in the grid each cell glyph is painted by its row's
color (free cells faint); in the legend the `glyph + source` marker is painted;
in `--table` only the width-padded `Source` cell is painted, so column alignment
is unaffected by escape bytes.

## Glyphs: shared for counted, distinct for the rest

Glyphs no longer carry per-source identity (color does that now), so they're kept
to plain, universally-rendered shapes — **Geometric Shapes / Block Elements** —
that never show up as missing-glyph boxes the way the earlier `⛁`/`⛶` symbols did
in common terminal fonts (Menlo, SF Mono). The counted categories
(`body`/`resolved`/`deferred`/`unresolved`) all use one solid square `■`
(`_USED_GLYPH`); `unavailable` uses a faint `▨` and free space a faint light-shade
`░`, so those two non-usage rows stay legible even without color.
`_glyph_for(status)` is the single place that picks a row's glyph; all grid glyphs
share one display width so the grid stays aligned.

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
