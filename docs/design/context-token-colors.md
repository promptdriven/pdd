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
wraps, but neighbours always differ — and a **parallel glyph channel** (below)
gives every counted source its own glyph too, so the grid keeps source
attribution even with color off. Assignment is deterministic because the core
returns rows in a stable order (largest first).

Color and glyph are paired by a single `_row_styles(rows) -> [(glyph, color)]`
helper (the source of truth); `_row_colors` is a thin projection of its colour
half for the table path. Color flows through a single `paint(color, text)` seam:
in the grid each cell glyph is painted by its row's colour (free cells faint); in
the legend the `glyph + source` marker is painted; in `--table` only the
width-padded `Source` cell is painted, so column alignment is unaffected by
escape bytes.

## Glyphs: a parallel per-source channel

Colour is the primary per-source channel, but it must keep working with color
off (pipes, CI, `NO_COLOR`), so the glyph is a **parallel** channel: every
counted source gets its own glyph too. Counted sources draw from `_SOURCE_GLYPHS`
— four Neutral-width draughts pieces, one per palette hue: the white "king" `⛁`
(U+26C1, also Claude Code's `/context` used cell), the white "man" `⛀` (U+26C0),
and the filled "black" pair `⛃`/`⛂` (U+26C3/U+26C2). Glyph and colour cycle their
own tables **in lockstep**, so the first four distinct sources differ in *both*
channels — and the glyph alone keeps the monochrome grid source-attributed.
Like the colours, the glyphs wrap when there are more sources than entries, so
two sources that share a glyph also share a colour (the 5th source repeats the
1st in both). The reserved rows don't participate in the cycle — `unresolved` /
`deferred` keep the base `⛁` (their red/yellow marks them), `unavailable` a faint
`▨`, and free space a faint `⛶` (U+26F6).

On macOS, Terminal.app's CoreText font fallback (Apple Symbols) renders every one
of these as a single narrow cell (all four draughts glyphs U+26C0–C3 are
Neutral-width, like `⛁`), so the grid stays aligned. `_glyph_for(status)` picks
the glyph for the override/non-cycle rows; `_row_styles` owns the counted-source
glyph.

## Color detection (`--color` / `--no-color` / auto)

The `--color/--no-color` flag is tri-state (default = auto):

- `--color` forces color on (even into a pipe — useful for `| less -R`).
- `--no-color` forces it off.
- **auto** (default): color only when stdout is a TTY **and** `NO_COLOR`
  (<https://no-color.org>, any value including empty) is unset. So piping,
  redirecting, and CI logs stay plain by default.

When color is off, the `paint` seam returns text unchanged, so the output
carries **no ANSI at all** — pipes and CI logs stay plain, and `--json` is never
colored regardless of the flag. The glyph channel still runs, so the monochrome
grid keeps its per-source attribution (each counted source leads with its own
draughts glyph); only the color is dropped. The glyphs themselves are identical
with color on or off, so stripping the ANSI from a `--color` render yields
exactly the `--no-color` render — the invariant the tests pin.
