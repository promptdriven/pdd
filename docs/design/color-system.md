# PDD CLI color system

Part of [EPIC #1540](EPIC-1540-design-refresh.md) — workstream 1, "Command color
system."

The PDD CLI uses **one** color system, defined in [`pdd/cli_theme.py`](../../pdd/cli_theme.py)
and derived from the PromptDriven.ai Brand Guidelines v1.4 (§3 Color Palette,
§7 ASCII & Terminal Assets). Color communicates *meaning*, not decoration:
commands always look like commands, tags always look like tags, and states
(success / warning / error) are unmistakable.

## Why centralize

Before this, ~20 color names were used ad-hoc across the package (516 `[yellow]`,
239 `[red]`, 205 `[bold red]`, …) and four modules each defined their own inline
Rich `Theme`. The same idea (an error, a path, a tag) could appear in different
colors depending on which file printed it. A single theme fixes that and gives
every future command a ready-made, on-brand palette to build on.

## Brand palette

| Brand name      | Hex       | Role in the brand |
|-----------------|-----------|-------------------|
| Electric-Cyan   | `#00D8FF` | Primary           |
| Deep-Navy       | `#0A0A23` | Ink / Fill        |
| Lumen-Purple    | `#8C47FF` | Accent 1          |
| Prompt-Magenta  | `#FF2AA6` | Accent 2          |
| Light-Sleet     | `#F5F7FA` | Surface-Light     |
| Graphite-900    | `#1A1B26` | Surface-Dark      |
| Build-Green     | `#18C07A` | Success           |
| Build-Green-700 | `#0FA86A` | Success tint      |
| Diff-Yellow     | `#FBBB35` | Warning           |
| Break-Red       | `#F34842` | Error             |

## Semantic roles

Style output by **role**, never by raw color. The mapping below is the contract;
the colors behind it can evolve (e.g. adaptive theming, workstream 4) without
touching call sites.

| Role(s)                                   | Color           | When to use |
|-------------------------------------------|-----------------|-------------|
| `command`, `command.strong`, `heading`, `info`, `value` | Electric-Cyan | Subcommands, headings, primary info — the hero color |
| `tag`, `tag.strong`, `label`              | Lumen-Purple    | PDD/XML tags, labels, keys — distinct from commands |
| `accent`, `selector`                      | Prompt-Magenta  | Selections, highlights, CTAs — use sparingly |
| `success`, `success.strong`               | Build-Green     | Completed operations |
| `version`                                 | Build-Green-700 | Version line (per §7) |
| `warning`, `warning.strong`               | Diff-Yellow     | Recoverable problems, cautions |
| `error`                                   | bold Break-Red  | Failures |
| `danger`                                  | Break-Red       | Destructive prompts / emphasis |
| `path`                                    | dim Electric-Cyan | File paths, values |
| `muted`                                   | dim             | De-emphasized text |

The legacy role names `info`, `warning`, `error`, `success`, `path`, and
`selector` are kept resolvable so existing modules keep working as they migrate.

## Usage

```python
from pdd.cli_theme import get_console, style

console = get_console()                 # themed Rich Console (forwards kwargs)
console.print("[command]pdd sync[/command] [path]auth.prompt[/path]")
console.print("[success]✔ build succeeded[/success]")
console.print("[error]✗ generation failed[/error]")

# Build a styled fragment for a console that already carries the theme:
msg = style("warning", "no API key found")   # -> "[warning]no API key found[/warning]"

# Route to stderr while keeping the palette:
err = get_console(stderr=True)
```

For raw colors (charts, banners), import the palette constants
(`ELECTRIC_CYAN`, `BUILD_GREEN`, …) or `BRAND_PALETTE` rather than hardcoding hex.

## Terminal compatibility

Hex styles are emitted as truecolor and downgraded automatically by Rich to the
nearest 256/16-color value on limited terminals, and dropped entirely when output
is not a TTY (e.g. CI logs), matching the branding fallback guidance in §7.

## Adoption status

- ✅ `pdd/cli_theme.py` — the system itself.
- ✅ `pdd/content_selector.py` — first module migrated onto `get_console()`.
- ⬜ `construct_paths.py`, `metadata_sync.py`, `update_main.py` and the remaining
  inline `[color]` markup across the package — these are prompt-driven modules;
  they migrate via their prompts in follow-on PRs under this EPIC.
