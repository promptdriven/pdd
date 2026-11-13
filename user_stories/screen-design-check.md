# Catch screens that drop their approved design

As a developer who builds screens from `.ui.svg` drawings, I want lint to warn when an HTML screen omits its stylesheet or CSS classes and an optional look check to compare colors, painted boxes and spacing, so that an unstyled screen cannot pass every check.

## Acceptance criteria

1. When `app-map.json` has `"stylesheets": []` for HTML screen `"ledger"` whose prompt `prompts/ledger_screen.prompt.md` links `prompts/views/ledger__stacked.ui.svg`, lint warns `Warning: SVG layout app-map.json -> prompts/ledger_screen.prompt.md: stylesheets: HTML screen "ledger" links prompts/views/ledger__stacked.ui.svg with no stylesheet in "stylesheets".`
2. When `app-map.json` lists `styles/pocket.css` defining `.btn-primary` and `.ledger-card` and `prompts/ledger_screen.prompt.md` names no class from `styles/pocket.css`, lint warns `Warning: SVG layout prompts/ledger_screen.prompt.md -> styles/pocket.css: stylesheet classes: HTML screen "ledger" links prompts/views/ledger__stacked.ui.svg and names no CSS class from its stylesheet (for example .btn-primary).`, and emits 0 warnings once the prompt names `.ledger-card`.
3. Comparing a rendered screen with `--look` against a `#0f172a` canvas and two stacked `#1e293b` cards (`#balance-card` at `388×68` and `#entry-list` at `388×74`, `12px` apart) passes when the screen has a `#111827` canvas and painted `380×66` and `380×72` `#1e293b` cards `14px` apart, without requiring pixel equality.
4. Comparing that same screen with `--look` when its stylesheet is dropped fails with status `look` on the `#ffffff` canvas and the unpainted `#balance-card` and `#entry-list` boxes (`unpainted box` and `unpainted box; gap 0px`).

```pdd-boundary
prompts/cli/screen-design-check.prompt.md
```

## Rules to check

- SVG mockup screens (`"source": "mockup"`) and HTML screens without `.ui.svg` drawings need no external stylesheet in `"stylesheets"`. Forbidden: a missing-stylesheet warning for a mockup screen or an HTML screen prompt with no `.ui.svg` link.
- Without `--look`, `pdd test --screen` checks only parts, text, regions and order. Forbidden: a color, box-paint, size or spacing failure when `--look` is omitted.
- A collapsed box (`320×14` against a `320×320` reference box) fails `--look` even when painted and centered. Forbidden: `passed: true` on a collapsed box under `--look`.

## Verification boundary

The prompt scenario checks the pure stylesheet-link advisory and look-comparison rules over supplied app-map, stylesheet and surface inputs. Native CLI and headless Chromium tests separately cover repository app-map discovery, CSS/prose token extraction, real browser DOM/CSS paint capture, `--look` CLI routing and JSON/table output; those filesystem and browser effects are not claimed as prompt-interpreter evidence.
