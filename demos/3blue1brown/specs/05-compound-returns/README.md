# Part 5: Compound Returns (18:00 - 20:15)

This section contrasts the returns on investment between patching and PDD. Patching yields linear-to-sublinear returns that diminish over time. PDD yields exponential returns because each test permanently constrains all future generations. The section closes with callbacks to the grandmother and developer from earlier, tying the economic argument together.

**Core Concept:** Every investment in the mold (tests, prompts, grounding) compounds. Every investment in patching (individual fixes) diminishes.

**Key Visual Motif:** Two curves on the same axes -- patching (linear/sublinear, amber) vs PDD (exponential, blue). The gap between them widens dramatically. This is the "Compound Curves" motif described in the main script's Visual Design Notes: "Mathematical, clean. Linear/sublinear for patching. Exponential for PDD."

Total runtime: ~2 minutes 15 seconds (135 seconds).

## Section Breakdown

| Section | File | Tool | Duration | Timestamp | Description |
|---------|------|------|----------|-----------|-------------|
| 5.1 | `01_compound_curves_intro.md` | Remotion | ~10s | 18:00-18:10 | Graph with two curves: Patching vs PDD |
| 5.2 | `02_patching_curve.md` | Remotion | ~20s | 18:10-18:30 | Patching curve grows linearly, local returns |
| 5.3 | `03_patching_curve_wobbles.md` | Remotion | ~15s | 18:30-18:45 | Curve wobbles and dips, annotations on regressions |
| 5.4 | `04_pdd_curve.md` | Remotion | ~10s | 18:45-18:55 | PDD curve introduced, each test is a point of investment |
| 5.5 | `05_pdd_curve_exponential.md` | Remotion | ~15s | 18:55-19:10 | PDD curve grows exponentially, gap widens |
| 5.6 | `06_investment_table.md` | Remotion | ~20s | 19:10-19:30 | Comparison table animates row by row |
| 5.7 | `07_return_to_grandmother.md` | Hybrid | ~10s | 19:30-19:40 | Callback to grandmother and modern sock imagery |
| 5.8 | `08_return_to_developer.md` | Hybrid | ~10s | 19:40-19:50 | Callback to developer with Cursor |
| 5.9 | `09_economics_chart_reprise.md` | Remotion | ~25s | 19:50-20:15 | Economics chart from Part 1 reprised, crossing point pulses |

## Tool Distribution

**Remotion (7 sections):** Graphs, curves, tables, chart reprise -- all programmatic animation
**Hybrid (2 sections):** Video callbacks to cold open / Part 1 footage with Remotion overlay

## Key Visual Elements

### Compound Curves (01-05)
- Two curves on the same axes: Time (X) vs Cumulative Value (Y)
- Patching curve: Amber (#D9944A), linear then sublinear with wobbles/dips
- PDD curve: Blue (#4A90D9), exponential growth
- The widening gap is the visual centerpiece

### Investment Table (06)
- Clean, typographic comparison table
- Three rows animate in sequence: Fix bug, Improve code, Document behavior
- Patching column shows diminishing returns (amber tint)
- PDD column shows compound returns (blue tint)

### Callback Visuals (07-09)
- Grandmother footage from cold open / Part 1, recontextualized
- Developer footage from cold open / Part 1, recontextualized
- Economics chart from Part 1 (spec `01-economics/04_code_cost_chart.md`) reprised with emphasis on crossing point

## Narration Text (Part 5)

> "Let's talk about compound returns."
>
> "When you patch code, each fix has local returns. You fixed one bug in one place. Similar bugs can still occur elsewhere. And sometimes your patch introduces new bugs -- CodeRabbit found AI patches carry one-point-seven times more issues than human code. So each patch risks creating more patches."
>
> "The returns are linear at best. Often sublinear. And the cost keeps compounding -- CISQ estimates technical debt costs US companies one-point-five-two trillion dollars annually."
>
> "When you add a test in PDD, the returns are different."
>
> "That test you wrote today? It constrains tomorrow's generation. And next week's. And next year's. It's a permanent wall."
>
> "Every investment in the mold has compound returns. Every investment in patching has diminishing returns."
>
> "Your great-grandmother wasn't stupid for darning socks. The economics made it rational."
>
> "And you're not stupid for patching code. Until now, the economics made it rational."
>
> "But the economics changed. And when economics change, behavior that was rational becomes... darning socks."

## Color Palette (Part 5)

- **PDD / Generation (Blue):** #4A90D9 - cool blue for compound returns
- **Patching / Tests (Amber):** #D9944A - warm amber for diminishing returns
- **Patched Code accent:** Warmer gray with red tint for regression markers
- **Grounding (Green):** #5AAA6E - soft green
- **Background:** Dark (#1a1a2e)
- **Table text:** White/light gray, with column tints matching curve colors

## Visual Style Notes

- Mathematical, 3Blue1Brown-style graphing throughout
- Clean typography on the investment table
- Callbacks (07, 08) should feel like a deliberate return -- the viewer recognizes the footage
- The economics chart reprise (09) should feel like a bookend to Part 1
- Pacing builds: curves introduced, gap widens, table summarizes, callbacks land the emotional beat
