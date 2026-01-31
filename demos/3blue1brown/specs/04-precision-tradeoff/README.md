# Part 4: The Precision Tradeoff (13:45 - 15:45)

This section explains the inverse relationship between test coverage and required prompt precision. More tests means simpler prompts because the walls do the precision work.

**Core Concept:** Tests reduce prompt complexity - the mold constrains the output, not the specification.

**Key Metaphor:** 3D printing (must specify every point) vs Injection molding (walls do the precision work)

Total runtime: ~2 minutes (120 seconds).

## Section Breakdown

| Section | File | Tool | Duration | Timestamp | Description |
|---------|------|------|----------|-----------|-------------|
| 4.1 | `01_split_3d_vs_mold.md` | Veo 3.1 | ~15s | 13:45-14:00 | Split: 3D printer vs injection mold |
| 4.2 | `02_3d_printer_focus.md` | Hybrid | ~15s | 14:00-14:15 | 3D printer with coordinate grid overlay |
| 4.3 | `03_mold_flow_focus.md` | Hybrid | ~15s | 14:15-14:30 | Liquid flowing until walls constrain |
| 4.4 | `04_precision_graph.md` | Remotion | ~15s | 14:30-14:45 | Graph: Tests vs Required Prompt Precision |
| 4.5 | `05_graph_animate_curve.md` | Remotion | ~15s | 14:45-15:00 | Marker animates along inverse curve |
| 4.6 | `06_long_prompt.md` | Remotion | ~15s | 15:00-15:15 | Dense 50-line `parser_v1.prompt` |
| 4.7 | `07_short_prompt_tests.md` | Remotion | ~15s | 15:15-15:30 | 10-line prompt + terminal: 47 tests |
| 4.8 | `08_both_generate_final.md` | Remotion | ~15s | 15:30-15:45 | Split comparison + final message |

## Tool Distribution

**Veo 3.1 (1 section):** Split screen manufacturing comparison
**Hybrid (2 sections):** Video base with Remotion overlay for 3D printing and mold flow
**Remotion (5 sections):** Graphs, code displays, abstract animations

## Key Visual Elements

### Manufacturing Comparison (01-03)
- 3D printer: Precise, methodical, point-by-point deposition
- Injection mold: Chaotic flow that becomes precise at walls
- Coordinate grid overlay on 3D printer (Remotion)
- Wall highlight overlay on mold flow (Remotion)

### Graph Animation (04-05)
- Inverse curve: High prompt precision at low test count, low precision at high count
- Blue (#4A90D9) to Amber (#D9944A) gradient along curve
- Animated marker showing the tradeoff relationship

### Prompt Comparison (06-08)
- `parser_v1.prompt`: 50 lines, dense requirements, few test walls nearby
- `parser_v2.prompt`: 10 lines, surrounded by amber test walls
- Both generate correct code, demonstrating equivalence

## Narration Text (Part 4)

> "Here's something subtle that changes how you think about prompts."
>
> "In 3D printing, there's no mold. The machine must know exactly where to place every single point of material. The specification must be extremely precise."
>
> "In injection molding, precision comes from the walls. The material just flows until it's constrained."
>
> "This maps directly to PDD."
>
> "With few tests, your prompt needs to specify everything. Edge cases. Error handling. Exact behavior in every situation."
>
> "With many tests, the prompt only needs to specify intent. The tests handle the constraints."
>
> "This is why test accumulation matters. It's not just about catching bugs. It's about making prompts simpler and regeneration safer over time."
>
> "The more walls you have, the less you need to specify. The mold does the precision work."

## Color Palette (Part 4)

- **Prompt (Blue):** #4A90D9 - cool specification color
- **Tests/Walls (Amber):** #D9944A - warm constraint color
- **3D Printer accent:** #5A9FE9 - lighter blue for coordinates
- **Generated Code:** Gray (#A0A0A0) with blue tint
- **Success:** Green (#5AAA6E)
- **Background:** Dark (#1a1a2e)

## PDD Commands Shown

| Timestamp | Section | Command Shown |
|-----------|---------|---------------|
| ~15:20 | 07 - Short prompt | `pdd test parser` with 47 tests passing |

## Visual Style Notes

- Clean split screens for manufacturing comparison
- Technical coordinate grid overlays
- Smooth curve animations on graph
- Code displays with syntax highlighting
- Amber glow on test wall accumulation
- Final message emphasized with text animation
