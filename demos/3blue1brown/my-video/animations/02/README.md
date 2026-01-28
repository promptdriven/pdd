# Part 1: The Economics of Darning (2:00 - 5:30)

This section establishes the economic argument for PDD by drawing a parallel between the economics of sock repair and code maintenance. Total runtime: ~3.5 minutes.

## Section Breakdown

| Section | File | Tool | Duration | Description |
|---------|------|------|----------|-------------|
| 1.1 | `01_sock_price_chart.md` | Remotion | ~20s | Animated line chart: sock cost vs labor over time |
| 1.2 | `02_threshold_highlight.md` | Remotion | ~10s | Highlight the 1970s crossing point |
| 1.3 | `03_lines_diverge.md` | Remotion | ~15s | Lines diverge dramatically by 2020 |
| 1.4 | `04_code_cost_chart.md` | Remotion | ~20s | Morph to code cost chart (generate vs patch vs debt) |
| 1.5 | `05_ai_milestones.md` | Remotion | ~15s | AI models marked on falling "generate" line |
| **1.6** | **`06_context_rot.md`** | **Remotion** | **~45s** | **NEW: Zoom into debt, explain context rot** |
| 1.7 | `07_crossing_point.md` | Remotion | ~10s | "We are here" - code crossing point pulses |
| 1.8 | `08_split_screen_sepia.md` | **Veo 3.1** | ~15s | Developer/grandmother split, sepia-toned |
| 1.9 | `09_developer_edit_zoomout.md` | **Hybrid** | ~20s | Veo (developer) + Remotion (codebase zoom) |
| 1.10 | `10_patch_cycle.md` | **Veo 3.1** | ~10s | Developer sighs, begins another patch |
| 1.11 | `11_codebase_timelapse.md` | Remotion | ~25s | Time-lapse: patches accumulate, comments appear |
| 1.12 | `12_pie_chart.md` | Remotion | ~15s | 80-90% maintenance pie chart |
| 1.13 | `13_pie_to_curve.md` | Remotion | ~10s | Pie morphs to exponential cost curve |

## Tool Distribution

**Remotion (9 sections):** Data visualizations, charts, code abstractions, morphing transitions
**Veo 3.1 (3 sections):** Real people, emotions, physical environments
**Hybrid (1 section):** Composite of video footage and programmatic animation

## Key Narrative Arc

### The Economic Argument (1.1 - 1.5)
- Socks: Darning made sense in 1950, became irrational by 1990
- Code: Generation was expensive for 50 years, AI changed that
- Both lines drop with AI (validating viewer experience with Cursor/Claude Code)

### The Hidden Costs (1.4 - 1.6)
- **Tech Debt:** Each patch leaves residue that compounds
- **Context Rot (NEW):** As codebases grow, AI's context window becomes a "keyhole"
- Net effect: Despite AI speedups, total cost barely improves

### The Crossing Point (1.7)
- Generation is now cheaper than patching + debt
- "We are here" - the economic threshold has been crossed

### The Accumulation Problem (1.8 - 1.13)
- AI tools are "best darning needles ever made"
- But they're still darning needles
- 80-90% of software cost is maintenance
- Costs compound over time

## Context Rot Section (NEW)

The new Section 1.6 addresses a common objection: "But AI makes patching faster!"

**The response:**
1. Yes, AI reduces the immediate cost of each patch (validated)
2. But each patch grows the codebase
3. As the codebase grows, the context window covers less of it
4. AI starts retrieving irrelevant code, making worse suggestions
5. This "context rot" is AI-specific and compounds over time

**Visual metaphor:** A fixed-size "window" over a growing grid of code blocks.
The coverage percentage drops from 80% to 2% as the codebase grows.

## Tool Selection Rationale

### Remotion (Programmatic Animation)
- Charts, graphs, and data visualizations requiring precise positioning
- Mathematical animations with smooth easing
- Code/text overlays and annotations
- Morphing transitions between visualizations
- Abstract/geometric representations
- The context window/grid visualization

### Veo 3.1 (AI Video Generation)
- Realistic footage of people (developer, grandmother)
- Physical environments and objects
- Cinematic shots with natural lighting
- Emotional expressions and body language

## Color Palette (from main script)
- **Prompts/Generate:** Cool blue (#4A90D9)
- **Tests/Walls/Patch:** Warm amber (#D9944A)
- **Context Rot:** Lighter amber with noise (#E8B888)
- **Grounding:** Soft green (#5AAA6E)
- **Generated Code:** Neutral gray with slight blue tint
- **Patched Code:** Warmer gray, accumulates red tint

## Narration Text (Part 1 - Updated)

> This isn't nostalgia. It's economics.
>
> In 1950, a wool sock cost real money relative to an hour of labor. Darning made sense. You'd spend thirty minutes to save a dollar.
>
> By 1990, the math flipped. A new sock cost less than the time to repair the old one. Darning became irrational.
>
> Now look at code.
>
> For fifty years, generating new code was expensive. Writing from scratch took hours, days, weeks. So when something broke, you patched. Of course you patched. It was rational.
>
> And yes—AI made patching faster too. Cursor, Claude Code, Copilot—they're remarkable tools. Look—each patch is getting faster. That's real.
>
> But watch the total cost. It's barely moving. Because every patch still leaves residue. Technical debt. And that debt accumulates.
>
> **[NEW - Context Rot section]**
> And there's something else hiding in that debt. Something specific to AI-assisted development.
>
> When your codebase is small, AI tools are brilliant. The context window covers almost everything.
>
> But codebases grow. And that window stays the same size. Now the AI is looking through a keyhole. It has to guess what's relevant. And increasingly, it guesses wrong.
>
> This is why AI-assisted patching feels great at first and frustrating later. It's not the model getting dumber. It's the ratio getting worse.
>
> Regeneration doesn't have this problem. A single module with a clear prompt? That always fits.
> **[End NEW section]**
>
> The cost to generate just crossed below the cost to patch. And it's far below the true cost—including all that accumulated debt.
>
> Tools like Cursor and Claude Code are the best darning needles ever made. I use them. They're fantastic.
>
> But they're still darning needles.
>
> This is the part of software economics nobody talks about. 80 to 90 percent of software cost isn't building the initial system.
>
> It's maintaining it. Navigating around all the previous patches. Understanding what the last ten developers did and why.
>
> And those costs compound. Unless you regenerate. Then they reset to zero.
