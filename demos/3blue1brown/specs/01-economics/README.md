# Part 1: The Economics of Darning (2:00 - 6:30)

This section establishes the economic argument for PDD by drawing a parallel between the economics of sock repair and code maintenance. Total runtime: ~4.5 minutes.

## Section Breakdown

| Section | File | Tool | Duration | Description |
|---------|------|------|----------|-------------|
| 1.1 | `01_sock_price_chart.md` | Remotion | ~20s | Animated line chart: sock cost vs labor over time |
| 1.2 | `02_threshold_highlight.md` | Remotion | ~10s | Highlight the 1960-65 crossing point |
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
- Socks: Darning made sense in 1950, became irrational by mid-1960s
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

## Narration Text (Part 1 - Synced with main_script.md)

> This isn't nostalgia. It's economics.
>
> In 1950, a wool sock cost real money relative to an hour of labor. Darning made sense. You'd spend thirty minutes to save a dollar.
>
> By the mid-1960s, the math flipped. A new sock cost less than the time to repair the old one. Darning became irrational.
>
> Now look at code.
>
> For decades, generating new code was expensive. Writing from scratch took hours, days, weeks. So when something broke, you patched. Of course you patched. It was rational.
>
> Now, here's where it gets interesting. AI made patching faster too. Cursor, Claude Code, Copilot—they're incredible tools. They understand your codebase, suggest fixes, catch bugs before you make them.
>
> Look—each patch is getting faster. That's real. That's what you feel when you use these tools.
>
> But watch the dashed line. The total cost. It's barely moving.
>
> Because even though each patch is faster, every patch still leaves residue. Technical debt. And that debt accumulates—faster now, because you're patching faster.
>
> GitHub measured a fifty-five percent speedup on individual coding tasks. But that was ninety-five developers writing one HTTP server from scratch. A greenfield task—exactly where AI shines.
>
> When Uplevel tracked almost eight hundred developers across real enterprise work for a full year? No change in throughput. Forty-one percent more bugs. The Uplevel team themselves expected to see gains. Their own product manager said: "People are ending up being more reviewers for this code than in the past, and you might have some false faith that the code is doing what you expect."
>
> And GitClear confirmed it across two hundred eleven million lines of code. Since AI coding assistants arrived, code churn is up forty-four percent—new code getting revised within two weeks. Meanwhile, refactoring collapsed by sixty percent. Developers aren't cleaning up. They're piling on.
>
> And there's something else hiding in that debt. Something specific to AI-assisted development.
>
> When your codebase is small, AI tools are brilliant. The context window—what the model can actually see—covers almost everything. It understands how the pieces connect.
>
> But codebases grow. And that window? It stays the same size. A typical enterprise codebase spans millions of tokens. Even the largest context windows hold a fraction of that.
>
> So now the AI has to guess what's relevant. Tools like Cursor use embeddings. Claude Code uses agentic search—grep, file by file. When Jolt AI benchmarked these tools on real codebases like Django and Kubernetes, pure vector search failed to find the right files. Agentic search found more—but took three to five minutes per query.
>
> And here's what makes it worse. A 2025 EMNLP study proved that even when the model retrieves the *right* information, performance still degrades—fourteen to eighty-five percent—just from the sheer length of the input. It's not about finding the right code. The extra tokens themselves hurt the model's ability to reason. A separate Chroma study across eighteen state-of-the-art models confirmed the pattern—they call it *context rot*.
>
> This is why AI-assisted patching is really two stories.
>
> On a small codebase—a few thousand lines—patching with AI is genuinely transformative. The context window covers everything. That's real.
>
> But on a large codebase—the kind you get after years of patching—experienced developers are actually nineteen percent *slower* with AI tools. And here's the devastating part: those same developers *believed* AI was making them twenty percent *faster*. That's a thirty-nine point gap between what it felt like and what happened.
>
> And here's the catch: every patch makes the codebase bigger. So patching pushes you from the world where AI helps into the world where it doesn't.
>
> Regeneration doesn't have this problem. A prompt is a fifth to a tenth the size of the code it governs. So where raw code overwhelms the context window, the *prompts* for ten modules fit comfortably. And the prompt defines its own context—the developer declares exactly what the model needs to see, instead of an agentic tool guessing at what's relevant. No retrieval. No search. No rot.
>
> And there's something else. These models are trained on up to thirty times more natural language than code. Natural language is their deepest fluency. MIT showed that giving models natural language context for coding tasks improved performance by up to eighty-nine percent. A prompt *is* natural language. You're speaking the model's strongest language and giving it room to think.
>
> Research also confirms: modules around two hundred fifty lines have the *lowest* defect density—a U-shaped curve where too small fragments logic and too large explodes complexity. That's exactly the size a focused prompt produces.
>
> Meanwhile, generation just crossed below both lines. The debt doesn't just slow down—it resets. Each regeneration starts clean.
>
> Tools like Cursor and Claude Code are the best darning needles ever made. I use them. They're fantastic.
>
> But they're still darning needles. And the fundamental problem with darning isn't speed—it's accumulation.
>
> This is the part of software economics nobody talks about. Eighty to ninety percent of software cost isn't building the initial system.
>
> It's maintaining it. McKinsey found that organizations with high technical debt spend forty percent more on maintenance and deliver features twenty-five to fifty percent slower. Stripe measured developers wasting a third of their entire work week on technical debt and maintenance.
>
> And those costs compound—literally. Technical debt follows a compound interest curve. Unless you regenerate. Then the debt resets.
