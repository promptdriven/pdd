# Part 1: Economics of Darning — Frame-by-Frame Audit

**Video:** `outputs/sections/part1_economics.mp4` (435s, 68.6 MB)
**Method:** Frames extracted every 2s, compared against `scripts/main_script.md`
**Date:** 2026-02-08

---

## Summary of Issues Found

| Severity | Count | Fixed | Description |
|----------|-------|-------|-------------|
| CRITICAL | 2 | 1.5 | Veo clip frozen 65s (FIXED: loop); CrossingPoint overlay text (PARTIALLY FIXED: overlay hidden, zoom skipped; annotations still missing) |
| MAJOR | 7 | 3 | CodeCostChart V5 offset (FIXED); PieChart V22 offset (FIXED); PieToCurve V23 offset (FIXED); remaining: missing per-segment annotations |
| MODERATE | 5 | 1 | ContextRot V13 offset (FIXED); remaining: static charts, incorrect coverage % |
| MINOR | 3 | 0 | Brief black flashes at transitions, missing secondary elements |

---

## Visual Segment Map

| Visual | Component | Time Range | Duration | Notes |
|--------|-----------|------------|----------|-------|
| V0 | SockPriceChart | 0.0–2.7s | 2.7s | |
| V1 | ThresholdHighlight | 3.5–12.0s | 8.5s | |
| V2 | LinesDiverge | 13.4–22.2s | 8.7s | |
| V3 | CodeCostChart | 23.9–25.4s | 1.5s | Very short |
| V4 | AIMilestones | 26.6–39.2s | 12.6s | |
| V5 | CodeCostChart | 40.8–54.7s | 13.9s | offset=2280 |
| V6 | CodeCostChartMini | 55.7–61.5s | 5.8s | offset=938 |
| V7 | CrossingPoint | 63.0–78.1s | 15.1s | |
| V8 | CrossingPoint | 79.2–118.1s | 38.9s | |
| V9 | CrossingPoint | 119.1–139.1s | 20.0s | |
| V10 | ContextRot | 140.7–146.9s | 6.2s | |
| V11 | ContextRot | 148.4–159.6s | 11.2s | offset=240 |
| V12 | ContextRot | 161.4–173.6s | 12.2s | offset=630 |
| V13 | ContextRot | 175.0–199.8s | 24.8s | offset=1020 |
| V14 | ContextRot | 201.2–230.5s | 29.4s | offset=1350 |
| V15 | CrossingPoint | 232.1–248.4s | 16.3s | |
| V16 | CrossingPoint | 249.8–279.0s | 29.3s | |
| V17 | CrossingPoint | 280.2–290.4s | 10.2s | |
| V18 | Veo (developer) | 292.5–319.9s | 27.4s | 8s clip |
| V19 | Veo (developer) | 320.9–365.0s | 44.1s | same 8s clip |
| V20 | CrossingPoint | 366.6–377.3s | 10.7s | |
| V21 | Veo (split screen) | 379.0–392.9s | 13.9s | |
| V22 | PieChart | 394.8–420.4s | 25.5s | offset=60 |
| V23 | PieToCurve | 421.8–432.6s | 10.9s | |

---

## Frame-by-Frame Analysis

### t=0s — Visual 0: SockPriceChart
- **Narration:** "This isn't nostalgia, it's economics."
- **Script visual:** "Price chart animation. 1950: A pair of quality wool socks costs about an hour of wages."
- **Actual:** Nearly black frame. Faint horizontal line barely visible.
- **Issue (MINOR):** Chart animation hasn't started. Viewer sees ~1s of near-darkness before any content appears.

### t=2s — Visual 0: SockPriceChart
- **Narration:** (end of "This isn't nostalgia...")
- **Script visual:** "Graph shows labor cost vs garment cost over time. The lines cross around 1960-65."
- **Actual:** Blue "Cost to Buy" line drawn from 1920 to ~1955. Single line only.
- **Status:** OK — animation in progress, V0 is only 2.7s long.

### t=4s — Visual 1: ThresholdHighlight
- **Narration:** "In 1950, a wool sock cost real money relative to an hour of labor."
- **Script visual:** "The crossing point highlights. Label: 'The Threshold'"
- **Actual:** Full chart with "Cost to Buy" (blue) and "Cost to Repair" (orange) lines. Crossing point ~1963 with "The Threshold" label.
- **Status:** GOOD — matches script.

### t=6s — Visual 1: ThresholdHighlight
- **Narration:** "Darning made sense."
- **Actual:** Same chart, unchanged from t=4s.
- **Status:** OK — static but acceptable during narration setup.

### t=8s — Visual 1: ThresholdHighlight
- **Narration:** "You'd spend thirty minutes to save a dollar."
- **Actual:** Same chart, unchanged.
- **Status:** OK — static.

### t=10s — Visual 1: ThresholdHighlight
- **Narration:** (continuing)
- **Actual:** Same chart, unchanged for 6+ seconds.
- **Status:** OK — static but narration carries interest.

### t=12s — Visual 1: ThresholdHighlight
- **Narration:** "Darning made sense. You'd spend thirty minutes to save a dollar."
- **Actual:** Chart with quote overlay: *"Darning made sense. You'd spend thirty minutes to save a dollar."*
- **Status:** GOOD — quote overlay adds engagement.

### t=14s — Visual 2: LinesDiverge
- **Narration:** "By the mid-1960s, the math flipped."
- **Script visual:** "The lines diverge dramatically. By 2020, socks are essentially free relative to labor."
- **Actual:** Chart extends to 2020 x-axis. Year counter shows "1968". Lines beginning to diverge past crossing point.
- **Status:** GOOD — year counter animating, lines diverging.

### t=16s — Visual 2: LinesDiverge
- **Narration:** "A new sock cost less than the time to repair the old one."
- **Actual:** Year counter "1981", blue line extending, gap widening.
- **Status:** GOOD — animation progressing well.

### t=18s — Visual 2: LinesDiverge
- **Narration:** "Darning became irrational."
- **Actual:** Year counter "1993", shaded area between diverging lines.
- **Status:** GOOD.

### t=20s — Visual 2: LinesDiverge
- **Narration:** (end of sock economics section)
- **Actual:** Year counter "2005", "Darning is irrational" label, "$0.48/h saved" annotation, large shaded area.
- **Status:** GOOD — strong visual payoff.

### t=22s — Visual 2: LinesDiverge
- **Narration:** (transition)
- **Actual:** Year counter "2017", chart near completion.
- **Status:** GOOD.

### t=24s — Visual 3: CodeCostChart
- **Narration:** "Now look at code."
- **Script visual:** "Transition to a similar chart for code. Y-axis: 'Cost (Developer Hours)'. Three elements: blue 'Cost to generate', amber 'Immediate patch cost', dashed amber 'Total cost (with debt)'."
- **Actual:** "The Economics of Code" title. Axes barely visible (extremely faint). Essentially empty chart.
- **Issue (MINOR):** V3 is only 1.5s long. The CodeCostChart animation takes 18s just to draw axes. With offset=540 (from the Sequence from={-540}), the chart shows axes fading in. Acceptable as a transition beat but feels empty.

### t=26s — Visual 3→4 gap / Visual 4: AIMilestones
- **Narration:** "For decades, generating new code was expensive."
- **Script visual:** "Key dates appear on the falling 'generate' line: Codex, GPT-4, Claude, Gemini. The line barely dips at Codex."
- **Actual:** "The Economics of Code" with visible axes (0-35 Cost Developer Hours, 2015-2025). No lines drawn yet.
- **Issue (MODERATE):** At t=26s we're in the gap between V3 (ends 25.44s) and V4 (starts 26.6s). The viewer sees empty CodeCostChart axes for ~1s. Then AIMilestones takes over but starts with empty axes too.

### t=28s — Visual 4: AIMilestones
- **Narration:** "Writing from scratch took hours, days, weeks."
- **Actual:** "AI Milestones: The Acceleration" title, empty chart (2020-2025, 0-35). No lines drawn yet.
- **Issue (MODERATE):** Animation is at its very beginning — just empty axes. Narration is already describing how expensive code generation was, but we see no data yet. Takes ~2s to start drawing.

### t=30s — Visual 4: AIMilestones
- **Narration:** "So when something broke, you patched."
- **Actual:** Blue line with "Codex / Copilot" milestone marker at 2021. Line shows cost dropping from ~30 to ~28.
- **Status:** GOOD — first milestone appearing.

### t=32s — Visual 4: AIMilestones
- **Narration:** "Of course you patched. It was rational."
- **Actual:** Blue line with Codex/Copilot, purple dot appearing at 2023 (GPT-4).
- **Status:** GOOD.

### t=34s — Visual 4: AIMilestones
- **Narration:** (continuation)
- **Actual:** Blue line with Codex/Copilot and labeled "GPT-4" at 2023. Line plunges steeply.
- **Status:** GOOD — matches "barely dips at Codex, then plunges steeply starting at GPT-4/Claude."

### t=36s — Visual 4: AIMilestones
- **Narration:** (continuation)
- **Actual:** All three milestones: Codex/Copilot, GPT-4, Claude 3.5 Sonnet. Line drops to ~7.
- **Status:** GOOD.

### t=38s — Visual 4: AIMilestones
- **Narration:** (continuation)
- **Actual:** Fourth milestone appearing (unlabeled dot at 2025), plus "Claude 3.5 Sonnet" label. Line near bottom.
- **Status:** GOOD.

### t=40s — Visual 4→5 transition
- **Narration:** "Now here's where it gets interesting."
- **Actual:** AIMilestones showing all labels including "Claude 3.7 Sonnet" at 2025.
- **Status:** OK — brief transition, V5 starts at 40.78s.

### t=42s — Visual 5: CodeCostChart (offset=2280)
- **Narration:** "AI made patching faster too."
- **Script visual:** "Post-2020, the amber 'immediate patch' line starts dropping as Copilot helps with fixes. The blue 'generate' line barely moves until 2023—then GPT-4 and Claude arrive, and it plunges."
- **Actual:** FULLY COMPLETED chart showing: blue "Cost to Generate" line, amber "Patch Cost" forked into "Small Codebase" and "Large Codebase", dashed "True cost" line, large shaded debt area, annotations "Same tools. Different codebase sizes." and "Every patch adds code."
- **Issue (MAJOR):** The frameOffset=2280 jumps to the END of the 120s CodeCostChart animation. ALL annotations are pre-loaded — including "Same tools. Different codebase sizes." and fork labels that belong to the narration at t=232s+ (V15-V17). At t=42s, the narration is just introducing "AI made patching faster" — the chart should show the fork BEGINNING to form, not the completed state with all future annotations.

### t=44s–54s — Visual 5: CodeCostChart (offset=2280)
- **Narration:** "Cursor, Claude, Copilot. They're incredible tools. They understand your codebase. Suggest fixes, catch bugs."
- **Script visual:** Progressive animation of patch cost dropping, AI tools accelerating fixes.
- **Actual:** Completely static. Same fully-drawn chart as t=42s for 14 straight seconds.
- **Issue (MAJOR):** Zero animation for the entire 14s segment. The narration describes an evolving story of AI tools making patching faster, but the visual is frozen at the end state. Should show progressive animation: amber line beginning to fork, blue line starting to plunge.

### t=56s — Visual 6: CodeCostChartMini (offset=938)
- **Narration:** "Look, each patch is getting faster."
- **Script visual:** "Focus on the immediate patch line dropping. This is the viewer's lived experience. Validate it."
- **Actual:** Clean chart titled "The Economics of Code" with labeled lines: "Cost to Generate" (blue, high), "Patch Cost" (amber), "Large Codebase" (amber, high), "Small Codebase" (amber, low). No dashed line.
- **Status:** OK — labeled chart shows the concept clearly. Not much animation visible but lines are distinct.

### t=58s–60s — Visual 6: CodeCostChartMini
- **Narration:** "That's real. That's what you feel when you use these tools."
- **Actual:** Same chart, appears static.
- **Issue (MODERATE):** Minimal animation visible across the 6s segment. The highlight on the patch line dropping (HIGHLIGHT_PATCH_START at frame 938) should be more prominent.

### t=62s — Visual 6→7 gap
- **Narration:** (transition to "But watch the dashed line")
- **Actual:** CodeCostChartMini chart still displayed.
- **Status:** OK — brief gap.

### t=64s — Visual 7: CrossingPoint
- **Narration:** "But watch the dashed line. The total cost. It's barely moving."
- **Script visual:** "Camera pulls back. As the immediate line drops, the shaded debt area EXPANDS upward. The dashed 'total cost' line at the top barely moves."
- **Actual:** CrossingPoint chart zoomed in — axis labels cut off, y-axis numbers not visible. Legend visible: Cost to Generate, Patch (small/large codebase), True cost (with tech debt).
- **Issue (MODERATE):** Chart axes are clipped. Animation is just starting (reset from beginning).

### t=66s — Visual 7: CrossingPoint
- **Narration:** "Because even though each patch is faster..."
- **Actual:** Full chart visible with axes (2015-2025, 0h-35h), "We are here" crossing point marker.
- **Status:** OK — chart readable now.

### t=68s–70s — Visual 7: CrossingPoint
- **Narration:** "every patch still leaves residue. Technical debt."
- **Actual:** Chart with "We are here." annotation.
- **Status:** OK.

### t=72s–76s — Visual 7: CrossingPoint
- **Narration:** "And that debt accumulates—faster now, because you're patching faster."
- **Actual:** Chart with text overlay: *"But look where we are now. The cost to generate a module just crossed below the total cost of patching one — on any real-world codebase. And they're still moving apart."*
- **Issue (MAJOR):** This text overlay belongs to the narration at t=366s (V20: "generation just crossed below both lines"). At t=72s the narration is about debt accumulating, NOT about generation crossing below patching. The CrossingPoint component's internal timeline doesn't match the section's narration context.

### t=80s — Visual 8: CrossingPoint (RESTART)
- **Narration:** "GitHub measured a fifty-five percent speedup on individual coding tasks."
- **Script visual:** "Annotation appears: 'Individual task: -55% (GitHub, 2022)' pointing to the dropping solid line. Fine print: '95 developers, one greenfield task'. Another: 'Overall throughput: ~0% (Uplevel, 2024)' pointing to the nearly-flat dashed line."
- **Actual:** Chart zoomed in, axis labels cut off. Animation has RESTARTED from the beginning — all annotations from V7 are gone.
- **Issue (CRITICAL — part of systemic CrossingPoint problem):** The CrossingPoint component restarts its 10s animation from frame 0 every time the activeVisual switches. V8 spans 39s but shows the same 10s loop. Missing ALL script-specified annotations: GitHub -55%, Uplevel ~0%, 41% more bugs.

### t=90s–110s — Visual 8: CrossingPoint
- **Narration:** Covers Uplevel study (785 developers, 41% more bugs), product manager quote.
- **Actual:** Same chart with generic "We are here." + text overlay about generation crossing patching cost.
- **Issue (CRITICAL):** Static for 30+ seconds. Wrong text overlay (about generation cost, not about GitHub/Uplevel data). Missing specific data annotations from script. The CrossingPoint component has no mechanism to display segment-specific annotations.

### t=120s — Visual 9: CrossingPoint (RESTART)
- **Narration:** "And GitClear confirmed it across 211 million lines of code."
- **Script visual:** "New annotation: 'Code churn: +44% (GitClear, 2025, 211M lines analyzed)'. Another: 'Refactoring: -60%'."
- **Actual:** Chart zoomed in, axis labels cut off. Animation RESTARTED again from beginning.
- **Issue (CRITICAL — same systemic problem):** Third CrossingPoint restart. Missing GitClear annotations. Same 10s animation playing for the third time.

### t=130s–140s — Visual 9: CrossingPoint
- **Narration:** "code churn is up 44%... refactoring collapsed by 60%... They're piling on."
- **Actual:** Same generic chart with "We are here." text overlay.
- **Issue:** Same static chart. No GitClear-specific annotations visible.

### t=142s — Visual 10: ContextRot
- **Narration:** "And there's something else hiding in that debt."
- **Script visual:** "Zoom into the shaded debt area. It separates into two distinct layers: a darker 'Code Complexity' layer and a lighter 'Context Rot' layer."
- **Actual:** (Not individually sampled — between t=140s and t=150s)
- **Status:** Based on t=150s, the debt zoom phase appears correctly.

### t=150s — Visual 11: ContextRot (offset=240)
- **Narration:** "When your codebase is small, AI tools are brilliant."
- **Script visual:** "A glowing rectangular 'context window' appears over a small codebase represented as a 4x4 grid of code blocks. The window covers most of the grid (~80%)."
- **Actual:** "The Shrinking Context Window" title. 5x5 grid (25 modules). Context Coverage: 48%. Blue context window covers about half the grid.
- **Issue (MODERATE):** Script says 4x4 grid with ~80% coverage. Actual shows 5x5 grid with 48% coverage. The "AI covers almost everything" narration is contradicted by showing only 48% coverage. Should start at ~80% to match "covers almost everything."

### t=160s — Visual 11→12 transition
- **Narration:** "But codebases grow. And that window stays the same size."
- **Actual:** Transitioning between ContextRot segments.
- **Status:** OK.

### t=170s — Visual 12: ContextRot (offset=630)
- **Narration:** "A typical enterprise codebase spans millions of tokens."
- **Script visual:** "The codebase grid grows: 4x4 → 8x8 → 16x16 → 32x32. Context window stays same. Counter: '80% → 40% → 10% → 2%'."
- **Actual:** 32x32 grid (1024 modules). "Context Coverage: 2%". "Large project - AI sees through a keyhole." Tiny blue window over massive grid.
- **Status:** GOOD — dramatic visual of context window shrinking. Matches "2%" from script's progression. The jump from 48% to 2% is due to the frame offset skipping the intermediate stages.

### t=180s — Visual 13: ContextRot (offset=1020)
- **Narration:** "Tools like Cursor use embeddings. Claude Code uses agentic search."
- **Script visual:** "Inside the tiny window, some blocks highlighted red—irrelevant code. Outside, green blocks show needed code that couldn't be seen."
- **Actual:** "The Consequence" chart showing cost lines with "Faster patching = faster growth = faster rot" annotation. Also "Regeneration: always starts small, always fits" label.
- **Issue (MODERATE):** The animation has jumped to the "Consequence" phase (Part 3 of ContextRot's 45s timeline) which shows the summary chart. But the narration is still describing the MECHANISM (embeddings, agentic search, vector search failure) — not yet the consequence. Script calls for red/green highlighted blocks showing retrieval failure, which is not rendered.

### t=190s — Visual 13: ContextRot
- **Narration:** "Agentic search found more—but took three to five minutes per query."
- **Actual:** Same "The Consequence" chart.
- **Issue:** Same — consequence chart displayed during mechanism narration.

### t=200s — Visual 14: ContextRot (offset=1350)
- **Narration:** "And here's what makes it worse. A 2025 EMNLP study proved..."
- **Script visual:** "A subtle graph inset: 'Performance vs. Context Length'. Line drops steadily. Label: 'Even with perfect retrieval, performance degrades 14-85% as context grows (EMNLP, 2025)'."
- **Actual:** Same "The Consequence" chart with same annotations.
- **Issue (MAJOR):** Script calls for a "Performance vs. Context Length" graph inset showing degradation. Not present. The ContextRot component doesn't have this sub-visualization. Same static chart continues.

### t=210s–230s — Visual 14: ContextRot
- **Narration:** "It's not about finding the right code. The extra tokens themselves hurt... A separate Chroma study... they call it context rot."
- **Actual:** Same "The Consequence" chart, completely static for 30 seconds.
- **Issue (MODERATE):** Static for 30s. Missing "context rot" specific annotation and the EMNLP performance graph. The narration covers 3 distinct research findings but the visual doesn't change.

### t=232s — Visual 14→15 transition
- **Narration:** "This is why AI-assisted patching is really two stories."
- **Actual:** Still showing "The Consequence" chart from ContextRot V14.
- **Status:** OK — transitioning to CrossingPoint V15 at 232.12s.

### t=240s — Visual 15: CrossingPoint
- **Narration:** "On a small codebase... patching with AI is genuinely transformative."
- **Script visual:** "The immediate patch cost line FORKS into two paths at 2020. Lower path labeled 'Small codebase' plunges down. Upper path labeled 'Large codebase' stays flat. Annotation: 'Same tools. Different codebase sizes.'"
- **Actual:** CrossingPoint chart with "We are here." annotation and text overlay.
- **Issue (MAJOR):** Same generic CrossingPoint animation — 4th time replaying. Missing the specific fork visualization and "Same tools. Different codebase sizes." annotation that belongs HERE (not at t=42s where it incorrectly appeared on CodeCostChart V5).

### t=250s — Visual 16: CrossingPoint (RESTART)
- **Narration:** "But on a large codebase... experienced developers are actually 19% slower."
- **Script visual:** "Focus on the upper fork. Small annotation: 'METR, 2025: experienced devs 19% slower on mature repos'. Then: 'Developers believed AI saved 20%. It cost 19%.'"
- **Actual:** Chart zoomed in, axis labels cut off. Animation restarted from beginning.
- **Issue (CRITICAL):** 5th CrossingPoint replay. Missing METR data annotations, perception gap annotation.

### t=260s–270s — Visual 16: CrossingPoint
- **Narration:** "That's a 39-point gap between what it felt like and what happened."
- **Actual:** Same generic chart with "We are here." text overlay.
- **Issue:** Missing "39-point perception gap" annotation. Static.

### t=280s — Visual 17: CrossingPoint (RESTART)
- **Narration:** "And here's the catch. Every patch makes the codebase bigger."
- **Script visual:** "Arrow from small-codebase fork curving upward toward large-codebase fork. Label: 'Every patch adds code.'"
- **Actual:** Same chart. Animation restarted. 6th CrossingPoint replay.
- **Issue (CRITICAL):** Missing arrow annotation. Same generic chart.

### t=290s — Visual 17: CrossingPoint
- **Narration:** "So patching pushes you from the world where AI helps into the world where it doesn't."
- **Actual:** Same chart, static.
- **Status:** End of CrossingPoint run.

### t=294s — Visual 18: Veo clip (veo_developer_edit.mp4)
- **Narration:** "Regeneration doesn't have this problem."
- **Script visual:** "The 'Generate' line pulses with emphasis. Small annotation: 'Small modules. Clear prompts. Always fits in context.'"
- **Actual:** Developer at desk, smiling, looking at monitor. Live-action footage.
- **Status:** OK — Veo footage plays, provides visual variety. Script called for chart annotation but Veo clip was chosen instead.

### t=300s — Visual 18: Veo clip
- **Narration:** "The prompts for ten modules fit comfortably."
- **Actual:** Developer at desk, close-up, different expression (thoughtful, hand on chin).
- **Status:** OK — clip appears to still be playing.

### t=310s — Visual 18: Veo clip
- **Narration:** "The developer declares exactly what the model needs to see."
- **Actual:** Developer at desk — appears nearly identical to t=300s.
- **Issue (MODERATE):** The ~8s Veo clip has likely reached its end. Frame is frozen or near-frozen.

### t=320s — Visual 19: Veo clip (SAME veo_developer_edit.mp4)
- **Narration:** "And there's something else."
- **Script visual:** "Side-by-side comparison. LEFT: 'Agentic patching' — context window filled with 15,000 tokens. RIGHT: 'PDD regeneration' — context window with 300-token prompt."
- **Actual:** Developer at desk — identical frozen frame from t=310s.
- **Issue (CRITICAL):** The same 8s Veo clip is reused for V19 (44s segment). It has already completed playback, so the frame is FROZEN. Script calls for a detailed side-by-side comparison visualization that doesn't exist. This frozen frame persists for 45+ seconds.

### t=330s–360s — Visual 19: Veo clip (FROZEN)
- **Narration:** Covers: models trained on 30x more NL than code; natural language is deepest fluency; MIT study (+89%); 250 lines optimal; U-shaped defect curve.
- **Actual:** Same frozen developer frame for all 30+ seconds.
- **Issue (CRITICAL):** 65+ seconds of frozen video total (from ~t=306s to t=366s). This is the longest stretch of narration covering the most research findings (MIT NL study, 250-line optimal modules, U-shaped defect curve) with ZERO visual variation. Script calls for specific visualizations that don't exist.

### t=370s — Visual 20: CrossingPoint
- **Narration:** "Meanwhile, generation just crossed below both lines."
- **Script visual:** "The blue 'generate' line crosses below the dashed 'total cost' line. Then keeps going, crossing below even the solid 'immediate' line. Label: 'We are here.'"
- **Actual:** Full CrossingPoint chart with axes, all lines visible, "We are here." crossing point marker.
- **Status:** OK — chart is readable and shows the crossing point. The animation's "We are here." annotation actually matches this narration segment (unlike V7-V9 and V15-V17 where it was wrong).

### t=380s — Visual 21: Veo clip (07_split_screen_sepia.mp4)
- **Narration:** "Tools like Cursor and Claude Code are the best darning needles ever made."
- **Script visual:** "Split screen. Developer with Cursor / Grandma with needle."
- **Actual:** Split screen — developer at desk (left) / grandmother sewing (right) in sepia tone.
- **Status:** GOOD — matches script perfectly.

### t=390s — Visual 21: Veo clip
- **Narration:** "But they're still darning needles. And the fundamental problem... isn't speed—it's accumulation."
- **Actual:** Similar split screen, slightly different angles — clip still playing.
- **Status:** GOOD.

### t=396s — Visual 22: PieChart (offset=60)
- **Narration:** "This is the part of software economics nobody talks about."
- **Script visual:** "Pie chart materializes. 'Initial Development: 10-20%'. 'Maintenance: 80-90%'."
- **Actual:** "Where Software Costs Go" title with empty circle outline. No slices visible yet.
- **Issue (MAJOR):** With offset=60 (2s), the pie chart shows only an empty circle for the first ~4s. Narration says "80 to 90 percent of software cost isn't building" but the chart hasn't drawn any slices yet.

### t=400s — Visual 22: PieChart
- **Narration:** "It's maintaining it."
- **Actual:** Pie chart partially drawn — "Initial Development" label visible, blue and amber slices growing.
- **Status:** OK — animation in progress.

### t=410s — Visual 22: PieChart
- **Narration:** "McKinsey found... 40% more on maintenance."
- **Actual:** Complete pie chart: "Initial Development 10-20%", "Maintenance 80-90%".
- **Status:** GOOD — matches script exactly.

### t=420s — Visual 22: PieChart
- **Narration:** "Stripe measured developers wasting a third of their entire work week."
- **Actual:** Same pie chart, static.
- **Status:** OK — static but acceptable, narration carries it.

### t=424s — Visual 23: PieToCurve
- **Narration:** "And those costs compound—literally."
- **Script visual:** "The pie chart morphs into an exponentially growing cost curve labeled 'Technical debt follows compound interest: Debt x (1 + Rate)^Time'. A second, flat line appears: 'Regeneration cost (debt resets each cycle)'."
- **Actual:** Nearly completely black/dark screen with tiny element in bottom-left corner.
- **Issue (MAJOR):** The PieToCurve animation starts with a morphing transition that is nearly invisible. Viewer sees ~4s of near-black before the curve appears.

### t=430s — Visual 23: PieToCurve
- **Narration:** "Technical debt follows a compound interest curve."
- **Actual:** Exponential curve visible: "Cumulative Maintenance Cost" (y-axis, 0-16x), "Time (Years 1-10)" (x-axis). Orange curve rising steeply. Dashed "Linear" reference line at bottom.
- **Status:** GOOD — curve matches script's "compound interest" concept.
- **Issue (MINOR):** Script calls for a second flat "Regeneration cost" line showing debt resets. Only the linear reference line is present — not labeled as regeneration.

### t=434s — Visual 23: PieToCurve (final frame)
- **Narration:** "Unless you regenerate. Then the debt resets."
- **Actual:** Same curve with quote overlay: *"And those costs compound."*
- **Issue (MINOR):** Missing "regeneration cost" flat line from script. The visual shows compound growth but not the contrast with regeneration's flat cost.

---

## Systemic Issues

### 1. CrossingPoint Component Replays (CRITICAL) — PARTIALLY FIXED
**Affects:** V7, V8, V9, V15, V16, V17, V20 — 7 segments totaling ~160s (37% of video)

**Fixes applied:**
- [x] Added `showOverlayText` prop (default false) — text overlay only shows for V20
- [x] Added `startAtFullView` prop — V8, V9, V16, V17 skip 2s zoom-out animation
- [x] Generator passes per-entry extra props via 6th tuple element

**Remaining (not yet addressed):**
- Per-segment annotations (GitHub -55%, Uplevel 0%, GitClear +44%, METR -19%) still missing
- Fork highlighting and arrow annotations not implemented
- Would require new sub-components or a more complex variant system

### 2. Veo Clip Freeze (CRITICAL) — FIXED
**Affects:** V18+V19 — 71.5s (16% of video)

**Fix applied:**
- [x] Added `loop` prop to all `<OffthreadVideo>` elements in generator
- Veo clips now loop instead of freezing on last frame

**Remaining:** V19 still uses the same `veo_developer_edit.mp4` clip as V18. Script calls for a side-by-side comparison visualization. Would need a dedicated Remotion component.

### 3. CodeCostChart V5 Shows End State (MAJOR) — FIXED
**Affects:** V5 — 13.9s

**Fix applied:**
- [x] Reduced frameOffset from 2280 to 1800
- Now starts mid-fork drawing phase, showing visible animation progression over the 14s segment

### 4. ContextRot Consequence Phase Too Early (MODERATE) — FIXED
**Affects:** V13 — 24.8s

**Fix applied:**
- [x] Reduced V13 offset from 1020 to 870
- Keeps the mechanism visualization active longer before transitioning to consequences

### 5. PieChart/PieToCurve Late Animations (MAJOR) — FIXED
**Affects:** V22 first 4s, V23 first 6s

**Fixes applied:**
- [x] PieChart offset increased from 60 to 120 — skips FADE_OUT + BASE_APPEAR, starts with blue segment visible
- [x] PieToCurve offset added at 90 — skips MORPH phase (pie shrinks to nothing), starts at AXES phase
