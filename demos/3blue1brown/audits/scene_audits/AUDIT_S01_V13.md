# Scene Audit: S01 V13 - ContextRot (retrieval failure / agentic search)

**Section:** S01 Part 1 Economics
**Scene:** V13 - ContextRot
**Video:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/outputs/sections/part1_economics.mp4`
**Time range:** 174.98s - 199.76s (24.78s duration)
**Auditor:** Claude Opus 4.6
**Date:** 2026-02-09

---

## Script Requirements

**Visual description:** "Inside the tiny window, some blocks are highlighted red -- irrelevant code that the AI grabbed. Outside the window, green-highlighted blocks show the code that was actually needed but couldn't be seen."

**Narration:** "So now the AI has to guess what's relevant. Tools like Cursor use embeddings. Claude Code uses agentic search -- grep, file by file. When Jolt AI benchmarked these tools on real codebases like Django and Kubernetes, pure vector search failed to find the right files. Agentic search found more -- but took three to five minutes per query."

---

## Frame-by-Frame Analysis

### Internal frame mapping

The ContextRot component is rendered with a Remotion `Sequence from={-870}` offset, meaning V13's local frame 0 maps to ContextRot internal frame 870. Key ContextRot phase boundaries:

| ContextRot Phase | Internal Frames | V13 Time (approx) |
|---|---|---|
| Part 2 (large codebase grid, tail) | 870-900 | 0s - 1s |
| Part 2b (InGridMismatch) | 900-1020 | 1s - 5s |
| Part 3 (The Consequence chart) | 1020-1350+ | 5s - 25s |

### Frame at t=176s (1.0s into V13, ContextRot frame ~901)

**Expected:** Red/green block grid visualization showing retrieval mismatch (InGridMismatch just starting).

**Observed:** Very faint, mostly dark screen. Title "The Context Mismatch Problem" is visible at the top but nearly invisible. A very faint grid of blocks is barely perceptible in the center. The InGridMismatch component has just begun its `fadeInOpacity` animation (interpolating from frame 900 to 945), so at frame 901 it is approximately 2% opacity. The content is effectively invisible.

**Verdict:** ISSUE -- The InGridMismatch fade-in begins at frame 900 and takes 45 frames (1.5s) to reach full opacity. At t=176s the visualization is functionally invisible. This was noted in the section-level audit as "just starting to render (faint)" at t=180s. The narration is already running about AI guessing relevance while the viewer sees essentially a blank dark screen.

### Frame at t=185s (10.0s into V13, ContextRot frame ~1171)

**Expected:** Red/green block visualization still showing the retrieval mismatch, matching the ongoing narration about vector search failure and agentic search.

**Observed:** "The Consequence" chart is displayed, showing cost lines from 2015-2025 with a tan/amber "Context Rot" shaded area. The chart includes legend entries for "Cost to Generate," "Patch (Small CB)," "Patch (Large CB)," "True Cost (with tech debt)," and "Context Rot." The annotation "Faster patching -> faster growth -> faster rot" is visible in the center-right. No red/green blocks anywhere.

**Verdict:** MISMATCH -- The chart is being shown instead of the red/green block visualization. This is the known design limitation (see below). The narration is specifically discussing Cursor embeddings, Claude Code's agentic grep search, and Jolt AI benchmarks on Django/Kubernetes -- none of which relates to the "Consequence" chart being displayed.

### Frame at t=195s (20.0s into V13, ContextRot frame ~1471)

**Expected:** Continued retrieval failure visualization or transition.

**Observed:** Same "The Consequence" chart, now also showing a second annotation at the bottom-left: "Small modules. Clear prompts. Always fits in context." This is the SETUP_SOLUTION phase text (frame >= 1140). Both annotations are visible simultaneously.

**Verdict:** MISMATCH -- The chart annotations about solution setup ("Small modules. Clear prompts.") appear during narration about benchmarking retrieval tools, which is a content mismatch. The visual is jumping ahead to the PDD solution teaser while the narration is still diagnosing the retrieval problem.

### Frame at t=199s (24.0s into V13, ContextRot frame ~1591)

**Expected:** End of retrieval failure section, possible transition.

**Observed:** Identical to t=195s. Same chart with both annotations visible. No visual change or transition evident.

**Verdict:** MISMATCH -- Static chart persists. Visual and narration remain out of sync.

---

## Known Design Limitation (Pre-identified)

**Severity:** MODERATE

The section-level audit previously identified this issue:

> "Script calls for red/green block visualization of retrieval failure. Component shows 'The Consequence' chart instead."

**Root cause analysis:** The ContextRot component is a 45-second (1350-frame) animation divided into three phases. V13 is mapped to start at internal frame 870, which gives it only ~30 frames (1 second) of the InGridMismatch phase (frames 900-1020) before transitioning to "The Consequence" chart (frame 1020+). The InGridMismatch fade-in alone takes 45 frames, so the red/green block visualization never reaches full opacity within V13's allocation. By the time V13's narration about retrieval tools begins in earnest (~2-3 seconds in), the component has already transitioned to the chart.

The InGridMismatch component *does* implement the spec-compliant visualization with:
- Red-bordered blocks inside the context window (irrelevant code grabbed)
- Green-bordered blocks outside the context window (needed code missed)
- A legend explaining both
- An "explanation callout" panel

However, V13's frame offset (`-870`) allocates virtually none of V13's duration to this phase. The bulk of V13 (>80% of its 24.78s) shows "The Consequence" chart instead.

---

## Summary

| Check | Result | Notes |
|---|---|---|
| Red blocks inside window (irrelevant code) | FAIL | InGridMismatch fades in too slowly; transitions to chart after ~1s |
| Green blocks outside window (needed code) | FAIL | Same -- never reaches visible state within V13 |
| Narration-visual sync | FAIL | Narration discusses retrieval tools; visual shows cost chart |
| Visual quality/rendering | PASS | Chart itself renders cleanly with proper labels and legend |
| Transitions | PARTIAL | Transition from grid to chart happens, but is premature |

---

## Overall Verdict: NEEDS_FIX

**Severity: HIGH**

The core issue is a timing/offset problem. The InGridMismatch visualization (which correctly implements the red/green block spec) is allocated approximately 1 second of screen time within V13, and even that 1 second is spent fading in from 0% opacity. The remaining ~24 seconds of V13 show "The Consequence" chart, which belongs to a different narrative segment. The narration about vector search, agentic search, Jolt AI benchmarks, Django, and Kubernetes has no corresponding visual support.

**Recommended fixes (in priority order):**

1. **Adjust the ContextRot frame offset for V13** from `-870` to approximately `-600` to `-630`, which would position V13's start at ContextRot frame 600-630 (mid-codebase-growth) and allow the InGridMismatch phase (frames 900-1020) to occupy the middle portion of V13 where the retrieval narration occurs.

2. **Alternatively, extend the InGridMismatch phase** by changing `SPLIT_VIEW_END` and `RETURN_TO_CHART_START` so the red/green block visualization persists longer (perhaps 240+ frames instead of 120), giving V13 adequate time to show it.

3. **Consider splitting V13 into its own sub-component** that directly shows the retrieval mismatch for the full 24.78s duration, rather than sharing the monolithic ContextRot timeline with V10-V14.
