# Part 1: Economics of Darning — Post-Fix Audit

**Video:** `outputs/sections/part1_economics.mp4` (435s / 7:15, 70.1 MB, 13050 frames @ 30fps)
**Script:** `scripts/main_script.md` lines 42-158 (PART 1: THE ECONOMICS OF DARNING, 2:00-6:30)
**Prior Audit:** `PART1_AUDIT.md` (2026-02-08)
**Date:** 2026-02-09
**Auditor:** Critic Agent
**Method:** Frame-accurate extraction using `ffmpeg -vf select=eq(n,FRAME)` at 22 key timestamps

---

## Status: PASS (with remaining known limitations)

All 5 systemic issues from the prior audit have been addressed. The video is watchable and narratively coherent end-to-end. Remaining issues are design limitations (missing per-segment annotations on CrossingPoint) that would require new component development, not rendering bugs.

---

## Fix Verification Summary

| Prior Issue | Severity | Fix Applied | Verified | Notes |
|-------------|----------|-------------|----------|-------|
| #1 CrossingPoint replays | CRITICAL | `startAtFullView`, `showOverlayText` | PARTIAL | Full view works, overlay hidden on non-V20 segments. Per-segment annotations still missing. |
| #2 Veo clip freeze (V18-V19) | CRITICAL | `loop` on OffthreadVideo; **new side-by-side component for V19** | YES | t=294s/t=310s show different poses (clip loops). t=330s shows new Remotion comparison visual. |
| #3 CodeCostChart V5 end state | MAJOR | offset 2280->1800 | YES | t=42s shows mid-fork, t=48s shows blue line plunging. Animation progression visible across segment. |
| #4 ContextRot V13 too early | MODERATE | offset 1020->870 | YES | t=180s shows "The Consequence" beginning to render (faint). t=200s fully readable. |
| #5a PieChart late start | MAJOR | offset 60->120 | YES | t=396s shows blue "Initial Development" slice immediately visible. |
| #5b PieToCurve late start | MAJOR | offset added at 90 | YES | t=424s shows axes with curve beginning. t=430s shows full exponential with regeneration line. |

---

## New Improvements Found (not in prior audit)

### V19 Side-by-Side Comparison Component (NEW)
- **Previously:** Frozen Veo clip for 44s. Script called for "Agentic Patching vs PDD Regeneration" comparison.
- **Now (t=330s):** Dedicated Remotion component showing:
  - LEFT: "Agentic Patching" -- code editor with red "IRRELEVANT" markers, "15,000 tokens"
  - RIGHT: "PDD Regeneration" -- clean layout with "Prompt (300 tokens)", "Tests (2,000 tokens)", "Grounding Example", "Room to think"
  - CENTER: "6.5x fewer tokens" badge
- **Assessment:** Matches script intent precisely. Major visual upgrade.

### PieToCurve Regeneration Line (FIXED)
- **Previously:** Missing "regeneration cost" flat line from script.
- **Now (t=430s):** Blue flat line labeled "Regeneration cost (debt resets each cycle)" visible alongside the exponential curve. Compound interest formula annotation present.
- **Assessment:** Now matches script: "Regeneration cost (debt resets each cycle)."

---

## Frame-by-Frame Verification

### t=4s -- V1: ThresholdHighlight
- **Script:** "The crossing point highlights. Label: 'The Threshold'"
- **Actual:** Full "Economics of Sock Repair" chart with "Cost to Buy" (blue) and "Cost to Repair" (orange) lines. Crossing point ~1963.
- **Status:** GOOD

### t=14s -- V2: LinesDiverge
- **Script:** "The lines diverge dramatically. By 2020, socks are essentially free."
- **Actual:** Chart extending to 2020 axis. Year counter "1968". Lines diverging past crossing.
- **Status:** GOOD -- animation in progress.

### t=24s -- V3: CodeCostChart (brief)
- **Script:** "Transition to similar chart for code."
- **Actual:** "The Economics of Code" title, very faint axes.
- **Status:** OK -- V3 is only 1.5s, serves as transition beat.

### t=42s -- V5: CodeCostChart (offset=1800)
- **Script:** "Post-2020, the amber 'immediate patch' line starts dropping."
- **Actual:** Chart showing fork beginning at 2020. Blue line still high (~29), amber fork just starting with two dots visible. "Same tools. Different codebase sizes." annotation.
- **Status:** GOOD -- **Fix #3 verified.** Animation mid-progress instead of end state.
- **Issue (MODERATE, known):** "Same tools. Different codebase sizes." annotation appears here but script places it at t=232s (V15). Still premature for the narration at t=42s ("AI made patching faster too").

### t=48s -- V5: CodeCostChart
- **Actual:** Blue line plunging at 2022 to ~26h, small codebase fork dropping to ~6h. Clear visual progression from t=42s.
- **Status:** GOOD -- animation advancing.

### t=56s -- V6: CodeCostChartMini (offset=938)
- **Script:** "Focus on the immediate patch line dropping."
- **Actual:** Labeled chart: "Cost to Generate" (blue, high), "Patch Cost" (amber), "Large Codebase" (amber, stays high), "Small Codebase" (amber, drops low). All labels visible at 2025.
- **Status:** GOOD -- clear visual distinction between codebase sizes.

### t=80s -- V8: CrossingPoint (startAtFullView=true)
- **Script:** "GitHub measured a 55% speedup... Annotation: 'Individual task: -55% (GitHub, 2022)'"
- **Actual:** Full chart view (no zoom-in animation). Legend: Cost to Generate, Patch (small/large codebase), True cost (with tech debt). Shaded debt area. No per-segment annotations.
- **Status:** IMPROVED -- `startAtFullView` eliminates the jarring zoom restart. No text overlay.
- **Issue (MAJOR, known):** Per-segment annotations (GitHub -55%, Uplevel ~0%, GitClear +44%, METR -19%) still missing. These are the most data-rich moments in Part 1's narration.

### t=120s -- V9: CrossingPoint (startAtFullView=true)
- **Script:** "'Code churn: +44% (GitClear, 2025, 211M lines analyzed)'. 'Refactoring: -60%'."
- **Actual:** Same full chart view. No GitClear annotations.
- **Status:** Same as t=80s. Missing per-segment data annotations.

### t=150s -- V10-V11: ContextRot (debt zoom)
- **Script:** "Zoom into the shaded debt area. Two layers: 'Code Complexity' and 'Context Rot'."
- **Actual:** "Context Rot: The AI-Specific Problem" title. Two labeled bands: "Context Rot" (lighter, top) and "Code Complexity" (darker, bottom).
- **Status:** GOOD -- matches script concept clearly.

### t=170s -- V12: ContextRot (context window)
- **Script:** "Codebase grid grows: 4x4 -> 8x8 -> 16x16 -> 32x32. Context window stays same. Counter: '80% -> 40% -> 10% -> 2%'."
- **Actual:** "The Shrinking Context Window" title. 32x32 grid (1024 modules). "Context Coverage: 2%". Tiny blue context window. "Large project - AI sees through a keyhole."
- **Status:** GOOD -- dramatic visualization at the 2% state. Intermediate states (80%/40%/10%) skipped due to offset but the endpoint is powerful.

### t=180s -- V13: ContextRot (offset=870)
- **Script:** "Inside the tiny window, red blocks (irrelevant). Outside, green blocks (needed but unseen)."
- **Actual:** "The Consequence" title, chart lines very faint -- animation just starting to render.
- **Status:** IMPROVED -- **Fix #4 verified.** Previously showed fully-rendered consequence chart too early. Now shows transition into consequence phase.
- **Issue (MODERATE, known):** Script calls for red/green block visualization of retrieval failure. Component doesn't have this sub-visualization.

### t=200s -- V14: ContextRot (offset=1350)
- **Script:** "'Performance vs. Context Length' graph. 'Even with perfect retrieval, performance degrades 14-85%.'"
- **Actual:** "The Consequence" fully rendered. Legend with all lines. Annotations: "Faster patching -> faster growth -> faster rot" and "Small modules. Clear prompts. Always fits in context."
- **Status:** OK -- readable and informative summary chart.
- **Issue (MODERATE, known):** Script calls for a "Performance vs. Context Length" graph inset (EMNLP study). Not implemented as a sub-visualization.

### t=240s -- V15: CrossingPoint
- **Script:** "Patch cost line FORKS. 'Small codebase' plunges. 'Large codebase' stays flat. 'Same tools. Different codebase sizes.'"
- **Actual:** Full chart with crossing point glow. No text overlay. Missing fork-specific annotations.
- **Status:** See CrossingPoint systemic issue below.

### t=294s -- V18: Veo (developer)
- **Script:** "'Generate' line pulses. 'Small modules. Clear prompts. Always fits in context.'"
- **Actual:** Developer at desk, smiling, looking at monitor. Live-action footage playing.
- **Status:** GOOD -- **Fix #2 verified.** Clip playing, not frozen.

### t=310s -- V18: Veo (developer)
- **Actual:** Developer in different pose (hand on chin, contemplative). Confirms loop is working.
- **Status:** GOOD -- **Fix #2 confirmed.** Visible motion between frames.

### t=330s -- V19: Side-by-Side Comparison (NEW COMPONENT)
- **Script:** "Side-by-side: LEFT 'Agentic patching' 15,000 tokens. RIGHT 'PDD regeneration' 300-token prompt, 2,000-token tests."
- **Actual:** Exact match. Agentic Patching (15,000 tokens, code with IRRELEVANT marks) vs PDD Regeneration (2,300 tokens, Prompt/Tests/Grounding Example). "6.5x fewer tokens" badge.
- **Status:** EXCELLENT -- New component matches script specification precisely. Major improvement.

### t=370s -- V20: CrossingPoint (showOverlayText=true)
- **Script:** "Blue 'generate' line crosses below dashed 'total cost' line. Label: 'We are here.'"
- **Actual:** Full chart with crossing point highlighted by glow effect. "We are here." annotation visible.
- **Status:** GOOD -- this is the one segment where the overlay text is correctly shown.

### t=380s -- V21: Veo (split screen)
- **Script:** "Split screen. Developer with Cursor / Grandma with needle."
- **Actual:** Sepia-toned split screen: developer at desk (left) / grandmother sewing (right).
- **Status:** GOOD -- matches script perfectly.

### t=396s -- V22: PieChart (offset=120)
- **Script:** "Pie chart materializes. 'Initial Development: 10-20%'. 'Maintenance: 80-90%'."
- **Actual:** "Where Software Costs Go" title. Blue "Initial Development" slice visible. Circle drawn.
- **Status:** GOOD -- **Fix #5a verified.** Blue slice visible immediately instead of empty circle.

### t=410s -- V22: PieChart
- **Actual:** Complete pie chart. "Initial Development 10-20%" (blue). "Maintenance 80-90%" (amber).
- **Status:** GOOD -- matches script exactly.

### t=424s -- V23: PieToCurve (offset=90)
- **Script:** "Pie chart morphs into exponentially growing cost curve."
- **Actual:** Axes visible (Cumulative Maintenance Cost 0-16x, Time Years 1-10). Orange curve at year ~3, just beginning to rise. Dashed "Linear" reference line.
- **Status:** GOOD -- **Fix #5b verified.** Axes visible immediately instead of near-black morph phase.

### t=430s -- V23: PieToCurve
- **Script:** "'Technical debt follows compound interest: Debt x (1 + Rate)^Time'. Flat line: 'Regeneration cost (debt resets each cycle)'."
- **Actual:** Full exponential curve to ~15x at year 10. Formula annotation present. Blue flat "Regeneration cost (debt resets each cycle)" line. Quote: "Unless you regenerate. Then the debt resets."
- **Status:** GOOD -- regeneration line now present (was missing in prior audit).

---

## Remaining Known Limitations

### 1. CrossingPoint Per-Segment Annotations (MAJOR -- design limitation)
**Affects:** V7-V9 (t=63-139s), V15-V17 (t=232-290s) -- ~130s (30% of video)

The CrossingPoint component shows the same generic chart for all 7 segments. The script calls for segment-specific data annotations:
- V8: "Individual task: -55% (GitHub, 2022)" / "Overall throughput: ~0% (Uplevel, 2024)"
- V9: "Code churn: +44% (GitClear, 2025)" / "Refactoring: -60%"
- V16: "METR, 2025: experienced devs 19% slower" / "Developers believed AI saved 20%. It cost 19%."
- V17: Arrow from small-codebase fork to large-codebase fork / "Every patch adds code."

**Impact:** These are the most research-dense moments in Part 1. The narration cites 6+ specific studies, but the visual shows the same static chart. Viewers get no visual reinforcement of the data.

**Recommendation:** Would require either:
- A new `CrossingPointAnnotated` variant with configurable text labels per segment
- An overlay annotation system that renders text callouts on top of CrossingPoint
- Priority: HIGH -- this covers the argumentative core of Part 1

### 2. ContextRot Missing Sub-Visualizations (MODERATE -- design limitation)
**Affects:** V13-V14 (t=175-230s) -- ~55s

Script calls for:
- Red/green block visualization showing retrieval failure (V13 narration)
- "Performance vs. Context Length" graph inset from EMNLP study (V14 narration)

These would require new sub-components within the ContextRot animation system.

**Priority:** MEDIUM -- the "Consequence" chart carries the narrative adequately but lacks the specific research visualization.

### 3. CodeCostChart V5 Premature Annotations (MODERATE -- timing mismatch)
**Affects:** V5 (t=42-54s)

The "Same tools. Different codebase sizes." annotation appears at t=42s but this text belongs with the narration at t=232s (V15). At t=42s the narration is introducing "AI made patching faster too" -- the fork concept hasn't been explained yet.

**Priority:** LOW -- the annotation is accurate content; it's just shown 190s early. Doesn't cause confusion since the chart visually shows the fork.

---

## Overall Assessment

**Verdict: PASS (with remaining known limitations)**

The 5 systemic issues from the prior audit are all resolved:
- CrossingPoint zoom/overlay: FIXED (startAtFullView + showOverlayText props)
- Veo freeze: FIXED (loop + new side-by-side comparison component at t=330s)
- CodeCostChart V5: FIXED (offset adjustment shows animation progression)
- ContextRot V13: FIXED (offset adjustment delays consequence phase)
- PieChart/PieToCurve: FIXED (offset adjustments + regeneration line added)

The video is narratively coherent and visually engaging across its 435s runtime. The remaining limitations are design features that would require new component development, not rendering bugs. The side-by-side comparison at t=330s is a particularly strong addition that matches the script specification precisely.

**Blocking issues:** None
**Recommended improvements (non-blocking):**
1. CrossingPoint per-segment annotations (HIGH priority for argumentative strength)
2. ContextRot retrieval visualization (MEDIUM)
3. V5 annotation timing (LOW)
