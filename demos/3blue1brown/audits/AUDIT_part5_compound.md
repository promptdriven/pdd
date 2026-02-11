# Part 5: Compound Returns -- Post-Render Audit

**Video:** `outputs/sections/part5_compound.mp4` (87s / 1:27, 2610 frames @ 30fps)
**Script:** `scripts/main_script.md` lines 374-421 (PART 5: COMPOUND RETURNS, 18:00-20:15)
**Composition:** `remotion/src/remotion/S05-CompoundReturns/Part5CompoundReturns.tsx`
**Date:** 2026-02-09
**Auditor:** Critic Agent
**Method:** Frame-accurate extraction using `ffmpeg -vf select=eq(n,FRAME)` at 10 key timestamps

---

## Status: PASS

No blocking issues found. All 8 visual segments render correctly. The CompoundCurvesGraph is the standout component -- it builds progressively across 4 phases (V0-V3) with excellent annotation placement. The InvestmentTable exactly matches the script specification. The closing sequence (sepia Veo + CrossingPoint) effectively bookends the video's economic argument.

---

## Visual Segment Map

| Visual | Component | Time Range | Duration | Status |
|--------|-----------|------------|----------|--------|
| V0 | CompoundCurvesGraph phase 1 | 0.0-1.9s | 1.9s | GOOD |
| V1 | CompoundCurvesGraph phase 2 | 2.7-23.6s | 20.9s | GOOD |
| V2 | CompoundCurvesGraph phase 3 | 24.4-39.4s | 15.0s | GOOD |
| V3 | CompoundCurvesGraph phase 5 | 39.4-52.3s | 12.9s | EXCELLENT |
| V4 | InvestmentTable | 53.9-60.3s | 6.4s | EXCELLENT |
| V5 | Veo: sepia split screen | 62.3-67.7s | 5.4s | GOOD |
| V6 | Veo: sepia split screen | 68.5-73.9s | 5.4s | GOOD |
| V7 | CrossingPoint | 76.4-84.5s | 8.1s | GOOD |

---

## Frame-by-Frame Verification

### t=1s -- V0: CompoundCurvesGraph phase 1
- **Script:** "A graph with two curves. One labeled 'Patching', one labeled 'PDD'. X-axis is time. Y-axis is 'Cumulative Value of Investment'."
- **Actual:** Bare X/Y axes appearing on dark background. Graph frame being set up (animation just starting).
- **Status:** GOOD -- V0 is only 1.9s, establishes the graph canvas before the curves draw.

### t=8s -- V1: CompoundCurvesGraph phase 2
- **Script:** "The 'Patching' curve. Each patch is a point of investment. The return is local -- one bug fixed. The curve grows linearly, then starts to flatten."
- **Actual:** Graph with "Cumulative Value of Investment" (Y-axis), "Time" (X-axis). Legend: "Patching" (orange), "PDD" (blue). Orange patching curve growing sublinearly with dots marking individual patch points. Annotations: "one bug fixed", "local return only". Blue PDD line barely visible at the bottom.
- **Status:** GOOD -- patching curve clearly shows diminishing returns. "one bug fixed" and "local return only" annotations match script narration perfectly.

### t=18s -- V2: CompoundCurvesGraph phase 3 (early)
- **Script:** "The patching curve wobbles, occasionally dips as patches conflict. Small annotations at the dips: 'new bug from patch', 'regression', 'merge conflict'."
- **Actual:** Patching curve extended further right, now showing the full sublinear growth pattern with many more dots. The curve is flattening. Dashed horizontal ceiling line visible. Blue PDD line still near baseline but slightly growing.
- **Status:** GOOD -- shows the progression. Flattening is clearly visible.

### t=30s -- V2: CompoundCurvesGraph phase 3 (complete)
- **Script:** "CISQ estimates technical debt costs US companies one-point-five-two trillion dollars annually."
- **Actual:** Full patching curve with wobbles and dips visible in the later portion. Red annotations: "new bug from patch" (with down-arrow at a dip), "regression" (at another dip). The curve clearly shows sublinear growth with instability. Blue PDD line still near baseline.
- **Status:** GOOD -- "new bug from patch" and "regression" annotations match the script's dip callouts. The dashed ceiling line effectively conveys the diminishing returns concept.
- **Issue (MINOR):** Script also calls for "merge conflict" annotation at one of the dips. Only "new bug from patch" and "regression" are visible.

### t=42s -- V3: CompoundCurvesGraph phase 5
- **Script:** "The PDD curve grows exponentially. Each test contributes to every future generation. The gap between the curves widens dramatically."
- **Actual:** Both curves fully drawn. Orange patching curve sublinear with wobbles. Blue PDD curve now growing exponentially, with individual test-point dots and radiating lines showing each test's compound contribution to future generations. The PDD curve is beginning to cross above the patching curve. Shaded area between curves visible.
- **Status:** EXCELLENT -- the radiating lines from each PDD test point are a brilliant visual innovation. They show how each test's value compounds forward in time, directly illustrating "that test constrains tomorrow's generation, and next week's, and next year's." The gap between curves is dramatic and growing. This is the visual payoff of Part 5.

### t=56s -- V4: InvestmentTable (early)
- **Script:** "Investment table appears: Fix bug -> One place, once / Impossible forever | Improve code -> One version / All future versions | Document behavior -> One snapshot / Living specification"
- **Actual:** Table with columns "Investment", "Return (Patching)", "Return (PDD)". First row visible: "Fix bug" | "One place, once" (orange) | "Impossible forever" (blue). Rows 2-3 not yet animated in.
- **Status:** GOOD -- animation in progress. Row-by-row reveal adds emphasis.

### t=59s -- V4: InvestmentTable (complete)
- **Actual:** All three rows visible:
  - "Fix bug" | "One place, once" | "Impossible forever"
  - "Improve code" | "One version" | "All future versions"
  - "Document behavior" | "One snapshot" | "Living specification"
- **Status:** EXCELLENT -- matches script table specification exactly. Orange/blue color coding for Patching/PDD returns maintains visual continuity with the graph. The contrast between columns is immediately graspable.

### t=65s -- V5: Veo sepia split screen
- **Script:** "Return to the 1950s grandmother and modern person with socks."
- **Actual:** Sepia-toned split screen. LEFT: developer at desk with code on monitor. RIGHT: older person at a workbench/desk with various items. Warm vintage tone.
- **Status:** GOOD -- matches the "grandmother darning / developer patching" parallel from Part 1. Sepia treatment provides nostalgic/reflective tone appropriate for "your great-grandmother wasn't stupid for darning socks."

### t=72s -- V6: Veo sepia split screen (continued)
- **Script:** "And you're not stupid for patching code. Until now, the economics made it rational."
- **Actual:** Same split screen composition. Subtitle overlay: "Until now," visible at bottom center.
- **Status:** GOOD -- the subtitle adds emphasis to the pivotal moment in the narration. The "Until now" text is the hinge between "rational" and "irrational" behavior.

### t=80s -- V7: CrossingPoint
- **Script:** "The economics chart from earlier. The crossing point pulses again."
- **Actual:** "The Economics of Code" chart from Part 1. Lines visible: "Cost to Generate" (blue, dropping), "True cost (with tech debt)" (dashed, rising). Crossing point highlighted with pulsing glow effect. "We are here." annotation at the crossing.
- **Status:** GOOD -- effective callback to Part 1's CrossingPoint. The "We are here." label provides the same anchor point but now with the full context of Parts 2-5 behind it. The pulsing glow draws attention to the crossing.

---

## Issues Summary

| Severity | Count | Description |
|----------|-------|-------------|
| MINOR | 1 | V2 (t=30s): "merge conflict" annotation missing from patching curve dips (only "new bug from patch" and "regression" shown) |

---

## Overall Assessment

Part 5 delivers the compound returns argument effectively. The progressive graph build across 4 phases (V0-V3) is the strongest data visualization technique in the production. Key highlights:

1. **CompoundCurvesGraph phase 5 (V3):** The radiating lines from PDD test points showing compound value over time are visually innovative. This is the best single frame in the entire video for communicating the PDD value proposition. Rated EXCELLENT.

2. **InvestmentTable (V4):** Perfect script match. Three rows, three columns, orange/blue color coding. The row-by-row animation adds emphasis. Rated EXCELLENT.

3. **Patching curve annotations (V2):** "one bug fixed", "local return only", "new bug from patch", "regression" annotations are well-placed and readable. They transform an abstract curve into a concrete narrative.

4. **Sepia Veo + CrossingPoint (V5-V7):** Effective emotional bookend. The grandmother/developer parallel from Part 1 returns with added weight after the full PDD argument.

5. **Pacing:** 8 segments across 87s = ~10.9s average. The graph phases (V0-V3, 52s) get 60% of runtime, appropriate for the most data-rich section.

**Blocking issues:** None
**Recommended improvements (non-blocking):**
1. V2: Add "merge conflict" annotation to patching curve dips (LOW priority -- "new bug from patch" and "regression" already convey the concept)
