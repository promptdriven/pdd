# Scene Audit: S01 V6 - CodeCostChartMini

**Section:** S01 Part 1 Economics
**Scene:** V6 - CodeCostChartMini
**Video:** `outputs/sections/part1_economics.mp4`
**Time range:** 55.7s - 61.46s (5.76s duration)
**Frames extracted:** t=56s, t=59s, t=61s
**Verdict:** PASS

---

## Script Alignment

**Script visual description:** "Focus on the immediate patch line dropping. This is the viewer's lived experience. Validate it."
**Script narration:** "Look -- each patch is getting faster. That's real. That's what you feel when you use these tools."

---

## Timing Analysis

The section composition mounts CodeCostChartMini with `<Sequence from={-938}>`, offsetting so that internal frame 938 (HIGHLIGHT_PATCH_START = 31.26s narration) aligns with section time 55.7s when the narration says "each patch is getting faster."

- **Section 55.7s = internal frame 938:** HIGHLIGHT_PATCH_START -- small-codebase line gets thicker stroke (3 + patchHighlight * 3 = up to 6px)
- **Section ~58.0s = internal frame 1008:** arrowStart -- "Every patch adds code" curved arrow begins fading in
- **Section 61.46s = internal frame 1111:** Still within HIGHLIGHT_PATCH phase (ends at frame 1130). No dashed line yet (REVEAL_DASHED_START = frame 1177).

This timing correctly focuses the viewer on the dropping small-codebase patch line before the dashed "total cost" reveal comes in V7.

---

## Frame-by-Frame Analysis

### Frame at t=56s (internal frame ~948)
- **Chart visible:** Full code cost chart with 2015-2025 x-axis, 0-35 y-axis ("Cost (Developer Hours)").
- **Blue line (Cost to Generate):** Drawn from ~32 hrs (2015) through ~30 hrs (2020), then plunging steeply through 2022 toward ~3 hrs by 2025. Line has completed drawing (Phase 2 end = frame 1130, but drawing was progressive and most is visible).
- **Amber baseline (Patch Cost):** Flat at ~10 hrs from 2015 to 2020, with label "Patch Cost" visible at the 2020 endpoint.
- **Amber fork - Small Codebase:** Drops from 10 hrs at 2020 down to ~1.5 hrs by 2025. Label "Small Codebase" visible at endpoint. Line appears slightly thicker due to patchHighlight animation.
- **Amber fork - Large Codebase:** Stays relatively flat, rising slightly from ~10 to ~12 hrs. Label "Large Codebase" visible at endpoint. Thinner/dimmer than small-codebase line.
- **Annotation:** "Same tools. Different codebase sizes." is visible in a dark overlay box centered on the chart.
- **No dashed line:** Correct -- the dashed "True Cost" line is not yet revealed at this point.
- **No arrow:** The "Every patch adds code" arrow has not yet appeared (arrowStart = frame 1008, this frame is ~948).

### Frame at t=59s (internal frame ~1038)
- **Same chart state** as t=56s, with all lines fully drawn.
- **Annotation still visible:** "Same tools. Different codebase sizes."
- **Arrow NOW VISIBLE:** The curved dashed arrow from the small-codebase fork (~3 hrs) to the large-codebase fork (~11 hrs) at approximately x=2023.5 is now visible. The label "Every patch adds code" appears to the right of the arrow. The arrow is partially faded in (opacity interpolating from frame 1008 to 1068).
- **Small-codebase line** remains highlighted with increased stroke width.

### Frame at t=61s (internal frame ~1088)
- **Same chart layout** persists.
- **Arrow fully visible:** The "Every patch adds code" curved arrow is now at higher opacity, clearly connecting the small-codebase path to the large-codebase path.
- **"Same tools" annotation** still present.
- **All line labels visible:** "Cost to Generate" (blue), "Patch Cost" (amber at 2020), "Small Codebase" (amber at bottom), "Large Codebase" (amber at ~12 hrs).
- **No dashed line, no debt area** -- these correctly do not appear until V7 (CrossingPoint).

---

## Spec Compliance

| Requirement | Status | Notes |
|---|---|---|
| Focus on dropping patch line | PASS | Small-codebase line drops visibly from 10 to ~1.5 hrs, thickened stroke highlights it |
| "That's real" validation feel | PASS | The viewer sees AI making patching genuinely faster -- the dropping amber line is the dominant visual |
| Fork visible (small vs large) | PASS | Two diverging amber paths clearly shown with distinct labels |
| "Same tools. Different codebase sizes." | PASS | Centered overlay annotation visible throughout scene |
| "Every patch adds code" arrow | PASS | Curved arrow appears mid-scene (~59s), connects small-to-large fork |
| No dashed line yet | PASS | Dashed "True Cost" line correctly withheld for reveal in V7 |
| No debt shaded area | PASS | Tech debt area not shown -- saved for V7 reveal |
| Labels readable | PASS | All labels ("Cost to Generate," "Patch Cost," "Small Codebase," "Large Codebase") are legible |
| Narration sync | PASS | "each patch is getting faster" aligns with highlight of dropping small-codebase line |

---

## Visual Quality

- **Color contrast:** Good. Blue line (Cost to Generate) and amber lines (Patch Cost / forks) are clearly distinguishable against the dark background (#1a1a2e).
- **Typography:** Clean sans-serif labels at appropriate sizes. Axis labels, year ticks, and line labels all readable.
- **Animation pacing:** The patch highlight (thicker stroke) on the small-codebase line provides subtle emphasis without being distracting. Arrow fade-in at ~59s creates a natural "wait, there's a catch" moment.
- **Chart data accuracy:** Values match the spec data points (Generate: 32->3, Baseline: 10, Small CB: 10->1.5, Large CB: 10->12).

---

## Issues Found

None. The scene correctly focuses on validating the viewer's experience ("patches are getting faster") while subtly introducing the fork and the "every patch adds code" arrow. The dashed total-cost line is appropriately withheld for the next scene's reveal.
