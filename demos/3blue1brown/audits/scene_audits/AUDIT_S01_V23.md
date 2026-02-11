# Scene Audit: S01 V23 - PieToCurve

**Section:** S01 Part 1 Economics
**Scene:** V23 - PieToCurve (compound interest curve + regeneration line)
**Video:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/outputs/sections/part1_economics.mp4`
**Time range:** 421.76s - 432.64s (10.88s duration)
**Frames inspected:** t=423s, t=427s, t=432s
**Remotion component:** `remotion/src/remotion/13-PieToCurve/PieToCurve.tsx`
**Date:** 2026-02-09

---

## Verdict: PASS

---

## Frame-by-Frame Analysis

### Frame 1: t=423s (early in scene)
- **Axes:** Both X-axis ("Time (Years 1-10)" with ticks 1-10) and Y-axis ("Cumulative Maintenance Cost" with ticks 4x, 8x, 12x, 16x) are fully visible.
- **Exponential curve:** Not yet drawn -- the chart area is empty. This is consistent with the early stage of the animation where the axes have appeared but the curve drawing has not yet begun (or is just starting).
- **Regeneration line:** Not yet visible. Expected at this early point.
- **Assessment:** Correct. The axes provide a clean foundation before the curve animates in.

### Frame 2: t=427s (midpoint of scene)
- **Axes:** Fully visible with all labels and ticks.
- **Exponential curve:** Fully drawn in orange/amber, rising from near 1x at Year 1 to approximately 15-16x by Year 10. The exponential shape is clearly conveyed with a gradual rise through Years 1-6 and a steep climb through Years 7-10.
- **Formula annotation:** Visible in the upper-right area of the chart in amber text: "Technical debt follows compound interest:" followed by "Debt x (1 + Rate)^Time" in monospace font. This matches the script description.
- **Regeneration line:** Present as a flat, horizontal blue dashed/solid line running along the bottom of the chart (near the 1x level). Labeled "Regeneration cost (debt resets each cycle)" in blue text. The label "Linear" also appears at the far right end. This directly contrasts with the exponential curve above.
- **Blue dot:** A small blue dot is visible at the end of the regeneration line, marking its endpoint.
- **Assessment:** All required visual elements are present and correctly positioned. The contrast between the exponential orange curve and flat blue regeneration line is visually clear and communicates the key insight effectively.

### Frame 3: t=432s (end of scene)
- **Axes, curve, formula, regeneration line:** All identical to t=427s -- these persist as expected.
- **Final quote text:** A white italic serif quote appears at the bottom center of the frame: "Unless you regenerate. Then the debt resets." This matches the script narration exactly.
- **Assessment:** The scene reaches its final state with all visual elements present: axes, exponential curve with formula, flat regeneration line with label, and the concluding narration quote.

---

## Checklist

| Element | Required | Present | Notes |
|---|---|---|---|
| Chart axes (X and Y) | Yes | Yes | X: Time (Years 1-10), Y: Cumulative Maintenance Cost (4x-16x) |
| Exponential curve | Yes | Yes | Orange/amber, rises to ~15-16x by Year 10 |
| Formula annotation | Yes | Yes | "Technical debt follows compound interest: Debt x (1 + Rate)^Time" |
| Regeneration line (flat) | Yes | Yes | Blue horizontal line near bottom, clearly contrasting with exponential |
| Regeneration label | Yes | Yes | "Regeneration cost (debt resets each cycle)" |
| Final narration quote | Yes | Yes | "Unless you regenerate. Then the debt resets." |
| Smooth animation progression | Yes | Yes | Axes visible first, then curve draws, then regen line, then quote |
| Dark background (3b1b style) | Yes | Yes | Dark navy/charcoal background throughout |

---

## Notes

- The animation pacing is well-structured: axes appear first (t=423), then the exponential curve and regeneration line are both fully visible by t=427, and the concluding quote fades in by t=432.
- The "Linear" label at the far right of the regeneration line is an additional detail not explicitly in the script but adds clarity by naming the flat line's growth pattern.
- The visual contrast between the steeply rising orange curve and the flat blue line effectively communicates the core message about compound debt vs. regeneration cost.
- Previously reported issues (missing regeneration line, offset problems) have been resolved as confirmed by the section-level audit notes.
