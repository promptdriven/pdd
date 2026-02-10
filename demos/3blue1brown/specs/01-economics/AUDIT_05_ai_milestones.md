# Audit: 05_ai_milestones

## Status: PASS

## Rendered Frames Reviewed

- Frame 30 (mid-zoom): Grid and axes visible at reduced opacity, title displayed, no cost line or markers yet
- Frame 200 (GPT-4 beat): Codex/Copilot and GPT-4 markers visible on the cost line, full staircase line drawn
- Frame 300 (Claude 3.5 Sonnet beat): Three markers visible (Codex, GPT-4, Claude 3.5 Sonnet), Claude 3.5 Sonnet marker is the largest
- Frame 440 (end of frontier cluster): All 7 markers visible, frontier cluster tightly packed at the bottom right
- Frame 500 (hold phase): All markers with pulse effects, legend visible in top-right corner

## Requirements Checklist

### 1. Duration and Canvas
- **Duration**: Spec requires ~18 seconds (540 frames at 30fps). Implementation: `AI_MILESTONES_DURATION_SECONDS = 18`, `AI_MILESTONES_DURATION_FRAMES = 540`. **MATCH**
  - Spec ref: line 4
  - `constants.ts:4-6`
- **Canvas**: 1920x1080. Implementation: `AI_MILESTONES_WIDTH = 1920`, `AI_MILESTONES_HEIGHT = 1080`. **MATCH**
  - `constants.ts:7-8`

### 2. Focus on 2020-2025 Region
- Spec says focus shifts to 2020-2025. Implementation uses `YEAR_RANGE = { min: 2020, max: 2026 }` to accommodate late-2025 frontier markers. X-axis shows ticks for 2020 through 2025. **MATCH** (minor adaptation extending to 2026 is necessary for data)
  - Spec ref: line 15
  - `constants.ts:95`

### 3. Milestone Identity and Count (7 markers across 5 milestones)
- Spec defines: Codex/Copilot, GPT-4, Claude 3.5 Sonnet, Claude 3.7 Sonnet, and frontier cluster (Opus 4.5, GPT 5.2, Gemini 3). Implementation `MILESTONES` array contains exactly these 7 entries with correct names and year positions. Confirmed in rendered frames -- all 7 labels are legible. **MATCH**
  - Spec ref: lines 26-32
  - `constants.ts:76-84`

### 4. Milestone Colors
- Codex: Blue (`#3B82F6`), GPT-4: Purple (`#8B5CF6`), Claude 3.5 Sonnet: Orange (`#F59E0B`), Claude 3.7 Sonnet: Orange (`#F59E0B`), Opus 4.5: Orange (`#F59E0B`), GPT 5.2: Purple (`#8B5CF6`), Gemini 3: Red (`#EF4444`). Spec: Codex=Blue, GPT-4=Purple, both Claudes=Orange, Frontier=Multi. Confirmed visually in frame 500 -- blue small dot for Codex, purple for GPT-4, large orange for Claude 3.5, and the frontier cluster shows orange/purple/red. **MATCH**
  - Spec ref: lines 26-32 (Color column)
  - `constants.ts:57-60, 76-84`

### 5. Marker Shape (Circle)
- Spec requires Circle icon for all markers. Implementation renders SVG `<circle>` elements. Confirmed in all rendered frames. **MATCH**
  - Spec ref: lines 26-32 (Icon column)
  - `MilestoneMarker.tsx:193-207`

### 6. Drop Size Hierarchy (Uneven Staircase)
- Spec requires: Codex=Small, GPT-4=Large, Claude 3.5 Sonnet=Large (largest visual), Claude 3.7=Moderate, Frontier=Moderate. Implementation uses `impactScale`: Codex=1.0, GPT-4=1.5, Claude 3.5 Sonnet=1.8 (largest), Claude 3.7=1.2, Frontier=1.0 each. The `markerRadius = 16 * impactScaleProp` creates a visible size hierarchy. COST_DATA models the staircase: Codex drops ~2 units (30 to 28), GPT-4 drops ~6 units (26 to 20), Claude 3.5 drops ~9 units (16 to 7, the cliff), Claude 3.7 drops ~1 unit (5.5 to 4.5), frontier settles from ~4 to ~3. Rendered frames confirm Claude 3.5 Sonnet is the largest marker and the steepest visible drop in the line. **MATCH**
  - Spec ref: lines 26-32 (Drop Size column), lines 73-75, 90, 179-184
  - `constants.ts:73, 77-84, 99-116`

### 7. Animation Beat Timings (All 7 Phases)
- Zoom: frames 0-60 (spec: "Frame 0-60") -- **MATCH**
- Codex: starts frame 60 (spec: "Frame 60-150") -- **MATCH**
- GPT-4: starts frame 150 (spec: "Frame 150-240") -- **MATCH**
- Claude 3.5 Sonnet: starts frame 240 (spec: "Frame 240-330") -- **MATCH**
- Claude 3.7 Sonnet: starts frame 330 (spec: "Frame 330-390") -- **MATCH**
- Frontier cluster: frames 390/405/420 (spec: "Frame 390-450") -- **MATCH**
- Hold: frames 450-540 (spec: "Frame 450-540") -- **MATCH**
  - Spec ref: lines 62-83
  - `constants.ts:11-42`

### 8. Zoom Effect (Frame 0-60)
- Spec says rest of chart fades to 30% opacity and x-axis rescales. Implementation: `zoomProgress` drives `scale(1 + zoomProgress * 0.15)` transform; `backgroundOpacity` interpolates from 1 to 0.3 over frames 0-60. Grid, axes, and labels all bound to `backgroundOpacity`. Confirmed in frame 30 render -- grid lines and labels are visibly faded. **MATCH**
  - Spec ref: lines 62-64
  - `AIMilestones.tsx:25-38, 164-172, 226`

### 9. Zoom Easing
- Spec requires `easeInOutCubic`. Implementation uses `Easing.inOut(Easing.cubic)`. **MATCH**
  - Spec ref: line 102
  - `AIMilestones.tsx:29`

### 10. Spring Animation for Marker Pop-in
- Spec requires `spring({ damping: 12, stiffness: 200 })`. Implementation: `SPRING_CONFIG = { damping: 12, stiffness: 200 }` used in `markerScale` spring. **MATCH**
  - Spec ref: line 103
  - `constants.ts:121-124`, `MilestoneMarker.tsx:37-41`

### 11. Frontier Cluster Staggered by 15 Frames
- Spec says three markers staggered by 15 frames. Implementation: OPUS_START=390, GPT52_START=405, GEMINI3_START=420 (each 15 frames apart). Labels "Opus 4.5", "GPT 5.2", "Gemini 3". Confirmed visually in frame 440 -- three distinct small markers closely packed. **MATCH**
  - Spec ref: lines 79-82
  - `constants.ts:34-36, 81-83`

### 12. Hold Phase with Subtle Pulse (Frame 450-540)
- Spec says "slight pulse on final position". Implementation uses `Math.sin` oscillation on both scale and opacity during `isHoldPhase` (frame >= 450). Markers subtly pulse with a radial gradient glow. **MATCH**
  - Spec ref: line 83
  - `MilestoneMarker.tsx:64-71, 182-189`

### 13. Impact Effect Scaled to Drop Size
- Spec says each marker has a "subtle impact effect scaled to match drop size". Implementation: ripple circles expand from 1x to 3x radius over 30 frames (fade from 0.6 to 0 opacity) with radius scaled by `impactScaleProp`. Claude 3.5 Sonnet (impactScale=1.8) gets the largest ripple; Codex (1.0) gets the smallest. **MATCH**
  - Spec ref: lines 87-88
  - `MilestoneMarker.tsx:73, 76-88, 169-179`

### 14. Labels Staggered to Avoid Overlap
- Spec says labels appear next to markers, staggered vertically. Implementation uses `getLabelPosition()` returning per-index positions (top/bottom/left/right) and `getLabelOffsetY()` for fine vertical adjustments. Confirmed in rendered frames -- labels are distributed without overlapping. **MATCH**
  - Spec ref: line 92
  - `AIMilestones.tsx:93-109`

### 15. Sans-serif Font
- Spec says "Sans-serif, 16pt, white". Implementation uses `fontFamily: "Inter, system-ui, sans-serif"`. Sans-serif requirement met. **MATCH**
  - Spec ref: line 96
  - `MilestoneMarker.tsx:94`

### 16. Visual-only (No Narration Text)
- Spec says "Visual only during this section". No subtitle or narration text rendered by AIMilestones component. **MATCH**
  - Spec ref: line 109
  - `AIMilestones.tsx` -- no subtitle elements

### 17. Integration into Part1Economics
- AIMilestones is placed as Visual 4 in Part1Economics, sequenced at `VISUAL_04_START` (frame 798, ~26.6s) with `defaultAIMilestonesProps`. **MATCH**
  - `Part1Economics.tsx:11, 75-79`
  - `S01-Economics/constants.ts:153-155, 240`

## Deviations (All Low/Informational)

### 1. Drop Easing Not Differentiated Per Milestone (Low)
- **Spec**: Small drops use `easeOutQuad` over 20 frames; large drops use `easeOutQuad` over 40 frames for slower fall emphasis.
- **Implementation**: The cost line is drawn as a single SVG path revealed via `strokeDasharray`/`strokeDashoffset` animation over 60 frames from ZOOM_END, meaning all segments reveal at uniform speed. No per-milestone animated drop with differentiated durations.
- **Impact**: The visual effect of the uneven staircase is still achieved through the COST_DATA values (the line shape shows unequal steps) and the scaled marker impact effects. Claude 3.5 Sonnet still "feels like a cliff" through the 9-unit cost drop and 1.8x impact scale. The spec's intent is substantially met even without per-segment easing.
- Spec ref: lines 104-105
- `AIMilestones.tsx:78-84`

### 2. Typography Font Size Larger Than Spec (Low)
- **Spec**: Model names 16pt, year labels 14pt.
- **Implementation**: Model name labels 22pt, year tick labels 28pt.
- **Impact**: At 1920x1080 video resolution, 16pt would be very small. The larger sizes are a reasonable adaptation for readability. Confirmed in rendered frames -- labels are legible and well-proportioned.
- Spec ref: lines 96-97
- `MilestoneMarker.tsx:95`, `AIMilestones.tsx:237-238`

### 3. Model Name Labels Use Milestone Color Instead of White (Low)
- **Spec**: Model names should be "white".
- **Implementation**: Labels use `color: color` (the milestone's marker color).
- **Impact**: Improves visual association between labels and markers. All milestone colors (blue, purple, orange, red) are bright enough to read against the dark background. Confirmed in rendered frames.
- Spec ref: line 96
- `MilestoneMarker.tsx:97`

### 4. Year Labels Use Translucent White Instead of Gray (Low)
- **Spec**: Year labels should be "gray".
- **Implementation**: Uses `rgba(255, 255, 255, 0.8)`, which renders as slightly faded white.
- **Impact**: Visually similar to light gray on the dark background. Negligible deviation.
- Spec ref: line 97
- `AIMilestones.tsx:239`, `constants.ts:50`

### 5. Title Added Not In Spec (Low)
- **Spec**: Section continues from Section 1.4 with no explicit title.
- **Implementation**: Adds "AI Milestones: The Acceleration" as a title (controlled by `showTitle` prop).
- **Impact**: Useful for standalone viewing. Does not conflict with any spec requirement. Can be suppressed via `showTitle=false`.
- Spec ref: lines 13-14
- `AIMilestones.tsx:132-149`, `constants.ts:127-133`

### 6. GPT-4 Beat Comment Says "moderate" Instead of "large" (Informational)
- The comment on `constants.ts:20` reads "moderate drop" for GPT-4, but the spec says "Large". The actual `impactScale` value of 1.5 correctly represents a large drop. Comment-only issue with zero functional impact.
- Spec ref: line 29
- `constants.ts:20`

### 7. Optional Company Logos Not Implemented (Informational)
- Spec mentions "Optional: Small logos next to names (if available/legal)". Not implemented. Spec explicitly marks as optional.
- Spec ref: line 98

### 8. Legend Added Beyond Spec (Informational)
- Implementation includes an "AI Model Releases" legend box in the top-right corner that fades in after the frontier cluster completes. Not in spec, but adds useful context for the viewer. Non-conflicting enhancement.
- `AIMilestones.tsx:347-401`

## Visual Quality Assessment

Based on the rendered frames:
- **Frame 30**: Clean zoom-in effect with faded grid. Title legible. No premature line or markers.
- **Frame 200**: Codex (small blue dot, high on curve) and GPT-4 (medium purple dot, after a clear drop) are visible. The cost line draws the staircase descent convincingly.
- **Frame 300**: Claude 3.5 Sonnet appears as a notably larger orange circle, positioned after the steepest drop in the line. This is the visual climax as intended by the spec.
- **Frame 440**: All 7 markers visible. The frontier cluster (3 small dots -- orange, purple, red) is tightly packed in the bottom-right. Labels are distributed to avoid overlap.
- **Frame 500**: Hold phase with all markers, legend visible. The overall composition reads clearly as an "uneven staircase descent" with Claude 3.5 Sonnet as the cliff.

The rendered output faithfully communicates the spec's core narrative: AI capability progression from small (Codex) to transformative (Claude 3.5 Sonnet) to competitive convergence (frontier cluster), represented as an uneven cost descent.

## Resolution Summary

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 1 | Drop easing not differentiated per milestone | Low | ACCEPTED - Staircase shape in COST_DATA + scaled impactScale achieves spec intent. Claude 3.5 reads as the cliff. |
| 2 | Typography font size larger than spec | Low | ACCEPTED - Necessary adaptation for 1920x1080 video readability. |
| 3 | Model name labels use milestone color | Low | ACCEPTED - Improves label-marker association. All colors readable on dark background. |
| 4 | Year labels translucent white vs gray | Low | ACCEPTED - Visually equivalent on dark background. |
| 5 | Title added not in spec | Low | ACCEPTED - Useful for standalone viewing, non-conflicting. |
| 6 | GPT-4 beat comment says "moderate" | Informational | NOTED - Comment-only, correct impactScale value. |
| 7 | Optional logos not implemented | Informational | NOTED - Spec explicitly marks as optional. |
| 8 | Legend added beyond spec | Informational | NOTED - Non-conflicting enhancement. |

No blocking issues found. All deviations are low-severity adaptations or informational notes.
