# Scene Audit: S01 Part 1 Economics - V4 AIMilestones

**Video:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/outputs/sections/part1_economics.mp4`
**Time range:** 26.6s - 39.24s (12.64s)
**Script visual:** "For decades, generating new code was expensive... So when something broke, you patched."
**Narration:** "For decades, generating new code was expensive... So when something broke, you patched. Of course you patched. It was rational."
**Spec:** `specs/01-economics/05_ai_milestones.md`
**Date:** 2026-02-09

## Frames Examined

- t=27s: Title "AI Milestones: The Acceleration" visible at top center, white bold sans-serif. Chart axes fully visible: Y-axis "Cost (Developer Hours)" with values 0-35, X-axis "Year" with markers at 2020, 2021, 2022, 2023, 2024, 2025. Grid lines faintly visible. No data line or milestone markers yet -- this is the zoom-in phase (spec frames 0-60). Dark navy background (#1a1a2e). Chart area is empty, establishing the canvas.

- t=30s: Cost-to-generate line fully drawn, descending from ~30 hours at 2020 to ~3 hours near end of 2025. Continuous light blue/cyan line. First milestone marker visible: **"Codex / Copilot"** -- blue circle at 2021, positioned at ~28 hours on the line. Label text in blue above the marker with a dashed connector line. The line shows a gentle slope from 2020-2022, then steepens dramatically after 2023. The line is fully drawn to the end, showing the complete descent.

- t=33s: Two milestone markers now visible:
  1. **"Codex / Copilot"** (blue circle, 2021, ~28 hrs) -- persists from t=30s with label.
  2. **"GPT-4"** (purple/lilac circle, ~2023.25, ~20 hrs) -- newly appeared with label text visible. Marker sits on the line at the point where the descent begins steepening. Dashed connector line from label to marker.
  The line shows the uneven staircase: gentle slope 2020-2022 (~30 to ~26), then moderate drop at GPT-4 position (~26 to ~20), then steep plunge through 2024-2025.

- t=37s: Three milestone markers visible:
  1. **"Codex / Copilot"** (blue, 2021, ~28 hrs)
  2. **"GPT-4"** (purple, ~2023.25, ~20 hrs)
  3. **"Claude 3.5 Sonnet"** (orange/amber, ~2024.5, ~7 hrs) -- **visibly LARGER marker** than the others, consistent with spec's impactScale=1.5. Orange label text with connector line. The dramatic cliff from ~18 to ~7 at this position is the visual climax.
  The line continues to ~3 hours near 2025. Frontier cluster not yet visible.

- t=39s (bonus frame near segment end): Four milestone markers visible:
  1. "Codex / Copilot" (blue, 2021, ~28 hrs)
  2. "GPT-4" (purple, ~2023.25, ~20 hrs)
  3. "Claude 3.5 Sonnet" (orange, ~2024.5, ~7 hrs) -- largest marker
  4. **"Claude 3.7 Sonnet"** (orange, ~2025, ~4.5 hrs) -- newly appeared, smaller than Claude 3.5 but same orange color. Label visible.
  Frontier cluster (Opus 4.5, GPT 5.2, Gemini 3) not yet visible -- expected to appear in subsequent segment (local frame 390+ maps to ~39.6s+).

## Detailed Element Verification

### 1. Chart Zoom to 2020-2025 Region
**VERIFIED.** By t=27s the chart has zoomed to show only 2020-2025 on the X-axis with individual year labels. Y-axis remains 0-35 "Cost (Developer Hours)." The rest of the broader chart from V3 is no longer visible -- the focus is exclusively on the AI era. Background grid lines faded to reduced opacity. Matches spec: "Zoom in on the 2020-2025 section."

### 2. Cost-to-Generate Line Shape
**VERIFIED.** The line shows the characteristic uneven staircase descent:
- 2020: ~30 hours (flat start)
- 2021 (Codex): small dip to ~28 hours -- **small drop** per spec
- 2022: gradual decline to ~26 hours
- 2023 (GPT-4): drops to ~20 hours -- **large drop** per spec
- 2024 (Claude 3.5 Sonnet): dramatic cliff to ~7 hours -- **largest drop** per spec
- 2025 (Claude 3.7 Sonnet): continues to ~4.5 hours -- **moderate drop** per spec
- Late 2025: settles at ~3 hours

Data values approximately match spec targets: Codex small (~2 hrs), GPT-4 large (~6 hrs), Claude 3.5 Sonnet dramatic (~13 hrs from ~20 to ~7), Claude 3.7 moderate (~2.5 hrs).

### 3. Milestone Marker Colors
**VERIFIED.**
- Codex / Copilot: **Blue** circle -- matches spec `#3B82F6`
- GPT-4: **Purple/lilac** circle -- matches spec `#8B5CF6`
- Claude 3.5 Sonnet: **Orange/amber** circle -- matches spec `#F59E0B`
- Claude 3.7 Sonnet: **Orange/amber** circle -- matches spec `#F59E0B`
Color coding correctly distinguishes OpenAI (blue), mixed/OpenAI (purple), and Anthropic (orange) models.

### 4. Marker Sizes and Visual Impact
**VERIFIED.** Claude 3.5 Sonnet marker is visibly the LARGEST circle, consistent with impactScale=1.5 in spec. GPT-4 marker is medium-sized. Codex marker is smallest. Claude 3.7 is medium-small. The spec's "uneven staircase descent" with Claude 3.5 Sonnet as the "cliff" is clearly conveyed.

### 5. Milestone Labels
**VERIFIED.** All four labels are correctly spelled and positioned:
- "Codex / Copilot" (at 2021)
- "GPT-4" (at ~2023)
- "Claude 3.5 Sonnet" (at ~2024.5)
- "Claude 3.7 Sonnet" (at ~2025)
Labels are white/colored sans-serif text with dashed connector lines to their respective markers. Labels are staggered to avoid overlap.

### 6. Animation Timing
**VERIFIED.** Milestones appear in sequence matching the spec's animation order:
- Codex/Copilot visible by t=30s (spec: frame 60-150, ~2-5s into component)
- GPT-4 visible by t=33s (spec: frame 150-240, ~5-8s)
- Claude 3.5 Sonnet visible by t=37s (spec: frame 240-330, ~8-11s)
- Claude 3.7 Sonnet visible by t=39s (spec: frame 330-390, ~11-13s)
- Frontier cluster not yet visible (spec: frame 390+, ~13s+) -- correctly absent

### 7. Frontier Cluster
**NOT IN SCOPE.** The frontier cluster (Opus 4.5, GPT 5.2, Gemini 3) starts at spec frame 390 (~13s into component = ~39.6s video time), which is after this segment's 39.24s end. This is expected -- the frontier cluster should appear in the next segment (V5).

### 8. Narration-Visual Alignment
**NOT AN ISSUE.** The spec explicitly states: "Visual only during this section - the chart speaks for itself" and "The narration from Section 1.4 continues." The juxtaposition of narration about the old paradigm ("patching was rational") with a visual showing generation cost plummeting is an intentional creative choice, not a misalignment. The spec explicitly designs for this.

## Assessment

### Matches Script
- AI milestone markers on the falling "cost to generate" line -- VERIFIED
- Uneven staircase descent with varying drop sizes -- VERIFIED
- Codex small drop, GPT-4 large drop, Claude 3.5 Sonnet dramatic cliff -- VERIFIED
- Color coding: blue (OpenAI), purple (GPT-4), orange (Anthropic) -- VERIFIED
- Chart axes consistent with V3 -- VERIFIED
- Focus on 2020-2025 region -- VERIFIED

### Issues Found
| # | Severity | Description | Fix Suggestion |
|---|----------|-------------|----------------|
| 1 | MINOR | Label fade-in delays (~0.5s after marker appears) mean labels are briefly invisible when a marker first pops in. This is standard animation sequencing -- marker appears, then label fades in. Not confusing to viewers. | No fix needed -- this is correct animation choreography. |
| 2 | MINOR | Frontier cluster (Opus 4.5, GPT 5.2, Gemini 3) not visible in this segment. Verify in V5 audit. | Verify in next segment audit. |

## Status: PASS

**Rationale:** The AIMilestones scene delivers the key visual argument effectively. The uneven staircase descent is clearly visible with appropriately scaled drops: small at Codex (~2 hrs), large at GPT-4 (~6 hrs), dramatic cliff at Claude 3.5 Sonnet (~13 hrs), and moderate at Claude 3.7 Sonnet (~2.5 hrs). Claude 3.5 Sonnet's marker is the largest, correctly conveying it as the visual climax and inflection point. All milestone labels are correctly spelled, colored, and positioned. The chart zoom focuses on 2020-2025 as specified. The narration-visual juxtaposition is explicitly designed per the spec and works as intended -- the viewer hears about the old paradigm while watching the new paradigm unfold. All spec elements within this segment's time range are present. No blocking issues.
