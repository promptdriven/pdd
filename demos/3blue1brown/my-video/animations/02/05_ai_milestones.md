# Section 1.5: AI Milestones on the Falling Line

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 3:05 - 3:20

## Visual Description

Key AI model releases appear as markers on the steep drop in the "cost to generate" line. Each milestone pushes the line lower.

## Technical Specifications

### Canvas
- Continues from Section 1.4
- Focus shifts to the 2020-2024 region

### Chart Elements

Zoom in on the 2020-2024 section of the chart:
- The steep drop becomes more detailed
- Individual model releases marked

### Milestone Markers

| Model | Year | Color | Icon |
|-------|------|-------|------|
| GPT-3 | 2020 | Green | Circle |
| Codex | 2021 | Blue | Circle |
| GPT-4 | 2023 | Purple | Circle |
| Claude | 2023 | Orange | Circle |
| Gemini | 2023 | Red | Circle |

### Animation Sequence

1. **Frame 0-60 (0-2s):** Zoom into 2020-2024 region
   - Rest of chart fades to 30% opacity
   - X-axis rescales
2. **Frame 60-120 (2-4s):** GPT-3 marker appears (2020)
   - Marker pops in with spring animation
   - Label fades in
   - Line drops to next level
3. **Frame 120-180 (4-6s):** Codex marker appears (2021)
   - Same pattern
4. **Frame 180-270 (6-9s):** GPT-4, Claude, Gemini appear in quick succession (2023)
   - Staggered by 30 frames each
   - Line drops dramatically
5. **Frame 270-360 (9-12s):** All markers visible, line settles at low point
6. **Frame 360-450 (12-15s):** Hold, slight pulse on final position

### Visual Style

- Markers should feel like "events" that cause the line to drop
- Each appearance could have a subtle "impact" effect
- Labels appear next to markers, slightly staggered vertically to avoid overlap

### Typography

- Model names: Sans-serif, 16pt, white
- Year labels: 14pt, gray
- Optional: Small logos next to names (if available/legal)

### Easing

- Zoom: `easeInOutCubic`
- Marker pop-in: `spring({ damping: 12, stiffness: 200 })`
- Line drops: `easeOutQuad`

## Narration Sync

(Visual only during this section - the chart speaks for itself)

The narration from Section 1.4 continues:
> "...So when something broke, you patched. Of course you patched. It was rational."

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={450}>
  {/* Zoom effect */}
  <Sequence from={0} durationInFrames={60}>
    <ZoomToRegion
      chart={<CodeCostChart />}
      region={{ startYear: 2019, endYear: 2025 }}
    />
  </Sequence>

  {/* Milestones */}
  <Sequence from={60}>
    <MilestoneMarker
      name="GPT-3"
      year={2020}
      color="#10B981"
    />
  </Sequence>

  <Sequence from={120}>
    <MilestoneMarker
      name="Codex"
      year={2021}
      color="#3B82F6"
    />
  </Sequence>

  <Sequence from={180}>
    <MilestoneMarker name="GPT-4" year={2023} color="#8B5CF6" />
  </Sequence>

  <Sequence from={210}>
    <MilestoneMarker name="Claude" year={2023} color="#F59E0B" />
  </Sequence>

  <Sequence from={240}>
    <MilestoneMarker name="Gemini" year={2023} color="#EF4444" />
  </Sequence>
</Sequence>
```

## Visual Style Notes

- This should feel like a "staircase descent" - each model makes things cheaper
- The 2023 cluster should feel like an acceleration
- Clean, informative, not promotional for any specific company

## Transition

Transition to context rot explanation (Section 1.6), then crossing point (Section 1.7).
