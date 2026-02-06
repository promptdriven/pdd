# Section 1.3: Lines Diverge Dramatically

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 2:39 - 2:58

## Visual Description

The chart continues from the threshold, showing the dramatic divergence as sock costs plummet to near-zero by 2020 while repair costs remain constant.

## Technical Specifications

### Canvas
- Continues from Section 1.2
- Same chart, threshold marker fades slightly

### Animation Elements

1. **Continued Line Animation**
   - "Cost to Buy" line continues dropping dramatically
   - Nearly touches X-axis by 2020
   - "Cost to Repair" line stays flat

2. **Year Counter**
   - Position: Top-right corner
   - Shows current year as time progresses
   - Large font, white, slight glow

3. **Gap Indicator**
   - Vertical dashed line showing the gap between the two lines
   - Appears around 1970
   - Label showing "Waste of time" or arrow indicating the irrational zone

4. **Shaded Region**
   - The area where "repair > buy" (post-threshold)
   - Light red/amber fill at 10% opacity
   - Label: "Darning is irrational"

### Animation Sequence

1. **Frame 0-60 (0-2s):** Threshold marker fades to 50% opacity
2. **Frame 0-270 (0-9s):** Time progresses 1965 → 2020
   - "Cost to Buy" line draws downward dramatically
   - Year counter updates smoothly
3. **Frame 120-180 (4-6s):** Shaded region fades in
4. **Frame 180-270 (6-9s):** Gap indicator appears
5. **Frame 270-360 (9-12s):** Hold on final state
6. **Frame 360-450 (12-15s):** Zoom out slightly to show full picture

### Data Visualization

By 2020:
- Cost to buy: ~$3 for a multi-pack = ~3 minutes of median wage
- Cost to repair: Still ~30 minutes of focused time
- Ratio: 10:1 in favor of replacement

### Typography

- Year counter: Monospace or digital-style font, 48pt
- "Darning is irrational" label: Italic, 18pt, amber color

### Easing

- Line continuation: `easeInOutQuad`
- Year counter: Linear (time progression)
- Fade effects: `easeOutCubic`

## Narration Sync

> "By the mid-1960s, the math flipped. A new sock cost less than the time to repair the old one. Darning became irrational."

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={450}>
  <PreviousChartWithThreshold opacityThreshold={0.5} />

  <Sequence from={0} durationInFrames={270}>
    <ContinuedLineAnimation
      startYear={1965}
      endYear={2020}
      data={costToBuyData}
    />
    <YearCounter startYear={1965} endYear={2020} />
  </Sequence>

  <Sequence from={120}>
    <ShadedRegion
      aboveLine="repair"
      belowLine="buy"
      fillColor="rgba(217, 148, 74, 0.1)"
    />
  </Sequence>

  <Sequence from={180}>
    <GapIndicator year={2010} />
  </Sequence>
</Sequence>
```

## Visual Style Notes

- The divergence should feel dramatic and definitive
- The shaded "irrational zone" should be subtle but clear
- This sets up the transition to the code chart

## Transition

Chart fades or morphs into the code cost chart (Section 1.4).
