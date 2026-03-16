[Remotion]

# Section 1.1: Sock Economics — Labor vs. Garment Cost

**Tool:** Remotion
**Duration:** ~24s
**Timestamp:** 0:20 – 0:44

## Visual Description
An animated line chart showing the economic crossover that made sock darning irrational. Two lines — "Labor Cost" (rising) and "Sock Cost" (falling) — are plotted from 1950 to 1975. They cross around 1962–1965, with the crossing point highlighted and labeled "The Threshold". Before the cross, the area between is shaded green (darning makes sense). After, it's shaded red (darning is irrational). The chart builds progressively as the narrator tells the story.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F1923 (dark blue-black)
- Grid lines: Horizontal at 25%, 50%, 75% of Y-axis — #FFFFFF at 5% opacity

### Chart/Visual Elements
- **Chart area:** 1400×600px, centered, with 260px left margin for Y-axis labels
- **X-axis:** Years 1950–1975, ticks every 5 years, labels in #8B9DC3
- **Y-axis:** "Relative Cost (% of hourly wage)" — 0% to 100%, ticks at 25% intervals
- **Labor cost line:** Warm amber (#D9944A), 3px solid, rises from ~30% to ~80%
- **Sock cost line:** Cool blue (#4A90D9), 3px solid, falls from ~70% to ~15%
- **Crossing point:** White circle (8px radius) with pulsing glow at the intersection (~1962, ~50%)
- **"The Threshold" label:** White text with connecting line to intersection point
- **Green shaded area (pre-cross):** Between lines, 1950–1962, #22C55E at 12% opacity
- **Red shaded area (post-cross):** Between lines, 1962–1975, #EF4444 at 12% opacity
- **Chart title:** "When Darning Became Irrational" — top-left of chart area

### Animation Sequence
1. **Frame 0–30 (0–1s):** Chart axes draw on (X-axis left→right, Y-axis bottom→up). Grid lines fade in.
2. **Frame 30–90 (1–3s):** Both lines draw simultaneously from 1950 toward 1960. Green shaded area fills behind as lines progress. Synced with "In 1950, a wool sock cost real money..."
3. **Frame 90–150 (3–5s):** Lines continue drawing through the crossing point. White circle pulses at intersection. "The Threshold" label fades in with a subtle bounce.
4. **Frame 150–240 (5–8s):** Lines continue to 1975. Red shaded area fills in post-crossing zone. The divergence becomes dramatic. Synced with "By the mid-1960s, the math flipped..."
5. **Frame 240–360 (8–12s):** Small annotation fades in near the green zone: "30 min of labor > new sock cost". Post-1965 region dims slightly to emphasize the irrationality.
6. **Frame 360–480 (12–16s):** Hold with gentle ambient animation (subtle line glow pulse). The word "irrational" appears in the red zone with a typewriter effect.
7. **Frame 480–720 (16–24s):** Chart holds for remaining narration. At frame 600, elements begin a slow fade-out to prepare for transition to code chart.

### Typography
- Chart title: Inter SemiBold, 28px, #FFFFFF, opacity 0.9
- Axis labels: Inter Regular, 14px, #8B9DC3
- "The Threshold" label: Inter SemiBold, 18px, #FFFFFF
- Annotation text: Inter Regular, 14px, #8B9DC3, italic
- "irrational" keyword: Inter Bold, 22px, #EF4444

### Easing
- Line draw-on: `easeInOutCubic`
- Crossing point pulse: `easeInOutSine` (looping, 2s period)
- Label fade-in: `easeOutQuad`
- Shaded area fill: `easeOutCubic`

## Narration Sync
> "This isn't nostalgia. It's economics."

> "In 1950, a wool sock cost real money relative to an hour of labor. Darning made sense. You'd spend thirty minutes to save a dollar."

> "By the mid-1960s, the math flipped. A new sock cost less than the time to repair the old one. Darning became irrational."

Segments: `part1_economics_005` (19.48s – 23.02s), `part1_economics_006` (23.94s – 34.50s), `part1_economics_007` (34.62s – 43.30s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={720}>
  <AbsoluteFill style={{ backgroundColor: '#0F1923' }}>
    <Sequence from={0} durationInFrames={30}>
      <AnimatedAxes xRange={[1950, 1975]} yRange={[0, 100]} />
    </Sequence>
    <Sequence from={30} durationInFrames={450}>
      <AnimatedLine
        data={laborCostData}
        color="#D9944A"
        drawDuration={210}
      />
      <AnimatedLine
        data={sockCostData}
        color="#4A90D9"
        drawDuration={210}
      />
      <ShadedArea data={preCrossArea} color="#22C55E" opacity={0.12} />
      <ShadedArea data={postCrossArea} color="#EF4444" opacity={0.12} />
    </Sequence>
    <Sequence from={90} durationInFrames={60}>
      <PulsingDot cx={crossX} cy={crossY} color="#FFFFFF" />
      <FadeInLabel text="The Threshold" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "laborCost": [
    { "year": 1950, "value": 30 },
    { "year": 1955, "value": 38 },
    { "year": 1960, "value": 47 },
    { "year": 1965, "value": 58 },
    { "year": 1970, "value": 68 },
    { "year": 1975, "value": 80 }
  ],
  "sockCost": [
    { "year": 1950, "value": 70 },
    { "year": 1955, "value": 58 },
    { "year": 1960, "value": 48 },
    { "year": 1965, "value": 32 },
    { "year": 1970, "value": 22 },
    { "year": 1975, "value": 15 }
  ],
  "crossingPoint": { "year": 1962, "value": 50 }
}
```
