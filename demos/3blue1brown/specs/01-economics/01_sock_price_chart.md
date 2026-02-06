# Section 1.1: Sock Price Chart Animation

**Tool:** Remotion
**Duration:** ~20 seconds
**Timestamp:** 2:00 - 2:26

## Visual Description

Animated line chart showing the economic relationship between sock prices and labor costs from 1950 to present day.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark (#1a1a2e) with subtle gradient
- Grid lines: Subtle gray (#333344), dashed

### Chart Elements
- **X-axis:** Years (1950 - 2020)
- **Y-axis:** "Hours of labor to buy / repair a sock" (0 - 1.5 hours)
- **Line 1 (Cost to Buy):**
  - Color: #4A90D9 (cool blue)
  - Starts high (~1.0 hours in 1950)
  - Drops steadily over time
- **Line 2 (Cost to Repair/Darn):**
  - Color: #D9944A (warm amber)
  - Relatively flat (~0.5 hours throughout)

### Animation Sequence

1. **Frame 0-30 (0-1s):** Axes fade in with labels
2. **Frame 30-90 (1-3s):** "Cost to Buy" line draws from left to right
3. **Frame 90-150 (3-5s):** "Cost to Repair" line draws (horizontal)
4. **Frame 150-300 (5-10s):** Both lines animate together, showing the 1950 starting point
5. **Frame 300-450 (10-15s):** Time progresses, "Cost to Buy" drops
6. **Frame 450-540 (15-18s):** Lines approach crossing point
7. **Frame 540-600 (18-20s):** Hold at crossing point (circa 1960-65)

### Typography
- Title: "The Economics of Sock Repair" (fade in at start)
- Axis labels: Sans-serif, 18pt, white with 80% opacity
- Year markers: Every decade (1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020)

### Easing
- Line drawing: `easeInOutCubic`
- Fade transitions: `easeOutQuad`

## Narration Sync

> "This isn't nostalgia. It's economics."
>
> "In 1950, a wool sock cost real money relative to an hour of labor."

## Code Structure (Remotion)

```typescript
// Component structure
<Sequence from={0} durationInFrames={600}>
  <ChartAxes />
  <Sequence from={30}>
    <AnimatedLine data={costToBuyData} color="#4A90D9" />
  </Sequence>
  <Sequence from={90}>
    <AnimatedLine data={costToRepairData} color="#D9944A" />
  </Sequence>
  <Sequence from={150}>
    <TimeProgression startYear={1950} endYear={1965} />
  </Sequence>
</Sequence>
```

## Data Points (Approximate)

```json
{
  "costToBuy": [
    { "year": 1950, "hours": 1.0 },
    { "year": 1955, "hours": 0.75 },
    { "year": 1960, "hours": 0.55 },
    { "year": 1963, "hours": 0.5 },
    { "year": 1970, "hours": 0.2 },
    { "year": 1980, "hours": 0.1 },
    { "year": 1990, "hours": 0.06 },
    { "year": 2000, "hours": 0.04 },
    { "year": 2010, "hours": 0.03 },
    { "year": 2020, "hours": 0.03 }
  ],
  "costToRepair": [
    { "year": 1950, "hours": 0.5 },
    { "year": 2020, "hours": 0.5 }
  ]
}
```

## Transition

Holds at crossing point, preparing for Section 1.2 highlight effect.
