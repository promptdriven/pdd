[Remotion]

# Section 1.5: Productivity Quadrant — The 2×2 Grid

**Tool:** Remotion
**Duration:** ~30s
**Timestamp:** 2:58 – 3:28

## Visual Description
A clean 2×2 quadrant grid resolves the apparent contradiction between AI productivity studies. The X-axis goes from "Greenfield" to "Brownfield", the Y-axis from "In-Distribution" to "Out-of-Distribution." Each quadrant fills in with a color and a study citation. Top-left (greenfield, in-distribution) glows green with "+55% (GitHub)". Bottom-right (brownfield, out-of-distribution) glows red with "-19% (METR)". The other two quadrants are neutral. A pulsing highlight on the bottom-right quadrant with the label "Most real enterprise work lives here" drives home the key point.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F1923 (dark blue-black)
- No grid lines (the quadrant IS the grid)

### Chart/Visual Elements
- **Quadrant container:** 800×600px, centered on screen
- **Dividing lines:** 2px, #FFFFFF at 30% opacity, forming the cross
- **X-axis label (bottom):** "Greenfield" (left) ←→ "Brownfield" (right)
- **Y-axis label (left):** "In-Distribution" (top) ←→ "Out-of-Distribution" (bottom)
- **Quadrant fills:**
  - **Top-Left (Greenfield + In-Dist):** #22C55E at 15% opacity fill → "+55%" in large text, "GitHub, 2022" below, "95 devs · HTTP server" fine print
  - **Top-Right (Brownfield + In-Dist):** #F59E0B at 8% opacity fill → "~0%" in medium text, "mixed results" below
  - **Bottom-Left (Greenfield + Out-of-Dist):** #F59E0B at 8% opacity fill → "variable" in medium text
  - **Bottom-Right (Brownfield + Out-of-Dist):** #EF4444 at 15% opacity fill → "-19%" in large text, "METR, 2025" below, "experienced devs · mature repos" fine print
- **Highlight ring:** Animated dashed border around bottom-right quadrant, #EF4444, 3px, slowly rotating dash pattern
- **Callout label:** "Most real enterprise work lives here" — positioned below the bottom-right quadrant with an arrow pointing into it
- **Summary text (bottom of screen):** "Every study is correct. They just measured different quadrants."

### Animation Sequence
1. **Frame 0–30 (0–1s):** The cross (dividing lines) draws on — horizontal first, then vertical. Axis labels fade in.
2. **Frame 30–90 (1–3s):** Top-left quadrant fills green. "+55%" counts up from 0. "GitHub, 2022" fades in. Synced with "The GitHub study measured greenfield, in-distribution work..."
3. **Frame 90–180 (3–6s):** Slight pause. Then bottom-right quadrant fills red. "-19%" counts down from 0. "METR, 2025" fades in. Synced with "The METR study measured brownfield, out-of-distribution work..."
4. **Frame 180–270 (6–9s):** Top-right and bottom-left quadrants fill with neutral amber, very subtly. Their labels appear.
5. **Frame 270–420 (9–14s):** Summary text types on at the bottom. The word "different quadrants" is highlighted in white while the rest is #8B9DC3. Synced with "They're not contradictory. They're measuring different quadrants."
6. **Frame 420–600 (14–20s):** Animated highlight ring appears around bottom-right quadrant. Callout "Most real enterprise work lives here" slides in from right with spring animation.
7. **Frame 600–780 (20–26s):** Top-left quadrant dims slightly (opacity drops to 50%). Bottom-right quadrant brightens. Visual emphasis shifts to where real work happens.
8. **Frame 780–900 (26–30s):** Hold. Ambient animation: the rotating dashed border continues, "+55%" and "-19%" pulse gently in alternation.

### Typography
- Axis labels: Inter Medium, 16px, #8B9DC3
- Quadrant metric (±%): Inter Bold, 48px, matching quadrant color (green/red)
- Study citation: Inter Medium, 16px, #FFFFFF at 80% opacity
- Fine print: Inter Regular, 12px, #6B7C93
- Summary text: Inter SemiBold, 22px, #8B9DC3 (with "different quadrants" in #FFFFFF)
- Callout: Inter SemiBold, 18px, #EF4444

### Easing
- Cross draw-on: `easeInOutCubic`
- Quadrant fill: `easeOutCubic` (400ms)
- Number count: `easeOutExpo` (800ms)
- Summary type-on: linear (30ms per character)
- Highlight ring rotation: linear (continuous, 8s per revolution)
- Callout slide-in: `spring({ damping: 12, stiffness: 100 })`

## Narration Sync
> "This is why AI-assisted patching is really two stories — and why every productivity study seems to contradict every other one."

> "The GitHub study measured greenfield, in-distribution work — exactly where AI shines. The METR study measured brownfield, out-of-distribution work — where AI flounders. They're not contradictory. They're measuring different quadrants. And most real enterprise work? It lives in the bottom-right."

Segments: `part1_economics_022` (236.0s – ~240s), `part1_economics_023` (~240s – ~260s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={900}>
  <AbsoluteFill style={{ backgroundColor: '#0F1923' }}>
    {/* Axes and cross */}
    <Sequence from={0} durationInFrames={30}>
      <DrawOnCross />
      <FadeIn><AxisLabels /></FadeIn>
    </Sequence>

    {/* Quadrant fills */}
    <Sequence from={30} durationInFrames={60}>
      <QuadrantFill
        position="top-left"
        color="#22C55E"
        metric="+55%"
        source="GitHub, 2022"
        detail="95 devs · HTTP server"
      />
    </Sequence>

    <Sequence from={90} durationInFrames={90}>
      <QuadrantFill
        position="bottom-right"
        color="#EF4444"
        metric="-19%"
        source="METR, 2025"
        detail="experienced devs · mature repos"
      />
    </Sequence>

    <Sequence from={180} durationInFrames={90}>
      <QuadrantFill position="top-right" color="#F59E0B" metric="~0%" />
      <QuadrantFill position="bottom-left" color="#F59E0B" metric="variable" />
    </Sequence>

    {/* Summary text */}
    <Sequence from={270} durationInFrames={150}>
      <TypeOnText text="Every study is correct. They just measured different quadrants." />
    </Sequence>

    {/* Bottom-right highlight */}
    <Sequence from={420} durationInFrames={480}>
      <RotatingDashBorder quadrant="bottom-right" color="#EF4444" />
      <SlideInCallout text="Most real enterprise work lives here" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "quadrants": [
    {
      "position": "top-left",
      "xAxis": "Greenfield",
      "yAxis": "In-Distribution",
      "metric": "+55%",
      "source": "GitHub, 2022",
      "color": "green"
    },
    {
      "position": "top-right",
      "xAxis": "Brownfield",
      "yAxis": "In-Distribution",
      "metric": "~0%",
      "source": "mixed",
      "color": "amber"
    },
    {
      "position": "bottom-left",
      "xAxis": "Greenfield",
      "yAxis": "Out-of-Distribution",
      "metric": "variable",
      "source": "mixed",
      "color": "amber"
    },
    {
      "position": "bottom-right",
      "xAxis": "Brownfield",
      "yAxis": "Out-of-Distribution",
      "metric": "-19%",
      "source": "METR, 2025",
      "color": "red"
    }
  ]
}
```
