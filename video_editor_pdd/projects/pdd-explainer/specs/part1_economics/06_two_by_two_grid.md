[Remotion]

# Section 1.5: Two-by-Two Grid — Why Studies Contradict

**Tool:** Remotion
**Duration:** ~25s (750 frames @ 30fps)
**Timestamp:** 4:27 - 4:52

## Visual Description

The context window visualization dissolves and a clean 2×2 quadrant grid materializes. This is the explanatory framework for why AI productivity studies seem to contradict each other.

- **X-axis:** "Greenfield → Brownfield" (left to right)
- **Y-axis:** "In-Distribution → Out-of-Distribution" (top to bottom)
- **Top-left quadrant** glows green: "GitHub study: +55%" — easy tasks on fresh code
- **Bottom-right quadrant** glows red: "METR study: −19%" — hard tasks on mature codebases
- **Top-right and bottom-left** are intermediate colors (amber)

Below the grid: "Every study is correct. They just measured different quadrants."

A dotted circle appears in the bottom-right quadrant labeled "Most enterprise work lives here" — driving home that the optimistic studies measured the exception, not the rule.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117`
- Grid area: centered, 640x640, positioned at (640, 180) to (1280, 820)

### Chart/Visual Elements

#### Quadrant Grid
- Outer border: `#334155` at 0.3, 2px
- Cross dividers: `#334155` at 0.2, 1px at x: 960 (vertical) and y: 500 (horizontal)
- Grid background: `#0D1117`

#### Axis Labels
- X-axis left: "Greenfield" — Inter, 14px, semi-bold, `#5AAA6E` at 0.6
- X-axis right: "Brownfield" — Inter, 14px, semi-bold, `#E74C3C` at 0.6
- Y-axis top: "In-Distribution" — Inter, 14px, semi-bold, `#5AAA6E` at 0.6
- Y-axis bottom: "Out-of-Distribution" — Inter, 14px, semi-bold, `#E74C3C` at 0.6
- Arrow indicators: subtle gradient arrows along axes

#### Top-Left Quadrant (Greenfield × In-Distribution)
- Background glow: `#5AAA6E` at 0.08
- Text: "GitHub study" — Inter, 13px, bold, `#5AAA6E` at 0.7
- Stat: "+55%" — Inter, 32px, bold, `#5AAA6E` at 0.85
- Subtext: "95 devs, greenfield" — Inter, 9px, `#94A3B8` at 0.35

#### Bottom-Right Quadrant (Brownfield × Out-of-Distribution)
- Background glow: `#E74C3C` at 0.08
- Text: "METR study" — Inter, 13px, bold, `#E74C3C` at 0.7
- Stat: "−19%" — Inter, 32px, bold, `#E74C3C` at 0.85
- Subtext: "experienced devs, mature repos" — Inter, 9px, `#94A3B8` at 0.35

#### Top-Right Quadrant (Brownfield × In-Distribution)
- Background: `#D9944A` at 0.04
- Text: "Mixed results" — Inter, 11px, `#D9944A` at 0.4

#### Bottom-Left Quadrant (Greenfield × Out-of-Distribution)
- Background: `#D9944A` at 0.04
- Text: "Mixed results" — Inter, 11px, `#D9944A` at 0.4

#### Enterprise Work Indicator
- Dotted circle: 100px radius, `#E74C3C` at 0.3, 2px dashed
- Position: centered in bottom-right quadrant
- Label: "Most enterprise work" — Inter, 10px, `#E74C3C` at 0.5, below circle

#### Summary Line
- "Every study is correct. They just measured different quadrants." — Inter, 16px, weight 400, `#E2E8F0` at 0.7
- Positioned below grid at y: 880, centered

### Animation Sequence
1. **Frame 0-30 (0-1s):** Previous visualization fades out. Background clears.
2. **Frame 30-90 (1-3s):** Grid border and cross dividers draw in. Axis labels fade in at endpoints.
3. **Frame 90-180 (3-6s):** Top-left quadrant glows green. GitHub "+55%" appears with a scale-up animation.
4. **Frame 180-270 (6-9s):** Bottom-right quadrant glows red. METR "−19%" appears with scale-up.
5. **Frame 270-330 (9-11s):** Intermediate quadrants tint amber. "Mixed results" labels appear.
6. **Frame 330-420 (11-14s):** Enterprise work dotted circle draws in bottom-right. Label appears.
7. **Frame 420-480 (14-16s):** Summary line fades in below the grid.
8. **Frame 480-750 (16-25s):** Hold. The framework sits with explanatory clarity.

### Typography
- Axis labels: Inter, 14px, semi-bold, respective colors at 0.6
- Study names: Inter, 13px, bold, respective colors at 0.7
- Statistics: Inter, 32px, bold, respective colors at 0.85
- Subtexts: Inter, 9px, `#94A3B8` at 0.35
- Summary: Inter, 16px, weight 400, `#E2E8F0` at 0.7

### Easing
- Grid draw: `easeOut(cubic)` over 30 frames
- Quadrant glow fill: `easeOut(quad)` over 20 frames
- Stat scale-up: `easeOut(back)` over 20 frames (slight overshoot for emphasis)
- Enterprise circle draw: `easeOut(cubic)` over 25 frames (dashed circle draws clockwise)
- Summary fade-in: `easeOut(quad)` over 20 frames

## Narration Sync
> "The GitHub study measured greenfield, in-distribution work — exactly where AI shines. The METR study measured brownfield, out-of-distribution work — where AI flounders. They're not contradictory. They're measuring different quadrants. And most real enterprise work? It lives in the bottom-right."

Segments: `part1_economics_021`, `part1_economics_022`

- **4:27** ("GitHub study measured"): Top-left quadrant glows green, +55%
- **4:33** ("METR study measured"): Bottom-right quadrant glows red, −19%
- **4:38** ("They're not contradictory"): Full grid visible
- **4:42** ("most real enterprise work"): Enterprise circle appears in bottom-right
- **4:45** ("lives in the bottom-right"): Summary line appears

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={750}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Grid structure */}
    <Sequence from={30}>
      <QuadrantGrid
        x={640} y={180} width={640} height={640}
        borderColor="#334155" dividerColor="#334155"
        xLabels={{ left: "Greenfield", right: "Brownfield" }}
        yLabels={{ top: "In-Distribution", bottom: "Out-of-Distribution" }}
        drawDuration={30}
      />
    </Sequence>

    {/* Top-left: GitHub */}
    <Sequence from={90}>
      <QuadrantFill quadrant="top-left" color="#5AAA6E" opacity={0.08}>
        <ScaleUp duration={20}>
          <Text text="+55%" font="Inter" size={32}
            weight={700} color="#5AAA6E" />
        </ScaleUp>
        <Text text="GitHub study" font="Inter" size={13}
          weight={700} color="#5AAA6E" opacity={0.7} />
        <Text text="95 devs, greenfield" font="Inter" size={9}
          color="#94A3B8" opacity={0.35} />
      </QuadrantFill>
    </Sequence>

    {/* Bottom-right: METR */}
    <Sequence from={180}>
      <QuadrantFill quadrant="bottom-right" color="#E74C3C" opacity={0.08}>
        <ScaleUp duration={20}>
          <Text text="−19%" font="Inter" size={32}
            weight={700} color="#E74C3C" />
        </ScaleUp>
        <Text text="METR study" font="Inter" size={13}
          weight={700} color="#E74C3C" opacity={0.7} />
        <Text text="experienced devs, mature repos" font="Inter" size={9}
          color="#94A3B8" opacity={0.35} />
      </QuadrantFill>
    </Sequence>

    {/* Enterprise work circle */}
    <Sequence from={330}>
      <DashedCircle
        cx={quadrantBottomRightCenterX}
        cy={quadrantBottomRightCenterY}
        radius={100} color="#E74C3C" opacity={0.3}
        strokeWidth={2} drawDuration={25}
        label="Most enterprise work"
      />
    </Sequence>

    {/* Summary line */}
    <Sequence from={420}>
      <FadeIn duration={20}>
        <Text text="Every study is correct. They just measured different quadrants."
          font="Inter" size={16} weight={400}
          color="#E2E8F0" opacity={0.7}
          x={960} y={880} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "quadrant_grid",
  "chartType": "two_by_two_study_comparison",
  "axes": {
    "x": { "left": "Greenfield", "right": "Brownfield" },
    "y": { "top": "In-Distribution", "bottom": "Out-of-Distribution" }
  },
  "quadrants": [
    {
      "position": "top-left",
      "study": "GitHub, 2022",
      "stat": "+55%",
      "color": "#5AAA6E",
      "detail": "95 devs, greenfield"
    },
    {
      "position": "bottom-right",
      "study": "METR, 2025",
      "stat": "−19%",
      "color": "#E74C3C",
      "detail": "experienced devs, mature repos"
    },
    {
      "position": "top-right",
      "label": "Mixed results",
      "color": "#D9944A"
    },
    {
      "position": "bottom-left",
      "label": "Mixed results",
      "color": "#D9944A"
    }
  ],
  "enterpriseIndicator": {
    "quadrant": "bottom-right",
    "label": "Most enterprise work",
    "radius": 100,
    "color": "#E74C3C"
  },
  "summary": "Every study is correct. They just measured different quadrants.",
  "backgroundColor": "#0D1117",
  "narrationSegments": ["part1_economics_021", "part1_economics_022"]
}
```

---
