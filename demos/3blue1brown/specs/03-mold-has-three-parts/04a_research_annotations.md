# Section 3.4a: Research Annotations on Mold Walls

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 11:15 - 11:30

## Visual Description

Research citation annotations appear next to the mold walls. First: "AI code: 1.7x more issues (CodeRabbit, 2025)" fades in as muted text beside the amber wall structure. Then: "AI + strong tests = amplified delivery (DORA, 2025)" appears below it. As the second citation lands, the mold walls glow brighter -- visually connecting the research to the importance of the walls/tests.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Continuing from the mold cross-section view established in 3.1-3.4

### Animation Elements

1. **Mold Walls (Persistent)**
   - Amber (#D9944A) wall segments from previous sections
   - Baseline glow level (moderate)
   - Labels like "null -> None" still faintly visible
   - Positioned center-left of frame

2. **Citation 1: CodeRabbit**
   - Text: "AI code: 1.7x more issues (CodeRabbit, 2025)"
   - Font: Sans-serif, 20px
   - Color: Muted white (#B0B0C0) at 70% opacity
   - Position: Right side of walls, top annotation slot
   - Subtle connecting line or bracket to nearest wall

3. **Citation 2: DORA**
   - Text: "AI + strong tests = amplified delivery (DORA, 2025)"
   - Font: Sans-serif, 20px
   - Color: Muted white (#B0B0C0) at 70% opacity
   - Position: Right side of walls, below Citation 1
   - "strong tests" highlighted in amber (#D9944A) to connect to the walls

4. **Wall Glow Intensification**
   - All mold walls increase glow from baseline to bright
   - Glow radius expands
   - Amber color saturates
   - Subtle pulse on the brighten moment

### Animation Sequence

1. **Frame 0-30 (0-1s):** Establish context
   - Mold walls visible at baseline glow
   - Scene continues from 3.4 (focus single wall)
   - Camera may be slightly pulled back to make room for annotations

2. **Frame 30-120 (1-4s):** Citation 1 appears
   - "AI code: 1.7x more issues" fades in from 0% to 70% opacity
   - "(CodeRabbit, 2025)" appears slightly after, staggered
   - Thin dotted line draws from citation to nearest wall segment
   - "1.7x" briefly highlighted brighter, then settles to muted

3. **Frame 120-150 (4-5s):** Brief hold
   - Both citation and walls visible
   - Walls still at baseline glow
   - Building anticipation

4. **Frame 150-270 (5-9s):** Citation 2 appears
   - "AI + strong tests = amplified delivery" fades in below first citation
   - "(DORA, 2025)" appears staggered
   - "strong tests" rendered in amber (#D9944A) instead of white
   - Arrow or bracket connecting "strong tests" to the wall structure

5. **Frame 270-360 (9-12s):** Walls glow brighter
   - All mold walls intensify from baseline to 2x glow
   - Glow radius expands (boxShadow spread increases)
   - Amber color deepens and saturates
   - Brief pulse at peak brightness, then holds at elevated level
   - Visual message: the research validates the wall design

6. **Frame 360-450 (12-15s):** Hold on brightened state
   - Walls at elevated glow
   - Both citations visible but clearly secondary
   - Ready for transition to narration about "walls aren't optional"

### Visual Design: Annotation Layout

```
+----------------------------------------------------------+
|                                                          |
|                                                          |
|      +============+     AI code: 1.7x more issues       |
|      ||          ||     (CodeRabbit, 2025)               |
|      || MOLD     ||........................              |
|      || WALLS    ||                                      |
|      || (amber)  ||     AI + strong tests =              |
|      ||          ||     amplified delivery                |
|      ||          ||     (DORA, 2025)                     |
|      +============+                                      |
|        ^^ glowing                                        |
|                                                          |
+----------------------------------------------------------+
  Citations: muted white     "strong tests": amber
  Small font, readable       Dotted lines connect to walls
```

### Code Structure (Remotion)

```typescript
const ResearchAnnotations: React.FC = () => {
  const frame = useCurrentFrame();

  // Citation 1 fade-in
  const citation1Opacity = interpolate(
    frame,
    [30, 90],
    [0, 0.7],
    { extrapolateRight: 'clamp' }
  );

  // "1.7x" emphasis flash
  const emphasisFlash = interpolate(
    frame,
    [60, 80, 120],
    [0.7, 1, 0.7],
    { extrapolateRight: 'clamp' }
  );

  // Citation 2 fade-in
  const citation2Opacity = interpolate(
    frame,
    [150, 210],
    [0, 0.7],
    { extrapolateRight: 'clamp' }
  );

  // Wall glow intensification
  const wallGlow = interpolate(
    frame,
    [270, 330],
    [0.4, 1.0],
    { extrapolateRight: 'clamp' }
  );

  // Brief pulse at peak
  const wallPulse = frame > 310 && frame < 360
    ? 1.0 + Math.sin((frame - 310) * 0.2) * 0.15
    : 1.0;

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Mold walls from previous sections */}
      <MoldWalls
        glowIntensity={wallGlow * wallPulse}
        showLabels={true}
        labelOpacity={0.3}
      />

      {/* Annotation area */}
      <div style={{
        position: 'absolute',
        right: 120,
        top: 280,
        width: 500,
      }}>
        {/* Citation 1: CodeRabbit */}
        <CitationText
          opacity={citation1Opacity}
          emphasisWord="1.7x"
          emphasisOpacity={emphasisFlash}
        >
          AI code: 1.7x more issues (CodeRabbit, 2025)
        </CitationText>

        {/* Dotted connector line */}
        <ConnectorLine
          opacity={citation1Opacity}
          style="dotted"
          from={{ x: 0, y: 12 }}
          to={{ x: -80, y: 12 }}
        />

        {/* Citation 2: DORA */}
        <div style={{ marginTop: 40 }}>
          <CitationText opacity={citation2Opacity}>
            AI +{' '}
            <span style={{ color: '#D9944A' }}>strong tests</span>
            {' '}= amplified delivery (DORA, 2025)
          </CitationText>
        </div>

        {/* Connector from "strong tests" to walls */}
        <ConnectorBracket
          opacity={citation2Opacity}
          targetLabel="strong tests"
          color="#D9944A"
          style="dotted"
        />
      </div>
    </AbsoluteFill>
  );
};
```

### Citation Text Component

```typescript
const CitationText: React.FC<{
  children: React.ReactNode;
  opacity: number;
  emphasisWord?: string;
  emphasisOpacity?: number;
}> = ({ children, opacity, emphasisWord, emphasisOpacity }) => {
  return (
    <div style={{
      fontSize: 20,
      fontFamily: 'Inter, sans-serif',
      color: '#B0B0C0',
      opacity,
      lineHeight: 1.5,
      letterSpacing: 0.3,
    }}>
      {typeof children === 'string' && emphasisWord
        ? children.split(emphasisWord).map((part, i, arr) => (
            <React.Fragment key={i}>
              {part}
              {i < arr.length - 1 && (
                <span style={{
                  color: '#FFFFFF',
                  fontWeight: 600,
                  opacity: emphasisOpacity ?? 1,
                }}>
                  {emphasisWord}
                </span>
              )}
            </React.Fragment>
          ))
        : children
      }
    </div>
  );
};
```

### Easing

- Citation fade-in: `easeOutCubic`
- Emphasis flash: `easeInOutSine`
- Wall glow intensification: `easeOutQuad`
- Wall pulse: Sinusoidal (manual Math.sin)
- Connector lines: `easeOutCubic` (draw on)

## Narration Sync

> "And these walls matter more than you'd think. CodeRabbit analyzed hundreds of pull requests and found AI-generated code produces one-point-seven times more issues than human code -- seventy-five percent more logic errors, eight times more performance problems. The 2025 DORA report confirmed it: AI without strong tests increases instability. AI *with* strong tests amplifies delivery."

- "one-point-seven times more issues" -- Citation 1 fully visible, "1.7x" flashes brighter
- "DORA report confirmed it" -- Citation 2 begins appearing
- "AI *with* strong tests amplifies delivery" -- Walls glow brighter on "amplifies delivery"

## Audio Notes

- Subtle text-appear sound (soft click or paper sound) for each citation
- Low, building ambient tone as walls prepare to brighten
- Warm resonant tone as walls glow intensifies -- "brightening" sound
- Walls hold a gentle hum at elevated glow level

## Visual Style Notes

- Citations are deliberately MUTED -- visible and readable, but not competing with the mold walls for attention
- The walls are the star; the citations provide evidence
- "strong tests" in amber creates a direct visual link between the DORA finding and the amber walls
- The glow intensification is the emotional payoff: research validates the design
- This is a "credibility moment" -- grounding the metaphor in real data
- The 3Blue1Brown style handles research citations as elegant, minimal annotations, never PowerPoint bullet points

## Transition

Continues directly into Section 3.4 (focus single wall) narration about "The walls aren't optional. They're what make regeneration safe." The elevated wall glow carries over.
