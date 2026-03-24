[Remotion]

# Section 4.3: Precision Tradeoff Curve — Tests vs Prompt Precision

**Tool:** Remotion
**Duration:** ~20s (601 frames @ 30fps)
**Timestamp:** 0:27 - 0:47

## Visual Description

A clean animated graph that forms the conceptual core of this section. The graph appears with a brief "This maps directly to PDD" text flash, then the inverse curve draws.

**X-axis:** "Number of Tests" (0 to 50+)
**Y-axis:** "Required Prompt Precision" (low to high)

An inverse/hyperbolic curve forms — starting high on the left (few tests = high prompt precision needed) and dropping toward the right (many tests = low prompt precision needed). The curve follows a 1/x shape.

After the curve draws, an animated dot travels along it. At the left extreme (few tests), a dense 50-line prompt document appears as a pop-out annotation. The dot moves right, and at the right extreme (many tests), a minimal 10-line prompt appears — but surrounded by a constellation of test wall icons. A terminal annotation shows `pdd test parser` with 47 tests passing.

The two scenarios are visually contrasted: heavy prompt vs heavy tests, both producing the same result.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Intro Text
- "This maps directly to PDD." — Inter, 32px, bold, `#E2E8F0` at 0.8, centered at (960, 540)
- Fades in and out quickly before graph appears

#### Graph Axes
- X-axis: horizontal line at y: 800, from x: 200 to x: 1720, `#334155` at 0.4, 2px
- Y-axis: vertical line at x: 200, from y: 200 to y: 800, `#334155` at 0.4, 2px
- X-label: "Number of Tests →" — Inter, 14px, `#94A3B8` at 0.6, at (960, 860)
- Y-label: "Required Prompt Precision →" — Inter, 14px, `#94A3B8` at 0.6, rotated -90° at (140, 500)
- X tick marks: 0, 10, 20, 30, 40, 50+ — Inter, 11px, `#64748B` at 0.4
- Y tick marks: Low, Medium, High — Inter, 11px, `#64748B` at 0.4

#### Inverse Curve
- Path: hyperbolic curve from (220, 240) to (1700, 760), stroke `#2DD4BF` at 0.8, 3px
- Fill below curve: gradient from `#2DD4BF` at 0.05 to transparent
- Curve equation approximation: y = 240 + 520 * (1 / (1 + 0.08 * x))

#### Animated Dot
- Circle, 10px radius, `#2DD4BF` at 1.0, with glow `#2DD4BF` at 0.3, 15px radius
- Travels along curve path from left to right

#### Left Annotation (Few Tests)
- Position: pop-out anchored at curve point (280, 280)
- Dense prompt document: 300×200px, bg `#0F1E1E`, border `#2DD4BF` at 0.3, rounded 6px
- Content: ~12 visible lines of dense text (simulated), Inter, 8px, `#2DD4BF` at 0.4
- File label: "`parser_v1.prompt` — 50 lines" — JetBrains Mono, 10px, `#2DD4BF` at 0.6
- Connector line: dashed, from curve point to annotation, `#2DD4BF` at 0.15

#### Right Annotation (Many Tests)
- Position: pop-out anchored at curve point (1500, 720)
- Minimal prompt document: 200×80px, bg `#0F1E1E`, border `#2DD4BF` at 0.3, rounded 6px
- Content: ~4 visible lines of text, Inter, 8px, `#2DD4BF` at 0.4
- File label: "`parser_v2.prompt` — 10 lines" — JetBrains Mono, 10px, `#2DD4BF` at 0.6
- Test wall icons: 12 small wall icons (8×16px each), `#D9944A` at 0.5, arranged in arc around prompt
- Terminal: small terminal block (250×60px), bg `#1E1E2E`, showing `pdd test parser` → "47 tests passing ✓", JetBrains Mono, 9px, `#4ADE80` at 0.6
- Connector line: dashed, from curve point to annotation, `#2DD4BF` at 0.15

### Animation Sequence
1. **Frame 0-45 (0-1.5s):** "This maps directly to PDD." fades in, holds, fades out.
2. **Frame 45-90 (1.5-3s):** Axes draw in. X and Y labels appear. Tick marks fade in.
3. **Frame 90-180 (3-6s):** Inverse curve draws from left to right with stroke-dashoffset animation. Subtle fill gradient below curve fades in.
4. **Frame 180-300 (6-10s):** Animated dot appears at far left of curve. Left annotation (dense 50-line prompt) pops out. Dot holds briefly. Narration: "With few tests, your prompt needs to specify everything."
5. **Frame 300-450 (10-15s):** Dot travels along curve toward the right. As it moves, left annotation fades. Right annotation (minimal prompt + test walls + terminal) pops out. Narration: "With many tests, the prompt only needs to specify intent."
6. **Frame 450-540 (15-18s):** Both annotations visible at reduced opacity. The curve pulses to emphasize the relationship.
7. **Frame 540-601 (18-20s):** Hold. Dot rests at right end. Test walls glow gently.

### Typography
- Intro text: Inter, 32px, bold (700), `#E2E8F0` at 0.8
- Axis labels: Inter, 14px, semi-bold (600), `#94A3B8` at 0.6
- Tick labels: Inter, 11px, `#64748B` at 0.4
- File labels: JetBrains Mono, 10px, `#2DD4BF` at 0.6
- Prompt content: Inter, 8px, `#2DD4BF` at 0.4
- Terminal text: JetBrains Mono, 9px, `#4ADE80` at 0.6

### Easing
- Intro text fade: `easeInOut(quad)` over 15 frames
- Axis draw: `easeOut(cubic)` over 30 frames
- Curve draw: `easeInOut(cubic)` over 90 frames
- Dot travel: `easeInOut(quad)` over 150 frames
- Annotation pop-out: `easeOut(back)` over 20 frames (slight spring)
- Annotation fade-out: `easeOut(quad)` over 15 frames
- Curve pulse: `easeInOut(sine)` on 40-frame cycle
- Test wall glow: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "This maps directly to PDD."
> "With few tests, your prompt needs to specify everything. Edge cases. Error handling. Exact behavior in every situation."
> "On... With many tests, the prompt only needs to specify intent. The tests handle the constraints."

Segments: `part4_precision_tradeoff_004`, `part4_precision_tradeoff_005`, `part4_precision_tradeoff_006`

- **0:27** ("This maps directly"): Intro text flash
- **0:30** ("With few tests"): Dot at left end, dense prompt annotation visible
- **0:35** ("Edge cases"): Dot beginning to move right
- **0:40** ("With many tests"): Dot arriving at right end, minimal prompt + tests visible
- **0:45** ("tests handle the constraints"): Both annotations visible, curve pulsing

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={601}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.03} />

    {/* Intro text */}
    <Sequence from={0} durationInFrames={45}>
      <FadeInOut fadeIn={15} fadeOut={15} hold={15}>
        <Text text="This maps directly to PDD." font="Inter" size={32}
          weight={700} color="#E2E8F0" opacity={0.8}
          x={960} y={540} align="center" />
      </FadeInOut>
    </Sequence>

    {/* Axes */}
    <Sequence from={45}>
      <StrokeDraw duration={30}>
        <Axis orientation="horizontal" from={[200, 800]} to={[1720, 800]}
          color="#334155" opacity={0.4} width={2}
          label="Number of Tests →" labelFont="Inter" labelSize={14} />
        <Axis orientation="vertical" from={[200, 800]} to={[200, 200]}
          color="#334155" opacity={0.4} width={2}
          label="Required Prompt Precision →" labelFont="Inter" labelSize={14} />
      </StrokeDraw>
      <Sequence from={20}>
        <FadeIn duration={15}>
          <TickMarks axis="x" values={["0", "10", "20", "30", "40", "50+"]}
            font="Inter" size={11} color="#64748B" />
          <TickMarks axis="y" values={["Low", "Medium", "High"]}
            font="Inter" size={11} color="#64748B" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Inverse curve */}
    <Sequence from={90}>
      <StrokeDraw duration={90}>
        <CurvePath d={INVERSE_CURVE_PATH} stroke="#2DD4BF" strokeWidth={3} opacity={0.8} />
      </StrokeDraw>
      <Sequence from={60}>
        <FadeIn duration={30}>
          <CurveFill d={INVERSE_CURVE_PATH} fill="#2DD4BF" opacity={0.05}
            gradient="toBottom" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Animated dot with annotations */}
    <Sequence from={180}>
      <AnimatedDot path={INVERSE_CURVE_PATH} travelDuration={150}
        startFrame={0} radius={10} color="#2DD4BF"
        glow="#2DD4BF" glowRadius={15} glowOpacity={0.3}>
        {/* Left annotation — dense prompt */}
        <Annotation anchor="left" fadeIn={20} fadeOut={15}
          visibleFrom={0} visibleUntil={200}>
          <PromptDocument width={300} height={200} bg="#0F1E1E"
            border="#2DD4BF" lines={12}
            fileLabel="parser_v1.prompt — 50 lines" />
        </Annotation>
        {/* Right annotation — minimal prompt + tests */}
        <Annotation anchor="right" fadeIn={20}
          visibleFrom={120}>
          <PromptDocument width={200} height={80} bg="#0F1E1E"
            border="#2DD4BF" lines={4}
            fileLabel="parser_v2.prompt — 10 lines" />
          <TestWallIcons count={12} color="#D9944A" arrangement="arc" />
          <TerminalBlock width={250} height={60}
            command="pdd test parser" output="47 tests passing ✓"
            outputColor="#4ADE80" />
        </Annotation>
      </AnimatedDot>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartId": "precision_tradeoff_curve",
  "axes": {
    "x": { "label": "Number of Tests", "range": [0, 50], "ticks": ["0", "10", "20", "30", "40", "50+"] },
    "y": { "label": "Required Prompt Precision", "range": ["Low", "High"], "ticks": ["Low", "Medium", "High"] }
  },
  "curve": {
    "type": "inverse_hyperbolic",
    "color": "#2DD4BF",
    "strokeWidth": 3
  },
  "annotations": {
    "left": {
      "label": "parser_v1.prompt — 50 lines",
      "description": "Dense prompt, few tests",
      "position": "high_precision"
    },
    "right": {
      "label": "parser_v2.prompt — 10 lines",
      "description": "Minimal prompt, 47 tests",
      "testCount": 47,
      "position": "low_precision"
    }
  },
  "introText": "This maps directly to PDD.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_precision_tradeoff_004", "part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]
}
```

---
