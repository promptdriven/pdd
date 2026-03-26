[Remotion]

# Section 3.5: Research Annotations — CodeRabbit & DORA Data Overlay

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 0:48 - 1:02

## Visual Description

A data-overlay screen presenting two key research findings that justify the importance of test walls. The mold cross-section persists in the background at low opacity — the walls region subtly visible.

First annotation materializes: "AI code: 1.7× more issues (CodeRabbit, 2025)" — positioned next to the mold walls with a callout line. Below it, supporting stats: "75% more logic errors" and "8× more performance problems" appear as subordinate data points.

Then a second annotation appears below: "AI + strong tests = amplified delivery (DORA, 2025)." This one glows brighter — it's the payoff. The walls in the background glow brighter in response, reinforcing that tests are the differentiator.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Background Mold (dimmed)
- Same mold cross-section from 02, walls region at 0.15 opacity
- Other regions at 0.05 opacity

#### Annotation 1 — CodeRabbit Finding
- Position: centered at (700, 350)
- Main text: "AI code: 1.7× more issues" — Inter, 24px, bold, `#EF4444` at 0.8
- Source: "(CodeRabbit, 2025)" — Inter, 14px, `#94A3B8` at 0.5
- Supporting stats:
  - "75% more logic errors" — Inter, 16px, `#EF4444` at 0.6, y: +40
  - "8× more performance problems" — Inter, 16px, `#EF4444` at 0.6, y: +65
- Callout line: 1px, `#EF4444` at 0.2, connecting to mold walls

#### Annotation 2 — DORA Finding
- Position: centered at (700, 600)
- Main text: "AI + strong tests = amplified delivery" — Inter, 24px, bold, `#4ADE80` at 0.8
- Source: "(DORA, 2025)" — Inter, 14px, `#94A3B8` at 0.5
- Green glow: 20px radius, `#4ADE80` at 0.08

#### Wall Glow Response
- When DORA annotation appears, mold walls brighten from 0.15 to 0.4
- Subtle pulse on walls, `#D9944A` at 0.4

### Animation Sequence
1. **Frame 0-30 (0-1s):** Background mold visible at low opacity. Stage set.
2. **Frame 30-120 (1-4s):** Annotation 1 types in. "1.7×" scales up with emphasis. Supporting stats fade in below.
3. **Frame 120-180 (4-6s):** Callout line draws from annotation to walls. Brief pause.
4. **Frame 180-300 (6-10s):** Annotation 2 appears. "amplified delivery" glows green. DORA source fades in.
5. **Frame 300-360 (10-12s):** Mold walls brighten in response. Green glow blooms on annotation 2.
6. **Frame 360-420 (12-14s):** Hold. Both annotations visible. Walls glowing.

### Typography
- Main annotations: Inter, 24px, bold (700), respective colors
- Sources: Inter, 14px, `#94A3B8` at 0.5
- Supporting stats: Inter, 16px, `#EF4444` at 0.6
- "1.7×" and "8×" numerals: slightly larger (28px) for emphasis

### Easing
- Text type-in: `easeOut(quad)` over 30 frames
- Stat emphasis scale: `easeOut(back)` over 15 frames (1.0→1.15→1.0)
- Callout line draw: `easeOut(quad)` over 20 frames
- Green glow bloom: `easeOut(cubic)` over 30 frames
- Wall brighten: `easeOut(cubic)` over 30 frames

## Narration Sync
> "And these walls matter more than you'd think. CodeRabbit analyzed hundreds of pull requests and found AI-generated code produces one-point-seven times more issues than human code — seventy-five percent more logic errors, eight times more performance problems."
> "The 2025 DORA report confirmed it: AI without strong tests increases instability. AI with strong tests amplifies delivery."

Segments: `part3_mold_has_three_parts_007`, `part3_mold_has_three_parts_008`

- **0:48** ("walls matter"): CodeRabbit annotation begins appearing
- **0:53** ("one-point-seven times"): "1.7×" emphasized
- **0:58** ("DORA report confirmed"): DORA annotation appears, walls glow

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.03} />
    <MoldOutline cx={960} cy={540} wallsOpacity={0.15} othersOpacity={0.05} />

    {/* Annotation 1: CodeRabbit */}
    <Sequence from={30}>
      <TypeIn duration={30}>
        <Text text="AI code: 1.7× more issues"
          font="Inter" size={24} weight={700} color="#EF4444" opacity={0.8}
          x={700} y={350} align="center" />
      </TypeIn>
      <FadeIn duration={15} delay={30}>
        <Text text="(CodeRabbit, 2025)" font="Inter" size={14}
          color="#94A3B8" opacity={0.5} x={700} y={380} align="center" />
      </FadeIn>
      <Sequence from={60}>
        <FadeIn duration={15}>
          <Text text="75% more logic errors" font="Inter" size={16}
            color="#EF4444" opacity={0.6} x={700} y={415} align="center" />
          <Text text="8× more performance problems" font="Inter" size={16}
            color="#EF4444" opacity={0.6} x={700} y={440} align="center" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Callout line */}
    <Sequence from={120}>
      <DrawLine from={[850, 380]} to={[1050, 450]}
        color="#EF4444" opacity={0.2} width={1}
        drawDuration={20} />
    </Sequence>

    {/* Annotation 2: DORA */}
    <Sequence from={180}>
      <FadeIn duration={30}>
        <GlowBox color="#4ADE80" opacity={0.08} radius={20}>
          <Text text="AI + strong tests = amplified delivery"
            font="Inter" size={24} weight={700} color="#4ADE80" opacity={0.8}
            x={700} y={600} align="center" />
        </GlowBox>
        <Text text="(DORA, 2025)" font="Inter" size={14}
          color="#94A3B8" opacity={0.5} x={700} y={635} align="center" />
      </FadeIn>
    </Sequence>

    {/* Wall glow response */}
    <Sequence from={300}>
      <AnimateOpacity from={0.15} to={0.4} duration={30}>
        <MoldWalls color="#D9944A" />
      </AnimateOpacity>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "annotation_overlay",
  "diagramId": "research_annotations",
  "annotations": [
    {
      "id": "coderabbit",
      "headline": "AI code: 1.7× more issues",
      "source": "CodeRabbit, 2025",
      "color": "#EF4444",
      "subStats": ["75% more logic errors", "8× more performance problems"]
    },
    {
      "id": "dora",
      "headline": "AI + strong tests = amplified delivery",
      "source": "DORA, 2025",
      "color": "#4ADE80"
    }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_has_three_parts_007", "part3_mold_has_three_parts_008"]
}
```

---
