[Remotion]

# Section 3.5: Research Annotations — AI Code Quality Stats

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 1:08 - 1:26

## Visual Description

The mold cross-section remains visible in the background at reduced opacity. Two research stat annotations appear as floating cards, one after the other, adjacent to the glowing wall region:

**Card 1:** "AI code: 1.7× more issues" with sub-text "(CodeRabbit, 2025)" — appears with a red-warning tint, emphasizing the problem.

**Card 2:** "AI + strong tests = amplified delivery" with sub-text "(DORA, 2025)" — appears with a green-positive tint. As this card appears, all the mold walls glow brighter, visually connecting "strong tests" to the mold walls.

Between the two cards, a subtle visual transition: the walls dim briefly (the problem), then brighten dramatically (the solution). A terminal overlay in the lower-right shows scrolling test output with green checkmarks.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Mold (background)
- Same cross-section from 02/03, opacity reduced to 0.2
- Walls visible but subdued

#### Annotation Card 1 — Warning
- Position: (1300, 300), 400×120px
- Background: `#1E1015` (dark red tint), border `#EF4444` at 0.3, 1px, rounded 8px
- Icon: Warning triangle `#EF4444` at 0.6, 20px, left of text
- Main text: "AI code: 1.7× more issues" — Inter, 20px, bold, `#EF4444`
- Sub-text: "CodeRabbit, 2025" — Inter, 12px, `#94A3B8` at 0.5
- Stats below: "75% more logic errors · 8× more perf problems" — Inter, 11px, `#EF4444` at 0.4

#### Annotation Card 2 — Positive
- Position: (1300, 480), 400×120px
- Background: `#0F1E15` (dark green tint), border `#4ADE80` at 0.3, 1px, rounded 8px
- Icon: Checkmark circle `#4ADE80` at 0.6, 20px, left of text
- Main text: "AI + strong tests = amplified delivery" — Inter, 20px, bold, `#4ADE80`
- Sub-text: "DORA, 2025" — Inter, 12px, `#94A3B8` at 0.5

#### Wall Glow Effect
- When Card 2 appears, walls transition from `#D9944A` at 0.2 to `#D9944A` at 0.8
- Glow radius increases from 0 to 20px

### Animation Sequence
1. **Frame 0-30 (0-1s):** Mold background settles at low opacity. Scene establishes.
2. **Frame 30-120 (1-4s):** Card 1 slides in from right with a fade. Warning tint. Walls dim slightly to 0.15.
3. **Frame 120-180 (4-6s):** Hold on Card 1. The problem sinks in.
4. **Frame 180-300 (6-10s):** Card 2 slides in below Card 1. Green tint. Simultaneously, all walls glow brighter — from 0.15 to 0.8. The connection is visceral: tests are the answer.
5. **Frame 300-420 (10-14s):** Both cards visible. Walls pulsing at full brightness. The annotation "The walls aren't optional" appears at bottom.
6. **Frame 420-540 (14-18s):** Hold. Terminal overlay appears in lower-right showing `✓ test_null_handling`, `✓ test_unicode`, checkmarks accumulating.

### Typography
- Card 1 main: Inter, 20px, bold (700), `#EF4444`
- Card 1 sub: Inter, 12px, `#94A3B8` at 0.5
- Card 2 main: Inter, 20px, bold (700), `#4ADE80`
- Card 2 sub: Inter, 12px, `#94A3B8` at 0.5
- Bottom annotation: Inter, 14px, italic, `#E2E8F0` at 0.6
- Terminal text: JetBrains Mono, 11px, `#4ADE80` at 0.5

### Easing
- Card slide-in: `easeOut(cubic)` over 30 frames, 20px from right
- Wall glow transition: `easeOut(cubic)` over 40 frames
- Wall pulse: `easeInOut(sine)` on 40-frame cycle
- Terminal lines: stagger 10 frames apart

## Narration Sync
> "And these walls matter more than you'd think. CodeRabbit analyzed hundreds of pull requests and found AI-generated code produces one-point-seven times more issues than human code—seventy-five percent more logic errors, eight times more performance problems. The 2025 DORA report confirmed it: AI without strong tests increases instability. AI with strong tests amplifies delivery."
> "The walls aren't optional. They're what make regeneration safe."

Segments: `part3_mold_three_parts_009`, `part3_mold_three_parts_010`

- **1:08** ("these walls matter"): Card 1 slides in — warning stat
- **1:21** ("AI with strong tests"): Card 2 slides in — walls glow brighter
- **1:36** ("walls aren't optional"): Both cards visible, walls pulsing

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.05} />
    <MoldOutline cx={960} cy={540} opacity={0.2} />

    {/* Card 1: Warning */}
    <Sequence from={30}>
      <SlideIn fromX={20} duration={30}>
        <AnnotationCard
          x={1300} y={300} width={400} height={120}
          bg="#1E1015" border="#EF4444" borderOpacity={0.3}
          icon="warning" iconColor="#EF4444"
          title="AI code: 1.7× more issues"
          titleColor="#EF4444"
          subtitle="CodeRabbit, 2025"
          detail="75% more logic errors · 8× more perf problems" />
      </SlideIn>
    </Sequence>

    {/* Card 2: Positive + Wall glow */}
    <Sequence from={180}>
      <SlideIn fromX={20} duration={30}>
        <AnnotationCard
          x={1300} y={480} width={400} height={120}
          bg="#0F1E15" border="#4ADE80" borderOpacity={0.3}
          icon="check_circle" iconColor="#4ADE80"
          title="AI + strong tests = amplified delivery"
          titleColor="#4ADE80"
          subtitle="DORA, 2025" />
      </SlideIn>
      <WallGlow from={0.15} to={0.8} duration={40} pulse={40} />
    </Sequence>

    {/* Terminal overlay */}
    <Sequence from={420}>
      <TerminalOverlay
        x={1400} y={800} width={400} height={200}
        lines={["✓ test_null_handling", "✓ test_unicode", "✓ test_empty_string", "✓ test_latency"]}
        stagger={10} font="JetBrains Mono" fontSize={11}
        color="#4ADE80" opacity={0.5} />
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
      "id": "coderabbit_stat",
      "type": "warning",
      "stat": "1.7×",
      "text": "AI code: 1.7× more issues",
      "source": "CodeRabbit, 2025",
      "detail": "75% more logic errors, 8× more perf problems",
      "color": "#EF4444"
    },
    {
      "id": "dora_stat",
      "type": "positive",
      "text": "AI + strong tests = amplified delivery",
      "source": "DORA, 2025",
      "color": "#4ADE80"
    }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_three_parts_009", "part3_mold_three_parts_010"]
}
```

---
