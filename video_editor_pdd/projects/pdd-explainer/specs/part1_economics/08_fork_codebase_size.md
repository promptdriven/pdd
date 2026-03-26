[Remotion]

# Section 1.8: Fork by Codebase Size — Diverging Patch Cost Paths

**Tool:** Remotion
**Duration:** ~22s (660 frames @ 30fps)
**Timestamp:** 4:18 - 4:40

## Visual Description

The main code cost chart returns, but now the amber "immediate patch cost" line FORKS into two paths at 2020. This is the visual realization that "same tools, different results" has a specific cause: codebase size.

- **Lower fork ("Small codebase"):** Plunges downward — AI-assisted patching is genuinely faster on small, clean repos. The line drops steeply.
- **Upper fork ("Large codebase"):** Stays flat at ~10-12 hours. Despite the same AI tools, large codebases don't see the speed improvements.

Annotations appear sequentially:
1. "METR, 2025: experienced devs 19% slower on mature repos" — pointing to the flat upper fork.
2. "Developers believed AI saved 20%. It cost 19%." — a devastating second annotation that fades in below the first.
3. An arrow curving from the lower fork upward toward the upper fork, with the label "Every patch adds code." — showing the inevitability of small codebases becoming large ones.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Inherits chart from Spec 03

### Chart/Visual Elements

#### Forking Lines (replacing single amber solid line from 2020 onward)
- **Lower fork ("Small codebase"):**
  - Color: `#22C55E`, 3px solid
  - Data from fork point: (2020, 2.5), (2022, 1.2), (2024, 0.4), (2025, 0.2)
  - Label: "Small codebase" — Inter, 13px, `#22C55E`
- **Upper fork ("Large codebase"):**
  - Color: `#EF4444`, 3px solid
  - Data from fork point: (2020, 2.5), (2022, 2.8), (2024, 3.0), (2025, 3.2)
  - Label: "Large codebase" — Inter, 13px, `#EF4444`
- Fork point at (2020, 2.5): small dot `#D9944A`, 6px

#### Fork Annotation
- "Same tools. Different codebase sizes." — Inter, 14px, `#E2E8F0` at 0.6
- Positioned near fork point

#### METR Annotation
- "METR, 2025: experienced devs 19% slower on mature repos"
  - Inter, 12px, `#EF4444` at 0.7
  - Connecting line to upper fork
- "Developers believed AI saved 20%. It cost 19%."
  - Inter, 12px, bold, `#EF4444` at 0.8
  - Fades in below first annotation

#### Growth Arrow
- Curved arrow from lower fork arcing upward to upper fork
  - Color: `#94A3B8` at 0.3, dashed, arrow head
  - Label: "Every patch adds code." — Inter, 12px, `#94A3B8` at 0.5

### Animation Sequence
1. **Frame 0-60 (0-2s):** Chart visible. Original amber line present up to 2020.
2. **Frame 60-180 (2-6s):** At 2020, the line FORKS. Lower path draws down green. Upper path draws flat red. Fork annotation appears.
3. **Frame 180-300 (6-10s):** Lines continue drawing. Small codebase plunges. Large codebase stays flat.
4. **Frame 300-420 (10-14s):** METR annotation appears pointing to upper fork.
5. **Frame 420-480 (14-16s):** "Developers believed AI saved 20%..." second annotation fades in.
6. **Frame 480-600 (16-20s):** Growth arrow curves from lower fork toward upper fork. "Every patch adds code."
7. **Frame 600-660 (20-22s):** Hold. The inevitability is visible.

### Typography
- Fork labels: Inter, 13px, respective colors
- Fork annotation: Inter, 14px, `#E2E8F0` at 0.6
- METR annotation: Inter, 12px, `#EF4444`
- Belief annotation: Inter, 12px, bold, `#EF4444`
- Growth arrow label: Inter, 12px, `#94A3B8` at 0.5

### Easing
- Fork draw: `easeOut(cubic)` over 120 frames, diverging paths
- Annotation appear: `easeOut(quad)` over 20 frames
- Arrow draw: `easeInOut(cubic)` over 60 frames with curve
- Belief annotation: `easeOut(quad)` over 30 frames — slightly slower for emphasis

## Narration Sync
> "A tower? And that's the thing nobody wants to hear..."
> "The degeneration doesn't have this problem. A regenerated module is always small. Context window is always clean..."
> "It's just there's something else. Agentic patching — what Cursor, Copilot, all the tools do — stuffs the context window with code..."

Segments: `part1_economics_026`, `part1_economics_027`, `part1_economics_028`

- **321.30s** ("A tower?"): Chart returns, fork begins
- **331.98s** ("The degeneration doesn't have this problem"): Lower fork plunging, blue line emphasized
- **361.46s** ("Agentic patching"): Upper fork flat, METR annotation visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={660}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Base chart with axes and existing lines */}
    <CodeCostChart showUntil={2020} />

    {/* Fork point */}
    <Sequence from={60}>
      <GlowDot x={2020} y={2.5} radius={6} color="#D9944A" />
    </Sequence>

    {/* Lower fork — Small codebase */}
    <Sequence from={60}>
      <AnimatedLine
        data={[[2020, 2.5], [2022, 1.2], [2024, 0.4], [2025, 0.2]]}
        color="#22C55E" strokeWidth={3}
        drawDuration={120} label="Small codebase" />
    </Sequence>

    {/* Upper fork — Large codebase */}
    <Sequence from={60}>
      <AnimatedLine
        data={[[2020, 2.5], [2022, 2.8], [2024, 3.0], [2025, 3.2]]}
        color="#EF4444" strokeWidth={3}
        drawDuration={120} label="Large codebase" />
    </Sequence>

    {/* Fork annotation */}
    <Sequence from={120}>
      <FadeIn duration={20}>
        <Text text="Same tools. Different codebase sizes."
          font="Inter" size={14} color="#E2E8F0" opacity={0.6}
          x={960} y={700} align="center" />
      </FadeIn>
    </Sequence>

    {/* METR annotation */}
    <Sequence from={300}>
      <SlideIn from="right" distance={5} duration={20}>
        <Annotation
          mainText="METR, 2025: experienced devs 19% slower on mature repos"
          mainColor="#EF4444" mainSize={12}
          connectTo={{ line: "large_codebase", x: 2024 }}
          position={{ x: 1400, y: 280 }} />
      </SlideIn>
    </Sequence>

    {/* Belief annotation */}
    <Sequence from={420}>
      <FadeIn duration={30}>
        <Text text="Developers believed AI saved 20%. It cost 19%."
          font="Inter" size={12} weight={700} color="#EF4444" opacity={0.8}
          x={1400} y={320} align="center" />
      </FadeIn>
    </Sequence>

    {/* Growth arrow */}
    <Sequence from={480}>
      <CurvedArrow
        from={{ line: "small_codebase", x: 2024 }}
        to={{ line: "large_codebase", x: 2025 }}
        color="#94A3B8" opacity={0.3} dashed
        drawDuration={60} label="Every patch adds code." />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "forked_line_chart",
  "baseChart": "code_cost_chart",
  "forkPoint": { "year": 2020, "value": 2.5 },
  "forks": [
    {
      "id": "small_codebase",
      "label": "Small codebase",
      "color": "#22C55E",
      "data": [[2020, 2.5], [2022, 1.2], [2024, 0.4], [2025, 0.2]]
    },
    {
      "id": "large_codebase",
      "label": "Large codebase",
      "color": "#EF4444",
      "data": [[2020, 2.5], [2022, 2.8], [2024, 3.0], [2025, 3.2]]
    }
  ],
  "annotations": [
    {
      "text": "METR, 2025: experienced devs 19% slower on mature repos",
      "pointsTo": "large_codebase"
    },
    {
      "text": "Developers believed AI saved 20%. It cost 19%.",
      "emphasis": true
    }
  ],
  "growthArrow": {
    "from": "small_codebase",
    "to": "large_codebase",
    "label": "Every patch adds code."
  },
  "narrationSegments": ["part1_economics_026", "part1_economics_027", "part1_economics_028"]
}
```

---
