[Remotion]

# Section 1.10: Fork by Codebase Size — The Trap

**Tool:** Remotion
**Duration:** ~46s (1380 frames @ 30fps)
**Timestamp:** 4:59 - 5:45

## Visual Description

The view returns to the code cost chart. The immediate patch cost line FORKS into two diverging paths at ~2020, revealing that "AI-assisted patching" is actually two different stories depending on codebase size.

**Lower fork** ("Small codebase"): The line plunges downward — AI patching is genuinely transformative on small codebases where the context window covers everything.

**Upper fork** ("Large codebase"): The line stays flat at ~10-12 developer hours — experienced developers are actually slower with AI tools on mature repos.

Key annotations appear:
- On the upper fork: "METR, 2025: experienced devs 19% slower on mature repos"
- Then a devastating second line: "Developers believed AI saved 20%. It cost 19%."
- An arrow curves from the lower fork upward toward the upper fork, labeled: "Every patch adds code."

This visualizes the trap: patching makes codebases bigger, pushing you from the world where AI helps into the world where it doesn't.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Chart from spec 03 with axes, blue generate line, and debt area visible

### Chart/Visual Elements

#### Forking Lines
- Fork point: 2020 on x-axis
- Lower fork ("Small codebase"): `#5AAA6E`, 3px solid, plunges from 0.48 → 0.10 by 2026
- Upper fork ("Large codebase"): `#EF4444`, 3px solid, stays flat at 0.45-0.48
- Fork labels: Inter 14px, bold (600), respective colors

#### Annotations
1. "METR, 2025: experienced devs 19% slower on mature repos" — Inter 13px, `#EF4444`
2. "Developers believed AI saved 20%. It cost 19%." — Inter 13px, italic, `#EF4444`, fades in after first annotation
3. "Same tools. Different codebase sizes." — Inter 14px, `#94A3B8`, positioned near fork point

#### The Trap Arrow
- Curved arrow from lower fork sweeping upward toward upper fork
- Arrow color: `#F59E0B`, 2px, dashed
- Label on arrow: "Every patch adds code." — Inter 14px, bold (700), `#F59E0B`

### Animation Sequence
1. **Frame 0-90 (0-3s):** Chart returns from 2×2 grid. Solid amber line is visible.
2. **Frame 90-210 (3-7s):** At 2020, the line forks. Lower path drops (green). Upper path stays flat (red). "Same tools. Different codebase sizes." label appears.
3. **Frame 210-420 (7-14s):** Fork diverges. Lower path plunges. Narration covers small codebase success.
4. **Frame 420-600 (14-20s):** Focus on upper fork. "METR, 2025" annotation appears. Then "Developers believed AI saved 20%..." fades in.
5. **Frame 600-900 (20-30s):** Hold on annotations. The 39-point perception gap is devastating.
6. **Frame 900-1050 (30-35s):** Curved arrow draws from lower fork upward. "Every patch adds code." label appears.
7. **Frame 1050-1380 (35-46s):** Hold. The trap is fully visible.

### Typography
- Fork labels: Inter, 14px, bold (600), `#5AAA6E` / `#EF4444`
- Annotations: Inter, 13px, regular/italic, `#EF4444`
- Arrow label: Inter, 14px, bold (700), `#F59E0B`
- Context label: Inter, 14px, regular (400), `#94A3B8`

### Easing
- Fork split: `easeOut(cubic)` — paths diverge over 120 frames
- Annotations: `easeOut(quad)` fade-in over 20 frames
- Arrow draw: `easeInOut(cubic)` over 90 frames
- Arrow label: `easeOut(quad)` over 20 frames

## Narration Sync
> "On a small codebase — a few thousand lines — patching with AI is genuinely transformative."
> "But on a large codebase... experienced developers are actually 19% slower with AI tools. And the devastating part: those same developers believed AI was making them 20% faster."
> "And that's the trap: every patch makes the codebase bigger."

Segments: `part1_economics_020`, `part1_economics_021`, `part1_economics_022`

- **299.16s** (seg 020): Fork begins — "On a small codebase"
- **309.32s** (seg 020 ends): Lower fork visible
- **309.52s** (seg 021): Upper fork and annotations — "But on a large codebase"
- **345.06s** (seg 021 ends): METR annotations fully visible
- **345.34s** (seg 022): Arrow draws — "And that's the trap"
- **356.64s** (seg 022 ends): Trap arrow complete

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1380}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Base chart with axes and generate line */}
    <CodeCostChartBase />

    {/* Forking patch line */}
    <Sequence from={90}>
      <ForkingLine
        forkPoint={{ x: 2020, y: 0.48 }}
        lower={{
          data: smallCodebaseData,
          color: "#5AAA6E", label: "Small codebase"
        }}
        upper={{
          data: largeCodebaseData,
          color: "#EF4444", label: "Large codebase"
        }}
        forkDuration={120}
      />
    </Sequence>

    {/* Fork context label */}
    <Sequence from={180}>
      <FadeIn duration={20}>
        <Text text="Same tools. Different codebase sizes."
          color="#94A3B8" size={14} />
      </FadeIn>
    </Sequence>

    {/* METR annotations */}
    <Sequence from={420}>
      <AnnotationCallout
        text="METR, 2025: experienced devs 19% slower on mature repos"
        color="#EF4444" size={13}
        targetLine="large_codebase" targetX={2025}
      />
    </Sequence>

    <Sequence from={540}>
      <FadeIn duration={20}>
        <Text text="Developers believed AI saved 20%. It cost 19%."
          color="#EF4444" size={13} style="italic" />
      </FadeIn>
    </Sequence>

    {/* Trap arrow */}
    <Sequence from={900}>
      <CurvedArrow
        from="small_codebase_end" to="large_codebase_mid"
        color="#F59E0B" strokeWidth={2}
        dashArray="6 4" drawDuration={90}
        label="Every patch adds code."
        labelColor="#F59E0B" labelSize={14}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "forking_line_chart",
  "chartRef": "code_cost_generate_vs_patch",
  "forkPoint": { "x": 2020, "y": 0.48 },
  "forks": [
    {
      "id": "small_codebase",
      "label": "Small codebase",
      "color": "#5AAA6E",
      "data": [
        { "x": 2020, "y": 0.48 }, { "x": 2022, "y": 0.30 },
        { "x": 2024, "y": 0.18 }, { "x": 2026, "y": 0.10 }
      ]
    },
    {
      "id": "large_codebase",
      "label": "Large codebase",
      "color": "#EF4444",
      "data": [
        { "x": 2020, "y": 0.48 }, { "x": 2022, "y": 0.47 },
        { "x": 2024, "y": 0.46 }, { "x": 2026, "y": 0.45 }
      ]
    }
  ],
  "annotations": [
    { "text": "METR, 2025: experienced devs 19% slower on mature repos", "target": "large_codebase" },
    { "text": "Developers believed AI saved 20%. It cost 19%.", "target": "large_codebase", "style": "italic" },
    { "text": "Every patch adds code.", "type": "arrow", "from": "small_codebase", "to": "large_codebase" }
  ],
  "narrationSegments": ["part1_economics_020", "part1_economics_021", "part1_economics_022"]
}
```

---
