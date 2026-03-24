[Remotion]

# Section 1.8: Fork by Codebase Size — The Trap Revealed

**Tool:** Remotion
**Duration:** ~40s (1200 frames @ 30fps)
**Timestamp:** 3:48 - 4:28

## Visual Description

Returning to the code cost chart, the amber "immediate patch cost" line FORKS into two divergent paths at 2020. The lower path — labeled "Small codebase" — plunges downward, showing genuine transformation. The upper path — labeled "Large codebase" — stays flat at ~10-12 developer hours, showing no improvement.

Annotations appear: "METR, 2025: experienced devs 19% slower on mature repos" on the flat upper line. Then a devastating second annotation: "Developers believed AI saved 20%. It cost 19%." — the 39-point perception gap.

Finally, an arrow curves from the small-codebase fork upward toward the large-codebase fork with the label "Every patch adds code." — showing that patching itself pushes you from the world where AI helps into the world where it doesn't.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Inherits chart framework from 03_code_cost_chart

### Chart/Visual Elements

#### Inherited Chart (dimmed)
- Blue generate line: visible at 0.2 opacity
- Amber dashed total cost line: visible at 0.2 opacity
- Debt shading: visible at 0.03 opacity

#### Forking Amber Line — at year 2020
- Fork point: small circle 6px, `#D9944A` at 0.6, at (2020, ~35%)

#### Lower Fork — Small Codebase
- Color: `#4ADE80`, 2.5px solid stroke
- Path: plunges from (2020, 35%) to (2025, 10%)
- Glow: 6px Gaussian blur, `#4ADE80` at 0.1
- Label: "Small codebase" — Inter, 12px, semi-bold, `#4ADE80` at 0.7
- Small annotation: "A few thousand lines — context covers everything" — Inter, 9px, `#4ADE80` at 0.4

#### Upper Fork — Large Codebase
- Color: `#EF4444`, 2.5px solid stroke
- Path: stays flat from (2020, 35%) to (2025, 32%) — barely moves
- Glow: 6px Gaussian blur, `#EF4444` at 0.1
- Label: "Large codebase" — Inter, 12px, semi-bold, `#EF4444` at 0.7

#### METR Annotation
- Position: above the flat upper fork line
- "METR, 2025: experienced devs 19% slower on mature repos" — Inter, 12px, `#EF4444` at 0.6
- Callout line: 1px, `#EF4444` at 0.2

#### Perception Gap Annotation
- Position: below METR annotation
- "Developers believed AI saved 20%. It cost 19%." — Inter, 14px, bold (700), `#EF4444` at 0.8
- Subtle red glow behind text: `#EF4444` at 0.04

#### Trap Arrow
- Curved arrow from lower fork bending upward toward upper fork
- Color: `#D9944A` at 0.5, 2px, with arrowhead
- Label: "Every patch adds code." — Inter, 13px, semi-bold (600), `#D9944A` at 0.7
- The arrow follows a quadratic bezier curve

### Animation Sequence
1. **Frame 0-60 (0-2s):** Chart visible with dimmed elements. Amber solid line is the focus.
2. **Frame 60-120 (2-4s):** Fork point circle appears at 2020. The line splits — lower fork draws downward (green), upper fork extends flat (red).
3. **Frame 120-240 (4-8s):** Fork labels appear: "Small codebase" (green) and "Large codebase" (red). Small annotation about context coverage appears under the green fork.
4. **Frame 240-360 (8-12s):** "Same tools. Different codebase sizes." annotation fades in centrally.
5. **Frame 360-480 (12-16s):** METR annotation appears on the flat upper fork: "experienced devs 19% slower."
6. **Frame 480-600 (16-20s):** Perception gap annotation fades in dramatically: "Developers believed AI saved 20%. It cost 19%." Red glow.
7. **Frame 600-780 (20-26s):** Hold on the perception gap. This is the emotional gut-punch moment.
8. **Frame 780-960 (26-32s):** Trap arrow animates — curves from green fork upward toward red fork. "Every patch adds code." label appears along the arrow path.
9. **Frame 960-1200 (32-40s):** Hold on complete visualization. The trap is visible.

### Typography
- Fork labels: Inter, 12px, semi-bold, respective colors at 0.7
- METR annotation: Inter, 12px, `#EF4444` at 0.6
- Perception gap: Inter, 14px, bold (700), `#EF4444` at 0.8
- Trap label: Inter, 13px, semi-bold (600), `#D9944A` at 0.7
- Fine print: Inter, 9px, `#4ADE80` at 0.4

### Easing
- Fork line draw: `easeInOut(quad)` over 60 frames
- Fork point appear: `easeOut(back)` over 15 frames
- Label fade: `easeOut(quad)` over 20 frames
- Perception gap fade: `easeOut(quad)` over 30 frames (slower for emphasis)
- Arrow draw: `easeInOut(cubic)` over 60 frames
- Red glow pulse: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "On a small codebase—a few thousand lines—patching with AI is genuinely transformative."
> "But on a large codebase—the kind you end up with after years of patching—experienced developers are actually nineteen percent slower with AI tools."
> "And that's the trap: every patch makes the codebase bigger. So patching pushes you from the world where AI helps into the world where it doesn't."

Segments: `part1_economics_024`, `part1_economics_025`, `part1_economics_026`

- **3:48** ("Small codebase"): Fork draws, green path plunges
- **4:09** ("large codebase"): Upper fork stays flat, METR annotation
- **4:17** ("believed AI saved 20%"): Perception gap annotation
- **4:22** ("that's the trap"): Arrow curves upward, "Every patch adds code."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1200}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Dimmed chart background */}
    <Opacity value={0.2}>
      <CodeCostChart />
    </Opacity>

    {/* Fork point */}
    <Sequence from={60}>
      <ForkPoint cx={forkX} cy={forkY} r={6}
        color="#D9944A" opacity={0.6} />
    </Sequence>

    {/* Green lower fork */}
    <Sequence from={60}>
      <AnimatedLine data={smallCodebaseFork} color="#4ADE80"
        width={2.5} glow={{ blur: 6, opacity: 0.1 }}
        drawDuration={60} />
      <Sequence from={60}>
        <FadeIn duration={20}>
          <LineLabel text="Small codebase" color="#4ADE80"
            opacity={0.7} font="Inter" size={12} weight={600} />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Red upper fork */}
    <Sequence from={60}>
      <AnimatedLine data={largeCodebaseFork} color="#EF4444"
        width={2.5} glow={{ blur: 6, opacity: 0.1 }}
        drawDuration={60} />
      <Sequence from={60}>
        <FadeIn duration={20}>
          <LineLabel text="Large codebase" color="#EF4444"
            opacity={0.7} font="Inter" size={12} weight={600} />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* METR annotation */}
    <Sequence from={360}>
      <AnnotationCard
        header="METR, 2025: experienced devs 19% slower"
        headerColor="#EF4444"
        calloutTo={largeCodebaseLine2024}
        calloutColor="#EF4444" />
    </Sequence>

    {/* Perception gap */}
    <Sequence from={480}>
      <FadeIn duration={30}>
        <GlowText
          text="Developers believed AI saved 20%. It cost 19%."
          font="Inter" size={14} weight={700}
          color="#EF4444" opacity={0.8}
          glowColor="#EF4444" glowOpacity={0.04}
          x={960} y={250} align="center" />
      </FadeIn>
    </Sequence>

    {/* Trap arrow */}
    <Sequence from={780}>
      <CurvedArrow
        from={smallForkEnd} to={largeForkMid}
        color="#D9944A" opacity={0.5} width={2}
        drawDuration={60}>
        <PathLabel text="Every patch adds code."
          font="Inter" size={13} weight={600}
          color="#D9944A" opacity={0.7} />
      </CurvedArrow>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "forking_chart",
  "chartId": "codebase_size_fork",
  "forkYear": 2020,
  "forks": [
    {
      "id": "small_codebase",
      "label": "Small codebase",
      "color": "#4ADE80",
      "dataPoints": [
        { "x": 2020, "y": 35 }, { "x": 2021, "y": 28 },
        { "x": 2022, "y": 22 }, { "x": 2023, "y": 15 },
        { "x": 2024, "y": 12 }, { "x": 2025, "y": 10 }
      ]
    },
    {
      "id": "large_codebase",
      "label": "Large codebase",
      "color": "#EF4444",
      "dataPoints": [
        { "x": 2020, "y": 35 }, { "x": 2021, "y": 35 },
        { "x": 2022, "y": 34 }, { "x": 2023, "y": 34 },
        { "x": 2024, "y": 33 }, { "x": 2025, "y": 32 }
      ]
    }
  ],
  "annotations": [
    { "text": "METR, 2025: experienced devs 19% slower on mature repos", "color": "#EF4444" },
    { "text": "Developers believed AI saved 20%. It cost 19%.", "color": "#EF4444", "emphasis": true }
  ],
  "trapArrow": { "label": "Every patch adds code.", "color": "#D9944A" },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part1_economics_024", "part1_economics_025", "part1_economics_026"]
}
```

---
