[Remotion]

# Section 3.4: Research Annotations — AI Code Quality Data

**Tool:** Remotion
**Duration:** ~15s (450 frames @ 30fps)
**Timestamp:** 13:26 - 13:41

## Visual Description

Building on the mold wall visualization, research citation annotations materialize one by one overlaid on the still-visible mold diagram. The mold walls remain glowing amber in the background, and each data point reinforces why the walls are essential.

First annotation: a data card appears upper-left, styled as a research paper citation. "AI code: 1.7× more issues" in bold red, with source "(CodeRabbit, 2025)" below. Sub-stats appear beneath: "75% more logic errors" and "8× more performance problems" — each on its own line, staggered. The mold walls pulse brighter as each stat lands.

Second annotation: a contrasting data card appears upper-right. "AI + strong tests = amplified delivery" in bold green, source "(DORA, 2025)". An arrow connects this card to the mold walls, implying: the walls solve the problem the first card identified.

Between the two cards, a visual equation emerges: [AI code] + [No tests] = [1.7× issues] vs. [AI code] + [Strong tests] = [Amplified delivery]. The left side glows red, the right side glows green. The mold walls are the differentiator.

The background mold diagram dims slightly to serve as context, with the annotations layered on top as the primary visual focus.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Mold diagram: carried forward at 0.2 opacity (dimmed)

### Chart/Visual Elements

#### Annotation Card 1 — CodeRabbit (position: upper-left, 200, 200)
- Card: 400×220px, `#1E293B` at 0.85, 1px `#EF4444` border at 0.3, rounded 8px
- Header: "AI CODE QUALITY" — Inter, 10px, semi-bold (600), `#64748B` at 0.5, letter-spacing 2px
- Main stat: "1.7× more issues" — Inter, 28px, bold (700), `#EF4444`
- Sub-stats (staggered, Inter, 14px, `#EF4444` at 0.7):
  - "75% more logic errors"
  - "8× more performance problems"
- Source: "(CodeRabbit, 2025)" — Inter, 11px, `#64748B` at 0.5

#### Annotation Card 2 — DORA (position: upper-right, 1320, 200)
- Card: 400×180px, `#1E293B` at 0.85, 1px `#5AAA6E` border at 0.3, rounded 8px
- Header: "WITH STRONG TESTS" — Inter, 10px, semi-bold (600), `#64748B` at 0.5, letter-spacing 2px
- Main stat: "Amplified delivery" — Inter, 28px, bold (700), `#5AAA6E`
- Sub-stat: "AI + strong tests = accelerated" — Inter, 14px, `#5AAA6E` at 0.7
- Source: "(DORA, 2025)" — Inter, 11px, `#64748B` at 0.5

#### Connecting Arrow
- From DORA card bottom-center to mold wall region
- Dashed line, 2px, `#5AAA6E` at 0.3, arrowhead at mold
- Label on arrow: "Tests are the walls" — Inter, 10px, `#D9944A` at 0.5

#### Visual Equation (centered at y: 850)
- LEFT: "[AI code] + [No tests] = 1.7× issues" — Inter, 14px, `#EF4444` at 0.6
- Divider: "vs." — Inter, 14px, `#64748B` at 0.3
- RIGHT: "[AI code] + [Strong tests] = Amplified delivery" — Inter, 14px, `#5AAA6E` at 0.6
- Differentiator bracket pointing to mold walls: "The walls" — Inter, 12px, `#D9944A` at 0.5

### Animation Sequence
1. **Frame 0-30 (0-1s):** Mold diagram dims to 0.2. Space clears for annotations.
2. **Frame 30-120 (1-4s):** Card 1 materializes — border draws, background fades in, header types, "1.7× more issues" scales up from 0.8 with spring. Sub-stats stagger in (15 frames apart). Mold walls pulse amber on each sub-stat.
3. **Frame 120-210 (4-7s):** Card 2 materializes — same sequence but green border. "Amplified delivery" scales up. Connecting arrow draws from card to mold walls.
4. **Frame 210-330 (7-11s):** Visual equation appears at bottom. LEFT side fades in (red). "vs." appears. RIGHT side fades in (green). Bracket draws pointing to walls.
5. **Frame 330-390 (11-13s):** Mold walls pulse brighter — amber glow intensifies. The walls are the differentiator.
6. **Frame 390-450 (13-15s):** Hold on complete picture. All annotations visible, mold walls glowing.

### Typography
- Card headers: Inter, 10px, semi-bold (600), `#64748B` at 0.5, letter-spacing 2px
- Main stats: Inter, 28px, bold (700), respective colors
- Sub-stats: Inter, 14px, respective colors at 0.7
- Sources: Inter, 11px, `#64748B` at 0.5
- Equation text: Inter, 14px, respective colors at 0.6

### Easing
- Card border draw: `easeOut(cubic)` over 20 frames
- Card background: `easeOut(quad)` over 15 frames
- Main stat scale: `spring({ stiffness: 200, damping: 12 })` from 0.8
- Sub-stat stagger: `easeOut(quad)` over 12 frames, 15-frame delay each
- Wall pulse: `easeInOut(sine)` on 20-frame cycle, opacity 0.3 → 0.7
- Arrow draw: `easeOut(cubic)` over 25 frames
- Equation fade: `easeOut(quad)` over 20 frames

## Narration Sync
> "CodeRabbit analyzed hundreds of pull requests and found AI-generated code produces one-point-seven times more issues than human code — seventy-five percent more logic errors, eight times more performance problems."
> "The 2025 DORA report confirmed it: AI without strong tests increases instability. AI with strong tests amplifies delivery."

Segment: `part3_004`

- **13:26** ("CodeRabbit analyzed hundreds of pull requests"): Card 1 materializes
- **13:30** ("one-point-seven times more issues"): Main stat appears, wall pulse
- **13:33** ("seventy-five percent more logic errors"): Sub-stats stagger in
- **13:36** ("The 2025 DORA report confirmed it"): Card 2 materializes
- **13:39** ("AI with strong tests amplifies delivery"): Green stat, connecting arrow draws

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={450}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Dimmed mold background */}
    <MoldCrossSection center={[960, 500]} opacity={0.2}
      wallColor="#D9944A" wallPulse={{
        trigger: [30, 90, 105, 210],
        duration: 20, fromOpacity: 0.3, toOpacity: 0.7
      }} />

    {/* Card 1 — CodeRabbit */}
    <Sequence from={30}>
      <DataCard position={[200, 200]} size={[400, 220]}
        bgColor="#1E293B" borderColor="#EF4444"
        borderOpacity={0.3} rounded={8}>
        <CardHeader text="AI CODE QUALITY" />
        <SpringScale from={0.8} stiffness={200} damping={12}>
          <StatText text="1.7× more issues" color="#EF4444"
            font="Inter" size={28} weight={700} />
        </SpringScale>
        <Stagger delay={15}>
          <SubStat text="75% more logic errors" color="#EF4444" />
          <SubStat text="8× more performance problems" color="#EF4444" />
        </Stagger>
        <Source text="(CodeRabbit, 2025)" />
      </DataCard>
    </Sequence>

    {/* Card 2 — DORA */}
    <Sequence from={120}>
      <DataCard position={[1320, 200]} size={[400, 180]}
        bgColor="#1E293B" borderColor="#5AAA6E"
        borderOpacity={0.3} rounded={8}>
        <CardHeader text="WITH STRONG TESTS" />
        <SpringScale from={0.8} stiffness={200} damping={12}>
          <StatText text="Amplified delivery" color="#5AAA6E"
            font="Inter" size={28} weight={700} />
        </SpringScale>
        <SubStat text="AI + strong tests = accelerated" color="#5AAA6E" />
        <Source text="(DORA, 2025)" />
      </DataCard>
    </Sequence>

    {/* Connecting arrow */}
    <Sequence from={180}>
      <DashedArrow from={[1520, 380]} to={[1100, 500]}
        color="#5AAA6E" opacity={0.3} dashLength={6}
        drawDuration={25}>
        <ArrowLabel text="Tests are the walls" color="#D9944A"
          opacity={0.5} font="Inter" size={10} />
      </DashedArrow>
    </Sequence>

    {/* Visual equation */}
    <Sequence from={210}>
      <VisualEquation y={850}
        left={{ text: '[AI code] + [No tests] = 1.7× issues', color: '#EF4444' }}
        divider="vs."
        right={{ text: '[AI code] + [Strong tests] = Amplified delivery', color: '#5AAA6E' }}
        differentiator={{ text: 'The walls', color: '#D9944A', target: 'mold_walls' }}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "research_annotations",
  "annotations": [
    {
      "id": "coderabbit_2025",
      "mainText": "1.7× more issues",
      "color": "#EF4444",
      "subStats": ["75% more logic errors", "8× more performance problems"],
      "source": "CodeRabbit, 2025",
      "finding": "AI-generated code quality deficit"
    },
    {
      "id": "dora_2025",
      "mainText": "Amplified delivery",
      "color": "#5AAA6E",
      "subStats": ["AI + strong tests = accelerated"],
      "source": "DORA, 2025",
      "finding": "Tests transform AI from liability to accelerant"
    }
  ],
  "equation": {
    "left": "AI code + No tests = 1.7× issues",
    "right": "AI code + Strong tests = Amplified delivery",
    "differentiator": "The walls"
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_004"]
}
```

---
