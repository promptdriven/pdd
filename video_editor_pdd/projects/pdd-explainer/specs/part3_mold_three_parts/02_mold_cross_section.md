[Remotion]

# Section 3.2: Mold Cross-Section — Three Regions Illuminate

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 13:04 - 13:14

## Visual Description

A technical cross-section diagram of an injection mold fills the center of the screen. The mold is rendered in a clean engineering-schematic style — precise lines, hard edges, subtle ambient glow. It has three clearly distinct regions: the **walls** (outer boundary constraining the cavity), the **injection nozzle** (top-center entry point where material is introduced), and the **cavity interior** (the space that will hold the material/grounding).

Each region highlights one by one as the narrator introduces the three types of capital. First the walls illuminate in amber, with small label tags appearing along the wall segments: "null → None", "empty string → ''", "handles unicode", "latency < 100ms". Then the nozzle illuminates in blue, with labels: "intent", "requirements", "constraints". Finally the cavity interior fills with a soft green wash representing material/grounding, with labels: "style", "patterns", "conventions".

The mold is viewed from a slightly angled cross-section perspective, giving depth without full 3D. Subtle engineering dimension lines and callout arrows connect each region to its label panel.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: engineering grid, 40px spacing, `#1E293B` at 0.04

### Chart/Visual Elements

#### Mold Cross-Section (centered at 960, 500)
- Overall dimensions: 600w × 700h
- **Outer shell:** `#334155` at 0.6, 3px stroke, rounded industrial corners
- **Cavity interior:** `#1E293B` at 0.2, 450w × 550h
- **Injection nozzle:** tapered funnel at top-center, 80w tapering to 30w, 120h, `#334155` at 0.6

#### Region 1 — Walls (amber)
- Wall segments: inner surfaces of the cavity, `#D9944A` at 0.5, 4px stroke
- Glow: 12px Gaussian blur, `#D9944A` at 0.15
- Labels along walls (JetBrains Mono, 9px, `#D9944A` at 0.7):
  - "null → None" (left wall, y: 350)
  - "empty string → ''" (left wall, y: 450)
  - "handles unicode" (bottom wall, y: 750)
  - "latency < 100ms" (right wall, y: 400)
- Callout arrows: 1px, `#D9944A` at 0.3

#### Region 2 — Nozzle/Specification (blue)
- Nozzle shape: `#4A90D9` at 0.5, 3px stroke
- Glow: 12px Gaussian blur, `#4A90D9` at 0.15
- Labels above nozzle (Inter, 11px, `#4A90D9` at 0.7):
  - "intent" (left of nozzle)
  - "requirements" (center above nozzle)
  - "constraints" (right of nozzle)

#### Region 3 — Cavity/Grounding (green)
- Cavity fill: gradient wash `#5AAA6E` at 0.08 → 0.15, bottom-up
- Organic texture: subtle Perlin noise displacement, `#5AAA6E` at 0.06
- Labels inside cavity (Inter, 11px, `#5AAA6E` at 0.6):
  - "style" (upper-left interior)
  - "patterns" (center interior)
  - "conventions" (lower-right interior)

#### Section Label
- "THREE TYPES OF CAPITAL" — Inter, 12px, semi-bold (600), `#94A3B8` at 0.4, letter-spacing 3px, centered at y: 120

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Mold cross-section draws itself — outer shell first (stroke-dashoffset), then cavity outline, then nozzle. All in neutral gray.
2. **Frame 40-60 (1.33-2s):** "THREE TYPES OF CAPITAL" label fades in at top.
3. **Frame 60-120 (2-4s):** Region 1 activates — walls illuminate amber. Glow pulses on. Wall labels appear one by one with callout arrows drawing.
4. **Frame 120-180 (4-6s):** Region 2 activates — nozzle illuminates blue. Labels appear above nozzle. Walls remain lit but dim to 0.3.
5. **Frame 180-240 (6-8s):** Region 3 activates — cavity fills with green wash, bottom-up. Labels appear inside. Nozzle dims to 0.3.
6. **Frame 240-300 (8-10s):** All three regions re-illuminate to full brightness simultaneously. Hold on the complete diagram. The three colors create a harmonious technical schematic.

### Typography
- Section label: Inter, 12px, semi-bold (600), `#94A3B8` at 0.4, letter-spacing 3px
- Wall labels: JetBrains Mono, 9px, `#D9944A` at 0.7
- Nozzle labels: Inter, 11px, `#4A90D9` at 0.7
- Grounding labels: Inter, 11px, `#5AAA6E` at 0.6

### Easing
- Mold draw: `easeInOut(cubic)` over 40 frames
- Region illuminate: `easeOut(quad)` over 20 frames
- Label appear: `easeOut(quad)` over 15 frames
- Callout arrow draw: `easeOut(cubic)` over 12 frames
- Green fill rise: `easeOut(cubic)` over 40 frames
- Region dim: `easeOut(quad)` over 15 frames to 0.3

## Narration Sync
> "In PDD, the mold has three components. Three types of capital you're accumulating."
> "First: tests. Tests are the walls of your mold."

Segment: `part3_002`

- **13:04** ("In PDD, the mold has three components"): Mold cross-section draws
- **13:07** ("Three types of capital"): Section label appears
- **13:09** ("First: tests"): Walls illuminate amber
- **13:11** ("Tests are the walls"): Wall labels appear with callout arrows

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <EngineeringGrid spacing={40} color="#1E293B" opacity={0.04} />

    {/* Mold cross-section draws in */}
    <StrokeDraw duration={40}>
      <MoldCrossSection center={[960, 500]}
        width={600} height={700}
        shellColor="#334155" shellOpacity={0.6} shellWidth={3}
        cavityColor="#1E293B" cavityOpacity={0.2} />
    </StrokeDraw>

    {/* Section label */}
    <Sequence from={40}>
      <FadeIn duration={20}>
        <Text text="THREE TYPES OF CAPITAL" font="Inter" size={12}
          weight={600} color="#94A3B8" opacity={0.4}
          letterSpacing={3} x={960} y={120} align="center" />
      </FadeIn>
    </Sequence>

    {/* Region 1 — Walls (amber) */}
    <Sequence from={60}>
      <RegionIlluminate region="walls" color="#D9944A"
        opacity={0.5} glowBlur={12} glowOpacity={0.15}
        duration={20}>
        <WallLabels labels={[
          { text: 'null → None', y: 350, side: 'left' },
          { text: "empty string → ''", y: 450, side: 'left' },
          { text: 'handles unicode', y: 750, side: 'bottom' },
          { text: 'latency < 100ms', y: 400, side: 'right' }
        ]} font="JetBrains Mono" size={9} color="#D9944A"
          opacity={0.7} arrowColor="#D9944A" arrowOpacity={0.3}
          stagger={15} />
      </RegionIlluminate>
    </Sequence>

    {/* Region 2 — Nozzle (blue) */}
    <Sequence from={120}>
      <RegionIlluminate region="nozzle" color="#4A90D9"
        opacity={0.5} glowBlur={12} glowOpacity={0.15}
        duration={20} dimOthers={0.3}>
        <NozzleLabels labels={['intent', 'requirements', 'constraints']}
          font="Inter" size={11} color="#4A90D9" opacity={0.7}
          stagger={12} />
      </RegionIlluminate>
    </Sequence>

    {/* Region 3 — Cavity/Grounding (green) */}
    <Sequence from={180}>
      <CavityFill color="#5AAA6E" fromOpacity={0.08} toOpacity={0.15}
        direction="bottom-up" duration={40} noise>
        <CavityLabels labels={[
          { text: 'style', position: 'upper-left' },
          { text: 'patterns', position: 'center' },
          { text: 'conventions', position: 'lower-right' }
        ]} font="Inter" size={11} color="#5AAA6E" opacity={0.6}
          stagger={12} />
      </CavityFill>
    </Sequence>

    {/* All three re-illuminate */}
    <Sequence from={240}>
      <AllRegionsFullBrightness duration={20} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "technical_diagram",
  "diagramId": "mold_cross_section",
  "regions": [
    {
      "id": "walls",
      "label": "Test Capital",
      "color": "#D9944A",
      "labels": ["null → None", "empty string → ''", "handles unicode", "latency < 100ms"]
    },
    {
      "id": "nozzle",
      "label": "Prompt Capital",
      "color": "#4A90D9",
      "labels": ["intent", "requirements", "constraints"]
    },
    {
      "id": "cavity",
      "label": "Grounding Capital",
      "color": "#5AAA6E",
      "labels": ["style", "patterns", "conventions"]
    }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_002"]
}
```

---
