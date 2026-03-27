[Remotion]

# Section 3.2: Mold Cross-Section — Three Regions

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 0:44 - 0:58

## Visual Description

A technical cross-section diagram of an injection mold appears on screen. The mold is rendered in a clean, blueprint-style aesthetic — precise lines, engineering feel. The mold has three distinct regions that highlight one by one:

1. **Walls** (left and right sides) — glow blue, labeled "TESTS"
2. **Nozzle** (top entry point) — glow amber, labeled "PROMPT"
3. **Cavity** (interior space) — glow teal, labeled "GROUNDING"

Each region illuminates in sequence with a brief pulse, establishing the three-part framework before the narration dives into each component. The mold is centered on screen with generous padding, allowing labels to appear alongside each region.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.08

### Chart/Visual Elements

#### Mold Outline
- Outer shell: `#334155` stroke, 3px, rounded corners (8px radius)
- Dimensions: ~600px wide × 400px tall, centered at (960, 540)
- Inner cavity: 400px × 280px, offset slightly downward

#### Region 1: Walls (Tests)
- Left and right interior walls of the mold
- Highlight color: `#4A90D9` (blue)
- Glow: `#4A90D9` at 0.3, 12px blur radius
- Label: "TESTS" — Inter, 18px, bold (700), `#4A90D9`, positioned outside the mold walls

#### Region 2: Nozzle (Prompt)
- Top injection point — funnel shape pointing into cavity
- Highlight color: `#D9944A` (amber)
- Glow: `#D9944A` at 0.3, 12px blur radius
- Label: "PROMPT" — Inter, 18px, bold (700), `#D9944A`, positioned above nozzle

#### Region 3: Cavity (Grounding)
- Interior space of the mold
- Highlight color: `#4AD9A0` (teal)
- Glow: `#4AD9A0` at 0.2, 8px blur radius
- Label: "GROUNDING" — Inter, 18px, bold (700), `#4AD9A0`, positioned below cavity

### Animation Sequence
1. **Frame 0-30 (0-1s):** Mold outline draws in with stroke-dashoffset animation. Blueprint grid already visible.
2. **Frame 30-60 (1-2s):** Hold on empty mold. Clean engineering aesthetic.
3. **Frame 60-120 (2-4s):** Region 1 (Walls) illuminates. Blue glow spreads along left and right walls. "TESTS" label fades in with connector line.
4. **Frame 120-150 (4-5s):** Hold on walls glowing.
5. **Frame 150-210 (5-7s):** Region 2 (Nozzle) illuminates. Amber glow on top entry point. "PROMPT" label fades in with connector line.
6. **Frame 210-240 (7-8s):** Hold on walls + nozzle glowing.
7. **Frame 240-300 (8-10s):** Region 3 (Cavity) illuminates. Teal glow fills interior space. "GROUNDING" label fades in with connector line.
8. **Frame 300-360 (10-12s):** All three regions glowing simultaneously. The mold is fully lit — the three-part framework is established.
9. **Frame 360-420 (12-14s):** Hold on complete diagram. Subtle pulse on all three regions (sine wave on glow intensity).

### Typography
- Region labels: Inter, 18px, bold (700), color matches region
- Connector lines: 1px, matching region color at 0.4

### Easing
- Mold outline draw: `easeInOut(cubic)` over 30 frames
- Region glow: `easeOut(quad)` over 30 frames each
- Label fade-in: `easeOut(quad)` over 15 frames
- Pulse: `easeInOut(sine)` on 45-frame cycle

## Narration Sync
> "Now let's get precise. Because 'prompt is the mold' is a nice metaphor, but it's incomplete. In PDD, the mold has three components. Three types of capital you're accumulating."

Segment: `part3_mold_parts_005`

- **43.92s** (seg 005): Mold outline begins drawing as "Now let's get precise" starts
- **50.0s**: First region (Walls) illuminates on "three components"
- **54.0s**: Second region (Nozzle) illuminates
- **56.0s**: Third region (Cavity) illuminates on "Three types of capital"
- **58.02s** (seg 005 ends): All three regions glowing

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.08} />

    {/* Mold outline */}
    <Sequence from={0}>
      <StrokeDraw duration={30}>
        <MoldCrossSection
          outerWidth={600} outerHeight={400}
          innerWidth={400} innerHeight={280}
          strokeColor="#334155" strokeWidth={3}
          center={[960, 540]}
        />
      </StrokeDraw>
    </Sequence>

    {/* Region 1: Walls (Tests) */}
    <Sequence from={60}>
      <GlowRegion
        region="walls"
        color="#4A90D9" glowRadius={12} glowOpacity={0.3}
        fadeDuration={30}
      />
      <Sequence from={15}>
        <FadeIn duration={15}>
          <ConnectorLabel text="TESTS" color="#4A90D9"
            font="Inter" size={18} weight={700}
            position="left" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Region 2: Nozzle (Prompt) */}
    <Sequence from={150}>
      <GlowRegion
        region="nozzle"
        color="#D9944A" glowRadius={12} glowOpacity={0.3}
        fadeDuration={30}
      />
      <Sequence from={15}>
        <FadeIn duration={15}>
          <ConnectorLabel text="PROMPT" color="#D9944A"
            font="Inter" size={18} weight={700}
            position="top" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Region 3: Cavity (Grounding) */}
    <Sequence from={240}>
      <GlowRegion
        region="cavity"
        color="#4AD9A0" glowRadius={8} glowOpacity={0.2}
        fadeDuration={30}
      />
      <Sequence from={15}>
        <FadeIn duration={15}>
          <ConnectorLabel text="GROUNDING" color="#4AD9A0"
            font="Inter" size={18} weight={700}
            position="bottom" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Pulse all regions */}
    <Sequence from={300}>
      <PulseGlow regions={["walls", "nozzle", "cavity"]}
        cycleFrames={45} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "mold_diagram",
  "regions": [
    { "id": "walls", "label": "TESTS", "color": "#4A90D9", "highlightFrame": 60 },
    { "id": "nozzle", "label": "PROMPT", "color": "#D9944A", "highlightFrame": 150 },
    { "id": "cavity", "label": "GROUNDING", "color": "#4AD9A0", "highlightFrame": 240 }
  ],
  "narrationSegments": ["part3_mold_parts_005"],
  "durationSeconds": 14.0
}
```

---
