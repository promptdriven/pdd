# Section 3.1: Cross-Section Introduction

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 8:45 - 9:00

## Visual Description

A technical cross-section view of an injection mold appears. Three distinct regions highlight one by one, introducing the "three parts" concept. This establishes the visual framework for the entire Part 3 section.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Full screen, centered composition

### Animation Elements

1. **Mold Cross-Section**
   - Technical, blueprint-style rendering
   - 3D-ish perspective showing internal structure
   - Steel gray (#8A9BA8) base color
   - Subtle grid lines for technical feel

2. **Three Regions**
   - **Walls (Amber):** Outer boundary structures
   - **Nozzle/Input (Blue):** Top injection point
   - **Interior/Material Zone (Green):** Central cavity area

3. **Highlight Sequence**
   - Each region pulses with its color when introduced
   - Labels fade in: "Walls", "Nozzle", "Material"
   - Subtle glow effect on active region

### Animation Sequence

1. **Frame 0-90 (0-3s):** Mold fades in
   - Cross-section view establishes
   - Technical rendering style
   - Neutral gray, awaiting highlights

2. **Frame 90-150 (3-5s):** First region highlights
   - Walls illuminate amber (#D9944A)
   - Brief pulse animation
   - "Walls" label fades in

3. **Frame 150-210 (5-7s):** Second region highlights
   - Nozzle/input illuminates blue (#4A90D9)
   - Brief pulse animation
   - "Nozzle" label fades in

4. **Frame 210-270 (7-9s):** Third region highlights
   - Interior illuminates green (#5AAA6E)
   - Brief pulse animation
   - "Material" label fades in

5. **Frame 270-450 (9-15s):** All three visible
   - All regions softly glowing their colors
   - Labels visible
   - Hold for narration completion

### Visual Design: Mold Cross-Section

```
        ┌─────────────────┐
        │    [NOZZLE]     │  ← Blue (#4A90D9)
        │       ↓         │
    ┌───┴─────────────────┴───┐
    │ ╔═══════════════════╗   │
    │ ║                   ║   │
    │ ║    [INTERIOR]     ║   │  ← Green (#5AAA6E)
    │ ║                   ║   │
    │ ╚═══════════════════╝   │
    │         [WALLS]         │  ← Amber (#D9944A)
    └─────────────────────────┘
```

### Code Structure (Remotion)

```typescript
const CrossSectionIntro: React.FC = () => {
  const frame = useCurrentFrame();

  // Timing constants
  const FADE_IN_END = 90;
  const WALLS_START = 90;
  const NOZZLE_START = 150;
  const MATERIAL_START = 210;

  const wallsOpacity = interpolate(
    frame,
    [WALLS_START, WALLS_START + 30],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  const nozzleOpacity = interpolate(
    frame,
    [NOZZLE_START, NOZZLE_START + 30],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  const materialOpacity = interpolate(
    frame,
    [MATERIAL_START, MATERIAL_START + 30],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      <MoldCrossSection />
      <RegionHighlight
        region="walls"
        color="#D9944A"
        opacity={wallsOpacity}
      />
      <RegionHighlight
        region="nozzle"
        color="#4A90D9"
        opacity={nozzleOpacity}
      />
      <RegionHighlight
        region="material"
        color="#5AAA6E"
        opacity={materialOpacity}
      />
      <RegionLabel text="Walls" opacity={wallsOpacity} />
      <RegionLabel text="Nozzle" opacity={nozzleOpacity} />
      <RegionLabel text="Material" opacity={materialOpacity} />
    </AbsoluteFill>
  );
};
```

### Easing

- Mold fade-in: `easeOutCubic`
- Region highlights: `easeOutQuad`
- Label fade-in: `easeOutCubic`
- Pulse animation: `easeInOutSine` (subtle oscillation)

## Narration Sync

> "Now let's get precise. Because 'prompt is the mold' is a nice metaphor, but it's incomplete."
>
> "In PDD, the mold has three components. Three types of capital you're accumulating."

The three regions highlight in sequence as "three components" is spoken.

## Audio Notes

- Subtle mechanical/technical ambient
- Soft "ping" on each region highlight
- Building sense of precision and structure

## Transition

Continues directly into Section 3.2 where the walls illuminate fully and receive their test labels.
