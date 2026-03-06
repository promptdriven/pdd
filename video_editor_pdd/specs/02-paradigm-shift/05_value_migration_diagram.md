[Remotion] Value Migration Diagram — Object-to-Specification Flow

# Section 2.4: Value Migration Diagram — Where the Value Lives

**Tool:** Remotion
**Duration:** ~15s
**Timestamp:** 1:30 - 1:45

## Visual Description
An animated diagram overlay showing the concept of value migration. The layout is a vertical stack: at the bottom, a simplified "physical object" icon (rounded rectangle) labeled "THE PART" in muted gray. At the top, a glowing "specification" icon (document/blueprint shape) labeled "THE MOLD" in vibrant blue. An animated arrow connects them — a stream of small glowing dots flowing upward from object to specification, representing value migration. As the animation progresses, the bottom icon dims and shrinks while the top icon brightens and grows. A horizontal value bar on the right side shows a slider moving from bottom (object) to top (specification), with percentage labels: "0% → 100% of value."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Diagram region: right-aligned, 600x700px area at (1200, 190) to (1800, 890)
- Backing panel: rounded rect, rgba(15, 23, 42, 0.7), blur(6px), border-radius 12px

### Chart/Visual Elements
- Bottom icon ("THE PART"):
  - Shape: rounded rectangle, 120x80px, centered at (1500, 760)
  - Fill: #475569 → dims to #1E293B over animation
  - Border: 2px solid #64748B → dims to #334155
  - Label: "THE PART" below icon
- Top icon ("THE MOLD"):
  - Shape: document/blueprint icon, 140x100px, centered at (1500, 340)
  - Fill: #1E3A5F → brightens to #3B82F6
  - Border: 2px solid #3B82F6 → brightens with glow
  - Label: "THE MOLD" above icon
  - Glow ring: grows from 0px to 20px spread, #3B82F6 at 40% opacity
- Migration arrow: vertical stream between icons
  - 12-16 small circles (6px), #F59E0B, flowing upward continuously
  - Path: slight sinusoidal wave, amplitude 15px
- Value bar: vertical progress bar, right side at x=1750
  - Track: 8px wide, 400px tall, #1E293B
  - Fill: gradient #475569 → #3B82F6, animates from 20% to 95%
  - Bottom label: "Object" — #64748B
  - Top label: "Specification" — #3B82F6
  - Percentage readout: animates "20%" → "95%"

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Backing panel fades in. Both icons appear at initial state.
2. **Frame 25-50 (0.83-1.67s):** Migration arrow particles begin flowing upward.
3. **Frame 50-80 (1.67-2.67s):** Bottom icon begins dimming/shrinking — scale 1.0→0.7, opacity 1.0→0.4.
4. **Frame 50-80 (1.67-2.67s):** Top icon begins brightening/growing — scale 0.8→1.1, glow appears.
5. **Frame 50-120 (1.67-4s):** Value bar fill animates from 20% to 95%. Percentage readout counts up.
6. **Frame 120-300 (4-10s):** Hold at final state. Particles continue flowing. Top icon glow pulses gently.
7. **Frame 300-360 (10-12s):** "THE MOLD" label transforms to bold with underline emphasis.
8. **Frame 360-450 (12-15s):** Entire diagram fades out — opacity 1→0.

### Typography
- "THE PART" label: Inter SemiBold, 18px, #94A3B8 → dims to #475569
- "THE MOLD" label: Inter Bold, 20px, #3B82F6 → brightens to #60A5FA, gains underline at frame 300
- Value bar labels: Inter Medium, 14px
  - "Object": #64748B
  - "Specification": #3B82F6
- Percentage readout: JetBrains Mono Bold, 28px, #FFFFFF

### Easing
- Icon dim/brighten: `easeInOutCubic`
- Icon scale: `easeInOutQuad`
- Value bar fill: `easeInOutCubic`
- Particle flow: `linear` (continuous)
- Glow pulse: sinusoidal, 3s period
- Fade out: `easeInCubic`

## Narration Sync
> "Value migrates from the object to the specification. The plastic part is disposable. The mold is everything."

Particles begin flowing as "value migrates" is spoken. Bottom icon dims on "disposable." Top icon pulses on "everything."

## Code Structure (Remotion)
```typescript
<Sequence from={VALUE_START} durationInFrames={450}>
  <AbsoluteFill>
    {/* Backing panel */}
    <BackingPanel
      bounds={{ x: 1200, y: 190, w: 600, h: 700 }}
      opacity={interpolate(frame, [0, 25, 420, 450], [0, 0.7, 0.7, 0])}
    />

    {/* Bottom icon — THE PART */}
    <ObjectIcon
      position={[1500, 760]}
      scale={interpolate(frame, [50, 80, 420, 450], [1.0, 0.7, 0.7, 0.7])}
      opacity={interpolate(frame, [50, 80, 420, 450], [1.0, 0.4, 0.4, 0])}
      fill={lerpColor(frame, [50, 80], ['#475569', '#1E293B'])}
    />
    <Label text="THE PART" position={[1500, 810]}
      opacity={interpolate(frame, [0, 25, 420, 450], [0, 1, 1, 0])}
      color={lerpColor(frame, [50, 80], ['#94A3B8', '#475569'])}
    />

    {/* Top icon — THE MOLD */}
    <SpecificationIcon
      position={[1500, 340]}
      scale={interpolate(frame, [50, 80], [0.8, 1.1], { extrapolateRight: 'clamp' })}
      fill={lerpColor(frame, [50, 80], ['#1E3A5F', '#3B82F6'])}
      glowRadius={interpolate(frame, [80, 120], [0, 20], { extrapolateRight: 'clamp' })}
      glowOpacity={frame > 120 ? interpolate(Math.sin(frame * 0.07), [-1, 1], [0.2, 0.4]) : 0}
    />
    <Label text="THE MOLD" position={[1500, 280]}
      color="#3B82F6"
      bold={frame > 300}
      underline={frame > 300}
    />

    {/* Migration particle stream */}
    <ParticleStream
      from={[1500, 720]} to={[1500, 390]}
      particleCount={14}
      particleSize={6}
      color="#F59E0B"
      waveAmplitude={15}
      visible={frame > 25}
    />

    {/* Value bar */}
    <VerticalProgressBar
      position={[1750, 360]}
      height={400}
      fillPercent={interpolate(frame, [50, 120], [20, 95], { extrapolateRight: 'clamp' })}
      trackColor="#1E293B"
      fillGradient={['#475569', '#3B82F6']}
    />
    <PercentageReadout
      position={[1750, 280]}
      value={interpolate(frame, [50, 120], [20, 95], { extrapolateRight: 'clamp' })}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "part_icon": {
    "label": "THE PART",
    "position": [1500, 760],
    "initial_fill": "#475569",
    "final_fill": "#1E293B",
    "initial_scale": 1.0,
    "final_scale": 0.7
  },
  "mold_icon": {
    "label": "THE MOLD",
    "position": [1500, 340],
    "initial_fill": "#1E3A5F",
    "final_fill": "#3B82F6",
    "initial_scale": 0.8,
    "final_scale": 1.1
  },
  "value_bar": {
    "initial_percent": 20,
    "final_percent": 95
  },
  "particle_color": "#F59E0B",
  "total_frames": 450,
  "fps": 30
}
```

---
