[Remotion] Interactive Precision Spectrum Slider Visualization

# Section 4.6: Precision Spectrum Slider

**Tool:** Remotion
**Duration:** ~25s
**Timestamp:** 1:05 - 1:30

## Visual Description
An animated horizontal spectrum/slider bar that visualizes the range of precision strategies. The spectrum runs from "Exploration" (left, blue) to "Enforcement" (right, amber). A glowing handle dot animates along the spectrum, pausing at two key positions to illustrate context-dependent choices. Below the spectrum bar, two context cards pop up when the handle reaches their positions:
- Left position: "Greenfield" card — blue-tinted, with traits "fast iteration, light prompts, exploratory tests"
- Right position: "Legacy/Contract" card — amber-tinted, with traits "strict prompts, heavy test walls, precise contracts"
The spectrum bar itself has a gradient fill from blue→amber. Tick marks along the bar indicate intermediate precision levels. The visualization makes clear that precision is a spectrum tool, not a binary choice.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Spectrum bar: centered horizontally at y=420, from x=240 to x=1680 (1440px wide), 12px height
- Context cards: 400px x 220px, positioned below spectrum at y=520

### Chart/Visual Elements
- Spectrum bar:
  - Gradient fill: #3B82F6 (left/blue) → #64748B (center/gray) → #F59E0B (right/amber)
  - Border-radius: 6px
  - Background track: rgba(255, 255, 255, 0.1), 12px
- Handle dot: 24px circle, white (#FFFFFF) with colored glow matching position
  - Glow: 40px radius, color interpolated from blue→amber based on position
- Tick marks: 8 evenly spaced vertical ticks, 2px x 20px, #475569 at 40% opacity
- Left label: "EXPLORATION" at x=240, above bar
- Right label: "ENFORCEMENT" at x=1680, above bar
- Center label: "BALANCED" at x=960, above bar (faded)
- Greenfield card (left position ~x=480):
  - Background: rgba(59, 130, 246, 0.12) with blur(8px)
  - Border: 1px solid rgba(59, 130, 246, 0.3)
  - Title: "Greenfield Project"
  - Traits: "Fast iteration · Light prompts · Exploratory tests"
  - Icon: rocket silhouette, #3B82F6 at 20% opacity
- Legacy card (right position ~x=1440):
  - Background: rgba(245, 158, 11, 0.12) with blur(8px)
  - Border: 1px solid rgba(245, 158, 11, 0.3)
  - Title: "Legacy / Contract System"
  - Traits: "Strict prompts · Heavy test walls · Precise contracts"
  - Icon: shield/lock silhouette, #F59E0B at 20% opacity

### Animation Sequence
1. **Frame 0-30 (0-1s):** Spectrum bar fades in — opacity 0→1, width 0→1440px (expanding from center).
2. **Frame 20-40 (0.67-1.33s):** Labels "EXPLORATION" and "ENFORCEMENT" fade in — opacity 0→1.
3. **Frame 30-50 (1-1.67s):** Tick marks fade in — opacity 0→0.4.
4. **Frame 40-60 (1.33-2s):** Handle dot appears at center — scale 0→1 with spring.
5. **Frame 60-150 (2-5s):** Handle slides to left position (~x=480) — smooth translation.
6. **Frame 140-180 (4.67-6s):** Greenfield card pops up below handle — scale 0.9→1, opacity 0→1.
7. **Frame 180-320 (6-10.67s):** Hold at left position. Handle glow pulses blue.
8. **Frame 320-420 (10.67-14s):** Handle slides from left to right position (~x=1440) — smooth translation with glow color transitioning blue→amber.
9. **Frame 340-360 (11.33-12s):** Greenfield card fades out — opacity 1→0.
10. **Frame 400-440 (13.33-14.67s):** Legacy card pops up — scale 0.9→1, opacity 0→1.
11. **Frame 440-650 (14.67-21.67s):** Hold at right position. Handle glow pulses amber.
12. **Frame 650-700 (21.67-23.33s):** Handle slides back to center. Both cards gone. "BALANCED" label brightens.
13. **Frame 700-750 (23.33-25s):** Entire visualization fades out — opacity 1→0.

### Typography
- Spectrum labels: Inter Bold, 18px, uppercase, letter-spacing 0.15em
  - "EXPLORATION": #3B82F6
  - "ENFORCEMENT": #F59E0B
  - "BALANCED": #94A3B8 (faded), brightens to #CBD5E1 at end
- Card title: Inter SemiBold, 24px, #FFFFFF
- Card traits: Inter Regular, 16px, matching panel color at 80% opacity
- Card traits separator: " · " (middle dot)

### Easing
- Spectrum bar expand: `easeInOutCubic`
- Handle appear: `spring({ damping: 14, stiffness: 200 })`
- Handle slide: `easeInOutQuad`
- Card pop up: `spring({ damping: 12, stiffness: 180 })`
- Handle glow color: linear interpolation based on x-position
- Fade out: `easeInCubic`

## Narration Sync
> "Adjust precision based on context. Greenfield project? Lighter prompts, explore fast. Legacy system with strict contracts? Heavy test walls, precise prompts. The spectrum is a tool, not a rule."

Handle slides left and Greenfield card appears on "Greenfield project? Lighter prompts, explore fast." Handle slides right and Legacy card appears on "Legacy system with strict contracts? Heavy test walls, precise prompts." Handle returns to center on "The spectrum is a tool, not a rule."

## Code Structure (Remotion)
```typescript
<Sequence from={SPECTRUM_START} durationInFrames={750}>
  <AbsoluteFill>
    {/* Spectrum bar */}
    <SpectrumBar
      width={interpolate(frame, [0, 30], [0, 1440], { extrapolateRight: 'clamp' })}
      gradient={['#3B82F6', '#64748B', '#F59E0B']}
      opacity={interpolate(frame, [0, 30, 700, 750], [0, 1, 1, 0])}
    />

    {/* Labels */}
    <SpectrumLabel
      text="EXPLORATION" side="left" color="#3B82F6"
      opacity={interpolate(frame, [20, 40, 700, 750], [0, 1, 1, 0])}
    />
    <SpectrumLabel
      text="ENFORCEMENT" side="right" color="#F59E0B"
      opacity={interpolate(frame, [20, 40, 700, 750], [0, 1, 1, 0])}
    />

    {/* Handle */}
    <SpectrumHandle
      position={handlePosition(frame)} // center→left→right→center
      scale={spring({ frame: Math.max(0, frame - 40), fps: 30, config: { damping: 14, stiffness: 200 } })}
      glowColor={interpolateColors(frame, [60, 150, 320, 420, 650, 700],
        ['#3B82F6', '#3B82F6', '#3B82F6', '#F59E0B', '#F59E0B', '#94A3B8'])}
    />

    {/* Greenfield card */}
    <Sequence from={140} durationInFrames={220}>
      <ContextCard
        title="Greenfield Project"
        traits="Fast iteration · Light prompts · Exploratory tests"
        color="#3B82F6"
        position="left"
        opacity={interpolate(frame, [0, 40, 180, 220], [0, 1, 1, 0])}
        scale={interpolate(frame, [0, 40], [0.9, 1], { extrapolateRight: 'clamp' })}
      />
    </Sequence>

    {/* Legacy card */}
    <Sequence from={400} durationInFrames={300}>
      <ContextCard
        title="Legacy / Contract System"
        traits="Strict prompts · Heavy test walls · Precise contracts"
        color="#F59E0B"
        position="right"
        opacity={interpolate(frame, [0, 40, 250, 300], [0, 1, 1, 0])}
        scale={interpolate(frame, [0, 40], [0.9, 1], { extrapolateRight: 'clamp' })}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "spectrum": {
    "left": {"label": "EXPLORATION", "color": "#3B82F6"},
    "center": {"label": "BALANCED", "color": "#94A3B8"},
    "right": {"label": "ENFORCEMENT", "color": "#F59E0B"}
  },
  "contexts": [
    {
      "position": 0.17,
      "title": "Greenfield Project",
      "traits": ["Fast iteration", "Light prompts", "Exploratory tests"],
      "color": "#3B82F6"
    },
    {
      "position": 0.83,
      "title": "Legacy / Contract System",
      "traits": ["Strict prompts", "Heavy test walls", "Precise contracts"],
      "color": "#F59E0B"
    }
  ],
  "totalFrames": 750,
  "fps": 30
}
```

---
