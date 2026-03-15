[Remotion]

# Section 7.5: Mold Glow Finale — "The Code Is Just Plastic"

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 24:55 - 25:03

## Visual Description
The dissolve-regenerate loop fades, and the scene transitions to the injection mold metaphor from Part 2 returning for the final time. A cross-section of an injection mold fills the center of frame — the same clean, technical illustration style established earlier. The mold walls glow with warm, living light (amber for tests, blue for prompt outline, green accents for grounding). Inside the mold cavity, a plastic part sits — it's present but unremarkable, rendered in flat neutral gray with no glow, no highlight, no special treatment.

The visual hierarchy is absolute: the mold glows, the plastic doesn't. This is the final visual thesis — the specification is what matters, the code is just output.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep dark `#0A0F1A` fading to `#050810` at edges (vignette)
- Grid lines: None

### Chart/Visual Elements
- **Mold Cross-Section (centered at 960, 500):**
  - Outer shell: Rounded rectangle, 500x320px, 3px stroke
  - Left wall: `#D9944A` (tests/amber), 3px, with inner glow (12px blur, 50% opacity)
  - Right wall: `#D9944A` (tests/amber), matching left
  - Top outline: `#4A90D9` (prompt/blue), 3px, with inner glow (12px blur, 40% opacity)
  - Bottom detail: `#5AAA6E` (grounding/green), 2px accent lines inside the mold base
  - Corner radii: 8px outer, 4px inner cavity

- **Mold Glow Effect:**
  - Pulsing ambient glow radiating outward from mold walls
  - Amber glow on sides: `#D9944A` radial gradient, 40px reach, opacity pulsing 0.2→0.5→0.2
  - Blue glow on top: `#4A90D9` radial gradient, 30px reach, same pulse
  - Green accent glow on base: `#5AAA6E`, subtle, 20px reach

- **Plastic Part (inside mold cavity):**
  - Filled shape conforming to cavity interior, `#64748B` (neutral gray)
  - No glow, no shadow, no highlight — deliberately flat and unremarkable
  - 1px `#4A5568` border, no effects
  - Positioned inside the cavity, 4px inset from walls

- **Label Text (appearing after mold establishes):**
  - "The code is just plastic." — positioned below mold at (960, 780)

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Scene transition. Previous elements fade out. Mold cross-section fades in from center (opacity 0→1, scale 0.9→1.0). Mold arrives as a technical diagram — neutral, no glow yet.
2. **Frame 30-60 (1.0-2.0s):** Mold walls begin to glow. Amber glow ignites on left wall, sweeps to right wall (staggered 8 frames). Blue glow ignites on top. Green accents on base. The mold comes alive.
3. **Frame 60-90 (2.0-3.0s):** Plastic part fades in inside cavity (opacity 0→0.6). Deliberately understated — it just appears, while the mold continues to glow intensely around it. The contrast is the point.
4. **Frame 90-120 (3.0-4.0s):** Narration: "The code is just plastic." — Text fades in below the mold. Quiet, definitive.
5. **Frame 120-180 (4.0-6.0s):** Mold glow intensifies (pulse peak — all walls reach maximum brightness). Plastic part remains exactly the same. Unaffected, unremarkable, replaceable.
6. **Frame 180-240 (6.0-8.0s):** Hold. Mold continues gentle ambient pulse. The visual hierarchy speaks for itself.

### Typography
- Quote text: Inter, 32px, regular (400), `#94A3B8`, centered at (960, 780)
- No other text in scene

### Easing
- Mold fade-in: `easeOut(quad)`
- Mold scale: `easeOut(cubic)`
- Wall glow ignition: `easeOut(expo)` — sharp onset
- Glow pulse: `easeInOut(sin)` — smooth breathing
- Plastic part fade: `easeOut(quad)` — deliberate, slow
- Text fade: `easeOut(quad)`

## Narration Sync
> "The code is just plastic."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VignetteBackground center="#0A0F1A" edge="#050810" />

  {/* Mold Cross-Section */}
  <Sequence from={0}>
    <FadeInScale scale={[0.9, 1.0]} durationInFrames={30}>
      <MoldCrossSection position={[960, 500]} width={500} height={320}>
        {/* Mold Walls with Glow */}
        <Sequence from={30}>
          <WallGlow side="left" color="#D9944A" glowBlur={12} glowOpacity={0.5} />
          <Sequence from={8}>
            <WallGlow side="right" color="#D9944A" glowBlur={12} glowOpacity={0.5} />
          </Sequence>
          <Sequence from={12}>
            <WallGlow side="top" color="#4A90D9" glowBlur={12} glowOpacity={0.4} />
          </Sequence>
          <Sequence from={16}>
            <WallGlow side="bottom" color="#5AAA6E" glowBlur={8} glowOpacity={0.3} />
          </Sequence>
        </Sequence>

        {/* Plastic Part — deliberately flat */}
        <Sequence from={60}>
          <PlasticPart
            color="#64748B"
            borderColor="#4A5568"
            maxOpacity={0.6}
            durationInFrames={30}
          />
        </Sequence>
      </MoldCrossSection>
    </FadeInScale>
  </Sequence>

  {/* Glow Pulse Cycle */}
  <Sequence from={120}>
    <GlowPulse
      colors={["#D9944A", "#4A90D9", "#5AAA6E"]}
      cycleFrames={60}
      opacityRange={[0.2, 0.5]}
    />
  </Sequence>

  {/* Quote Text */}
  <Sequence from={90}>
    <FadeIn durationInFrames={20}>
      <CenteredText
        text="The code is just plastic."
        position={[960, 780]}
        font="Inter"
        size={32}
        color="#94A3B8"
      />
    </FadeIn>
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "mold": {
    "position": [960, 500],
    "width": 500,
    "height": 320,
    "cornerRadius": { "outer": 8, "inner": 4 },
    "walls": {
      "left": { "color": "#D9944A", "width": 3, "glowBlur": 12 },
      "right": { "color": "#D9944A", "width": 3, "glowBlur": 12 },
      "top": { "color": "#4A90D9", "width": 3, "glowBlur": 12 },
      "bottom": { "color": "#5AAA6E", "width": 2, "glowBlur": 8 }
    }
  },
  "plasticPart": {
    "color": "#64748B",
    "borderColor": "#4A5568",
    "opacity": 0.6,
    "glow": "none"
  },
  "glowPulse": {
    "cycleFrames": 60,
    "opacityRange": [0.2, 0.5]
  },
  "quoteText": {
    "text": "The code is just plastic.",
    "position": [960, 780],
    "color": "#94A3B8",
    "fontSize": 32
  },
  "background": {
    "center": "#0A0F1A",
    "edge": "#050810"
  }
}
```

---
