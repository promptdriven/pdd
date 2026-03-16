[Remotion]

# Section 4.2: Mold Wall Constraint — Precision Through Boundaries

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 0:14 – 0:24

## Visual Description
A focused close-up on the injection mold principle applied to PDD. A clean mold cavity occupies center-screen with thick amber walls. A nozzle at the top pours liquid (blue particles) that flows chaotically until contacting walls. As liquid hits each wall segment, a constraint label appears on that wall — mapping the manufacturing metaphor directly to software tests. The cavity fills completely, producing a clean shape. A transition label fades in: "This maps directly to PDD." The visual makes the leap from physical metaphor to software development concrete.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (dark navy)
- No grid lines

### Chart/Visual Elements
- **Mold cavity:** Center of screen (x: 460–1460, y: 200–800), 1000×600px
  - Outer walls: 8px stroke, `#D9944A` at 0.7 opacity, rounded corners (12px radius)
  - Inner cavity shape: Irregular but symmetric — wider at top, narrow waist, wider at bottom (hourglass variant)
  - Wall segments: 6 distinct sections, each independently glowable
- **Nozzle:** Top-center at (960, 160), simplified funnel shape, `#6B7C93`
- **Liquid flow:** Blue particles (5px circles, `#4A90D9` at 0.4 opacity) streaming from nozzle
  - Chaotic initial spread: particles use random velocity with gravity bias
  - Contact behavior: particles stop at walls, accumulate, fill cavity bottom-up
- **Constraint labels (appear on wall contact):**
  - Wall 1 (left-top): `"handles null"` — `#D9944A`, 13px
  - Wall 2 (left-bottom): `"returns sorted list"` — `#D9944A`, 13px
  - Wall 3 (right-top): `"latency < 100ms"` — `#D9944A`, 13px
  - Wall 4 (right-bottom): `"no SQL injection"` — `#D9944A`, 13px
  - Wall 5 (bottom): `"valid JSON output"` — `#D9944A`, 13px
  - Wall 6 (top-right): `"idempotent retry"` — `#D9944A`, 13px
- **Transition text:** "This maps directly to PDD." — centered at (960, 900), `#FFFFFF` at 0.7 opacity, 22px

### Animation Sequence
1. **Frame 0–30 (0–1.0s):** Mold cavity outline draws in — walls trace clockwise from top-left. Nozzle fades in above.
2. **Frame 30–60 (1.0–2.0s):** Liquid begins pouring. Blue particles stream down, spread outward. Initial chaos — particles move in random directions within the cavity.
3. **Frame 60–120 (2.0–4.0s):** First wall contacts. Particles reach left walls — Wall 1 glows amber, label "handles null" slides in from left with 10px drift. 15-frame stagger, Wall 2 glows and labels. Particles redirect off walls and continue filling.
4. **Frame 120–180 (4.0–6.0s):** Right wall contacts. Walls 3 and 4 glow and label with same stagger pattern. Cavity ~50% filled. Particles accumulate in the bottom curves.
5. **Frame 180–220 (6.0–7.33s):** Bottom and top-right wall contacts. Walls 5 and 6 glow and label. Cavity ~80% filled. The shape is clearly constrained — liquid conforms to the cavity perfectly.
6. **Frame 220–260 (7.33–8.67s):** Cavity finishes filling. All walls glow simultaneously with a soft pulse. The complete shape glows `#4A90D9` at 0.2 opacity — a clean, wall-defined output.
7. **Frame 260–300 (8.67–10.0s):** Transition text "This maps directly to PDD." fades in at bottom with slight upward drift (8px). Hold.

### Typography
- Constraint labels: JetBrains Mono, 13px, `#D9944A` at 0.8 opacity
- Transition text: Inter Medium, 22px, `#FFFFFF` at 0.7 opacity
- No chart title — visual speaks for itself

### Easing
- Wall trace: `easeInOutCubic`
- Particle flow: linear with random velocity jitter (±25%)
- Wall glow pulse: `easeOutSine` (300ms on, 600ms settle to 0.3 opacity)
- Label slide-in: `spring({ damping: 15, stiffness: 100 })`
- Final fill glow: `easeInOutSine` (1s)
- Transition text fade: `easeOutCubic`

## Narration Sync
> "So, injection molding, precision comes from the walls. The material just flows until it's constrained."

> "This maps directly to PDD."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Mold cavity outline */}
    <Sequence from={0} durationInFrames={30}>
      <MoldCavityDraw
        bounds={{ x: 460, y: 200, width: 1000, height: 600 }}
        wallColor="#D9944A"
        wallWidth={8}
      />
    </Sequence>

    {/* Nozzle */}
    <Sequence from={0} durationInFrames={30}>
      <FadeIn>
        <Nozzle x={960} y={160} color="#6B7C93" />
      </FadeIn>
    </Sequence>

    {/* Liquid flow + wall contacts */}
    <Sequence from={30} durationInFrames={200}>
      <LiquidFillSimulation
        nozzle={{ x: 960, y: 180 }}
        cavityBounds={{ x: 460, y: 200, width: 1000, height: 600 }}
        particleColor="#4A90D9"
        wallGlowColor="#D9944A"
        constraintLabels={constraintLabels}
        labelStagger={15}
      />
    </Sequence>

    {/* Final glow */}
    <Sequence from={220} durationInFrames={40}>
      <CavityFillGlow color="rgba(74,144,217,0.2)" />
    </Sequence>

    {/* Transition text */}
    <Sequence from={260} durationInFrames={40}>
      <FadeIn yDrift={8}>
        <CenterText text="This maps directly to PDD." y={900} />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "cavity": {
    "bounds": { "x": 460, "y": 200, "width": 1000, "height": 600 },
    "wallColor": "#D9944A",
    "wallWidth": 8,
    "shape": "hourglass-variant"
  },
  "constraintLabels": [
    { "wall": "left-top", "text": "handles null", "contactFrame": 60 },
    { "wall": "left-bottom", "text": "returns sorted list", "contactFrame": 75 },
    { "wall": "right-top", "text": "latency < 100ms", "contactFrame": 120 },
    { "wall": "right-bottom", "text": "no SQL injection", "contactFrame": 135 },
    { "wall": "bottom", "text": "valid JSON output", "contactFrame": 180 },
    { "wall": "top-right", "text": "idempotent retry", "contactFrame": 195 }
  ],
  "transitionText": "This maps directly to PDD."
}
```

---
