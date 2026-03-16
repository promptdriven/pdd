[Remotion]

# Section 3.1: Mold Cross-Section — Three Components

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 13:04 – 13:18

## Visual Description
A technical cross-section of an injection mold is rendered schematically. The mold has three distinct regions that illuminate one by one: outer walls (tests, amber), inner cavity specification (prompt, blue), and material filling properties (grounding, green). The visualization starts as a single outlined shape, then each region lights up with its label as the narrator introduces the three components. Liquid code (visualized as flowing particles) fills the mold interior, constrained by the walls, shaped by the specification, and colored by the grounding material. The three-part framework is established visually before diving into each one.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (dark navy)
- Grid lines: None

### Chart/Visual Elements
- **Mold outline:** Centered at (960, 480), ~800×400px, rounded rectangle shape with thick walls
  - Outer stroke: 3px, `rgba(255,255,255,0.15)` initial, transitions to colored
  - Wall thickness: ~40px visual representation
- **Region 1 — Walls (Tests):**
  - The 40px-thick outer walls of the mold
  - Color: `#D9944A` (warm amber) at 0.7 opacity
  - Label: "Tests: The Walls" — positioned to the left of the mold at x=280
  - Connector line: 1px dashed, `#D9944A` at 0.4, pointing to wall region
- **Region 2 — Cavity (Prompt):**
  - The hollow interior shape of the mold — the specification of what gets created
  - Color: `#4A90D9` (cool blue) at 0.15 opacity fill, 2px border
  - Label: "Prompt: The Specification" — positioned to the right at x=1400
  - Connector line: 1px dashed, `#4A90D9` at 0.4, pointing to cavity
- **Region 3 — Material (Grounding):**
  - Particle texture filling the cavity — small dots representing the material properties
  - Color: `#5AAA6E` (soft green) particles, 3px radius, ~60 particles scattered
  - Label: "Grounding: The Material" — positioned below at y=760
  - Connector line: 1px dashed, `#5AAA6E` at 0.4, pointing upward to interior
- **Center equation (appears last):** "Intent + Constraints + Style = Complete Specification"
  - Positioned at y=900, centered, `#FFFFFF` at 0.6 opacity

### Animation Sequence
1. **Frame 0–45 (0–1.5s):** Mold outline draws on — outer rectangle traces clockwise from top-left. Interior cavity shape traces simultaneously. Both start as neutral white at low opacity.
2. **Frame 45–120 (1.5–4.0s):** Walls illuminate amber. The 40px wall region fills with `#D9944A` at 0.7, radiating outward from center like a glow. "Tests: The Walls" label fades in with connector line drawing outward. Synced with "In PDD, the mold has three components."
3. **Frame 120–195 (4.0–6.5s):** Cavity interior illuminates blue. The hollow space fills with `#4A90D9` at 0.15 opacity, a soft glow defining the shape. "Prompt: The Specification" label fades in with connector. Synced with "Three types of capital you're accumulating."
4. **Frame 195–270 (6.5–9.0s):** Grounding particles materialize. ~60 small green dots fade in scattered across the interior with slight random drift. "Grounding: The Material" label fades in from below. Particles have subtle Brownian motion (±2px random walk per second).
5. **Frame 270–360 (9.0–12.0s):** All three regions pulse gently in sequence (amber → blue → green, 0.5s each). Liquid code animation: streams of tiny code-like characters (`{`, `}`, `=`, `;`) flow downward into the mold cavity from above, constrained by walls, taking the shape of the cavity.
6. **Frame 360–420 (12.0–14.0s):** Center equation types on: "Intent + Constraints + Style = Complete Specification." Hold with all elements visible. Subtle ambient breathing on all three regions.

### Typography
- Region labels: Inter SemiBold, 22px, matching region color
- Connector labels: Inter Regular, 14px, matching region color at 0.6 opacity
- Center equation: Inter Medium, 20px, `#FFFFFF` at 0.6 opacity
- "+" and "=" in equation: Inter Regular, 20px, `#8B9DC3`

### Easing
- Mold outline draw: `easeInOutCubic`
- Region illumination: `easeOutCubic` (800ms each)
- Label fade-in: `easeOutQuad`
- Particle materialization: `easeOutExpo` (staggered, 20ms per particle)
- Equation type-on: linear
- Ambient pulse: `easeInOutSine` (looping, 3s period)

## Narration Sync
> "In PDD, the mold has three components. Three types of capital you're accumulating."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Mold outline */}
    <Sequence from={0} durationInFrames={45}>
      <MoldOutline cx={960} cy={480} width={800} height={400} wallThickness={40} />
    </Sequence>

    {/* Walls (Tests) illuminate */}
    <Sequence from={45} durationInFrames={75}>
      <WallRegion color="#D9944A" opacity={0.7} />
      <RegionLabel
        text="Tests: The Walls"
        color="#D9944A"
        x={280}
        y={480}
        connectorTarget={{ x: 560, y: 480 }}
      />
    </Sequence>

    {/* Cavity (Prompt) illuminate */}
    <Sequence from={120} durationInFrames={75}>
      <CavityRegion color="#4A90D9" fillOpacity={0.15} />
      <RegionLabel
        text="Prompt: The Specification"
        color="#4A90D9"
        x={1400}
        y={480}
        connectorTarget={{ x: 1360, y: 480 }}
      />
    </Sequence>

    {/* Material (Grounding) particles */}
    <Sequence from={195} durationInFrames={75}>
      <GroundingParticles count={60} color="#5AAA6E" radius={3} />
      <RegionLabel
        text="Grounding: The Material"
        color="#5AAA6E"
        x={960}
        y={760}
        connectorTarget={{ x: 960, y: 680 }}
      />
    </Sequence>

    {/* Code flow animation */}
    <Sequence from={270} durationInFrames={90}>
      <CodeFlowParticles direction="down" constrainTo="cavity" />
    </Sequence>

    {/* Equation */}
    <Sequence from={360} durationInFrames={60}>
      <TypeOnText
        text="Intent + Constraints + Style = Complete Specification"
        y={900}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "mold": {
    "center": { "x": 960, "y": 480 },
    "width": 800,
    "height": 400,
    "wallThickness": 40
  },
  "regions": [
    {
      "name": "Tests",
      "subtitle": "The Walls",
      "color": "#D9944A",
      "role": "constraints",
      "labelPosition": { "x": 280, "y": 480 }
    },
    {
      "name": "Prompt",
      "subtitle": "The Specification",
      "color": "#4A90D9",
      "role": "intent",
      "labelPosition": { "x": 1400, "y": 480 }
    },
    {
      "name": "Grounding",
      "subtitle": "The Material",
      "color": "#5AAA6E",
      "role": "style",
      "labelPosition": { "x": 960, "y": 760 }
    }
  ],
  "equation": "Intent + Constraints + Style = Complete Specification"
}
```

---
