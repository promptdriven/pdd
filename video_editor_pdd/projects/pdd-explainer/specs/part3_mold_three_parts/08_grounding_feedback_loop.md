[Remotion]

# Section 3.7: Grounding Capital — The Material

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 15:00 – 15:16

## Visual Description
A circular feedback loop diagram showing how grounding works in PDD. The cycle starts with a successful code generation: (prompt + tests) → generated code → passes tests → the (prompt, code) pair feeds back into a "grounding store" (visualized as a cloud/database icon). From the grounding store, style, patterns, and conventions flow back into future generations as green material particles. Three example convention cards fan out from the grounding store: "Naming: snake_case", "Error handling: custom exceptions", "Imports: grouped by type". The grounding is shown as learned, not declared — it accumulates automatically from successful generations. The green color palette connects this back to the "material" region from the mold cross-section.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (dark navy)
- Grid lines: None

### Chart/Visual Elements
- **Feedback loop ring:** Centered at (960, 420), radius 220px
  - Circular arrow path, 3px stroke, `#5AAA6E` at 0.3 opacity
  - Four node positions on the ring (12 o'clock, 3, 6, 9):
    - 12 o'clock (960, 200): "Generate" — gear icon, `#4A90D9`
    - 3 o'clock (1180, 420): "Test" — checkmark icon, `#D9944A`
    - 6 o'clock (960, 640): "Grounding Store" — cloud/database icon, `#5AAA6E`, larger (40px)
    - 9 o'clock (740, 420): "Apply Style" — paintbrush icon, `#5AAA6E`
  - Animated flow particles: Small dots traveling clockwise along the ring path, `#5AAA6E` at 0.5, 4px

- **Section header:** "GROUNDING CAPITAL: THE MATERIAL" — top-left at (200, 80)
  - `#5AAA6E`, 20px, Inter Bold, uppercase, letter-spacing 3px

- **Convention cards (fanning out from grounding store):**
  - Three cards positioned below the 6 o'clock node, fanning at -20°, 0°, +20°
  - Each card: 240×50px, `#1E293B` background, left accent bar 3px `#5AAA6E`
  - Card 1: "Naming: snake_case" — `#FFFFFF` at 0.7, 14px
  - Card 2: "Error handling: custom exceptions" — `#FFFFFF` at 0.7, 14px
  - Card 3: "Imports: grouped by type" — `#FFFFFF` at 0.7, 14px

- **"Learned, not declared" label:** Positioned at (960, 860)
  - "Learned from your past generations" — `#5AAA6E` at 0.6, 16px
  - Small upward arrow connecting to grounding store icon

- **Style particles:** ~20 small green dots (`#5AAA6E` at 0.4, 3px) flowing from the grounding store back into the generation step, representing style being applied

### Animation Sequence
1. **Frame 0–30 (0–1.0s):** Section header "GROUNDING CAPITAL: THE MATERIAL" fades in with green underline drawing left→right.
2. **Frame 30–90 (1.0–3.0s):** Feedback loop ring draws on clockwise starting from 12 o'clock. As the path traces each node position, the node icon fades in with a subtle scale-up (0.9→1.0). Labels appear with each icon. Synced with "Third: grounding. This determines the properties of what fills the mold."
3. **Frame 90–180 (3.0–6.0s):** Flow particles begin traveling clockwise along the ring. A code-shaped packet (small rectangle) travels from "Generate" → "Test" → green checkmark flash → continues to "Grounding Store." The packet dissolves into green particles upon reaching the store. Synced with "When you successfully generate and fix code, that knowledge feeds back into the system."
4. **Frame 180–270 (6.0–9.0s):** Convention cards fan out from the grounding store node. Cards slide outward one by one (20-frame stagger) with slight rotation to their final angle. Each card fades in as it settles. Synced with "Your style. Your patterns. Your team's conventions."
5. **Frame 270–360 (9.0–12.0s):** Style particles flow from the grounding store back up through "Apply Style" and into "Generate." The particles are green, showing the material flowing back into the mold. The "Apply Style" node pulses green once. "Learned, not declared" label fades in below. Synced with "Grounding captures all of it and applies it automatically to future generations."
6. **Frame 360–420 (12.0–14.0s):** Full loop pulses — a green glow ripple travels once around the entire ring path (1s duration). All nodes pulse in sequence. Emphasizes the closed-loop nature.
7. **Frame 420–480 (14.0–16.0s):** Hold. Flow particles continue ambient circulation. Convention cards have subtle breathing animation. Grounding store icon maintains gentle green glow.

### Typography
- Section header: Inter Bold, 20px, `#5AAA6E`, letter-spacing 3px, uppercase
- Node labels: Inter Medium, 16px, `#FFFFFF` at 0.8 opacity
- Convention card text: Inter Regular, 14px, `#FFFFFF` at 0.7 opacity
- "Learned" label: Inter Medium, 16px, `#5AAA6E` at 0.6 opacity

### Easing
- Ring draw: `easeInOutCubic`
- Node fade/scale: `easeOutCubic`
- Flow particles: linear with slight sine-wave offset on Y
- Card fan-out: `spring({ damping: 14, stiffness: 100 })`
- Glow ripple: `easeInOutSine`
- Label fade: `easeOutQuad`

## Narration Sync
> "Third: grounding. This determines the properties of what fills the mold."

> "Grounding is learned from your past generations. When you successfully generate and fix code, that knowledge feeds back into the system."

> "Your style. Your patterns. Your team's conventions. Grounding captures all of it and applies it automatically to future generations."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Section header */}
    <Sequence from={0} durationInFrames={30}>
      <SectionHeader text="GROUNDING CAPITAL: THE MATERIAL" color="#5AAA6E" />
    </Sequence>

    {/* Feedback loop ring + nodes */}
    <Sequence from={30} durationInFrames={60}>
      <FeedbackLoopRing
        center={{ x: 960, y: 420 }}
        radius={220}
        nodes={[
          { position: "top", icon: "gear", label: "Generate", color: "#4A90D9" },
          { position: "right", icon: "check", label: "Test", color: "#D9944A" },
          { position: "bottom", icon: "cloud", label: "Grounding Store", color: "#5AAA6E" },
          { position: "left", icon: "brush", label: "Apply Style", color: "#5AAA6E" },
        ]}
        pathColor="#5AAA6E"
      />
    </Sequence>

    {/* Code packet traveling to grounding store */}
    <Sequence from={90} durationInFrames={90}>
      <FlowPacket
        path="clockwise"
        from="generate"
        to="grounding"
        dissolveColor="#5AAA6E"
      />
    </Sequence>

    {/* Convention cards */}
    <Sequence from={180} durationInFrames={90}>
      <FanOutCards
        origin={{ x: 960, y: 640 }}
        cards={[
          "Naming: snake_case",
          "Error handling: custom exceptions",
          "Imports: grouped by type"
        ]}
        color="#5AAA6E"
        stagger={20}
        fanAngle={20}
      />
    </Sequence>

    {/* Style particles flowing back */}
    <Sequence from={270} durationInFrames={90}>
      <StyleParticles
        from="grounding"
        to="generate"
        color="#5AAA6E"
        count={20}
      />
      <FadeIn>
        <Label text="Learned from your past generations" color="#5AAA6E" y={860} />
      </FadeIn>
    </Sequence>

    {/* Full loop pulse */}
    <Sequence from={360} durationInFrames={60}>
      <RingGlowRipple color="#5AAA6E" duration={30} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "loop": {
    "center": { "x": 960, "y": 420 },
    "radius": 220,
    "nodes": [
      { "position": "top", "label": "Generate", "color": "#4A90D9" },
      { "position": "right", "label": "Test", "color": "#D9944A" },
      { "position": "bottom", "label": "Grounding Store", "color": "#5AAA6E" },
      { "position": "left", "label": "Apply Style", "color": "#5AAA6E" }
    ]
  },
  "conventions": [
    "Naming: snake_case",
    "Error handling: custom exceptions",
    "Imports: grouped by type"
  ],
  "key_insight": "Grounding is learned from successful past generations, not manually declared"
}
```

---
