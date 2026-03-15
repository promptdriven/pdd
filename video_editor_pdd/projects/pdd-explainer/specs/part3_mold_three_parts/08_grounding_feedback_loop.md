[Remotion]

# Section 3.8: Grounding Capital — The Material

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 14:47 - 15:03

## Visual Description
A panel showing material properties of the mold. The grounding concept is visualized as the "texture" or "flavor" of what fills the mold. Two paths demonstrate the same prompt and tests with different grounding contexts: Path A (OOP grounding) generates classes with methods; Path B (functional grounding) generates pure functions with composition. Then a feedback loop animation shows successful generations flowing back into a "Grounding Database" — a glowing repository. Future generations pull from this database, creating a virtuous cycle. After `pdd fix` succeeds, an arrow shows the (prompt, code) pair flowing to cloud storage.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Material Properties Panel:** Centered header region, Y=60
  - Label: "Grounding" — `#5AAA6E`, 32px bold
  - Sub-label: "Determines the properties of what fills the mold" — `#94A3B8`, 16px
- **Two Path Visualization (Y=160 to Y=550):**
  - Shared top element: Prompt document icon + Test wall icon — centered at X=960, Y=180
  - **Path A (left, X=360):**
    - Arrow from shared element, curving left
    - Grounding texture swatch: "OOP" in a rounded pill `rgba(90,170,110,0.2)`, border `#5AAA6E`
    - Generated code block: 380px wide x 200px tall, showing class-style code texture (indented blocks suggesting class + method pattern), faint green tint `rgba(90,170,110,0.1)`
    - Label: "Classes with methods" — `#5AAA6E`, 14px
  - **Path B (right, X=1560):**
    - Arrow from shared element, curving right
    - Grounding texture swatch: "Functional" in a rounded pill `rgba(90,170,110,0.2)`, border `#5AAA6E`
    - Generated code block: 380px wide x 200px tall, showing functional-style code texture (flat, sequential lines suggesting pure functions), faint green tint `rgba(90,170,110,0.1)`
    - Label: "Pure functions with composition" — `#5AAA6E`, 14px
- **Feedback Loop (Y=580 to Y=950):**
  - "Grounding Database" — Cylindrical database icon, `#5AAA6E` at 0.4 opacity, centered at X=960, Y=750, with ambient glow `rgba(90,170,110,0.2)` blur 10px
  - Successful generation icon (glowing code block with checkmark) at X=400, Y=720
  - Arrow from successful generation → database (curved, `#5AAA6E` at 0.5, animated flow particles)
  - Arrow from database → future generation (new code block at X=1520, Y=720), (curved, `#5AAA6E` at 0.5, animated flow particles)
  - Terminal snippet (bottom-right): After `pdd fix` succeeds, arrow shows "(prompt, code) pair" flowing to cloud icon — `rgba(90,170,110,0.3)`

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** "Grounding" header and sub-label fade in. Material properties visual context established
2. **Frame 40-100 (1.33-3.33s):** Shared prompt+test element appears at top-center. Two paths fork — arrows draw left and right simultaneously. Grounding texture swatches appear at each fork ("OOP" left, "Functional" right)
3. **Frame 100-200 (3.33-6.67s):** Both code blocks generate simultaneously — Path A fills with class-style texture, Path B with functional-style texture. Both get green tint from grounding. Labels fade in below each
4. **Frame 200-260 (6.67-8.67s):** Cross-fade transition. Two-path visualization dims. Feedback loop elements begin to appear
5. **Frame 260-360 (8.67-12.0s):** Feedback loop animation — successful generation glows, particles flow along curved arrow into the Grounding Database (database icon pulses as it receives data). Then particles flow outward from database to a new generation block. The cycle is visible
6. **Frame 360-420 (12.0-14.0s):** Terminal snippet appears showing `pdd fix` → success → arrow to cloud storage icon. Labels: "Your style. Your patterns. Your team's conventions." — `#FFFFFF`, 18px, staggered fade-in (one phrase per beat)
7. **Frame 420-480 (14.0-16.0s):** Hold. Database ambient glow pulses. Feedback arrows pulse with flowing particles

### Typography
- Header: Inter, 32px, bold (700), `#5AAA6E`
- Sub-header: Inter, 16px, regular (400), `#94A3B8`
- Grounding Pills: Inter, 14px, semi-bold (600), `#5AAA6E`
- Code Block Labels: Inter, 14px, regular (400), `#5AAA6E`
- Database Label: Inter, 18px, bold (700), `#5AAA6E`
- Terminal Text: JetBrains Mono, 12px, regular (400), `#94A3B8`
- Emphasis Phrases: Inter, 18px, semi-bold (600), `#FFFFFF`

### Easing
- Header fade: `easeOut(quad)`
- Path arrows: `easeOut(cubic)`
- Code block fill: `easeOut(cubic)`
- Feedback particles: `linear` (constant flow along path)
- Database pulse: `easeInOut(sine)` (looping)
- Phrase stagger: `easeOut(quad)` with 15-frame delay

## Narration Sync
> "Third: grounding. This determines the properties of what fills the mold."
> "Grounding is learned from your past generations. When you successfully generate and fix code, that knowledge feeds back into the system."
> "Your style. Your patterns. Your team's conventions. Grounding captures all of it and applies it automatically to future generations."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  {/* Header */}
  <Sequence from={0} durationInFrames={40}>
    <GroundingHeader title="Grounding" subtitle="Determines the properties of what fills the mold" />
  </Sequence>

  {/* Two Paths */}
  <Sequence from={40} durationInFrames={160}>
    <TwoPathVisualization
      sharedSource={{ prompt: true, tests: true }}
      pathA={{ grounding: "OOP", output: "Classes with methods" }}
      pathB={{ grounding: "Functional", output: "Pure functions with composition" }}
    />
  </Sequence>

  {/* Feedback Loop */}
  <Sequence from={260} durationInFrames={100}>
    <FeedbackLoop
      source="successful generation"
      database="Grounding Database"
      target="future generation"
      particleColor="#5AAA6E"
    />
  </Sequence>

  {/* Terminal + Phrases */}
  <Sequence from={360} durationInFrames={60}>
    <Terminal command="pdd fix" output="✓ → cloud" />
    <StaggeredPhrases
      phrases={["Your style.", "Your patterns.", "Your team's conventions."]}
      stagger={15}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "grounding": {
    "headerColor": "#5AAA6E",
    "tintOpacity": 0.1
  },
  "paths": [
    {
      "id": "pathA",
      "grounding": "OOP",
      "output": "Classes with methods",
      "position": "left"
    },
    {
      "id": "pathB",
      "grounding": "Functional",
      "output": "Pure functions with composition",
      "position": "right"
    }
  ],
  "feedbackLoop": {
    "databaseIcon": "cylinder",
    "databaseColor": "#5AAA6E",
    "databaseGlow": "rgba(90,170,110,0.2)",
    "particleColor": "#5AAA6E",
    "cloudStorage": true
  },
  "phrases": [
    "Your style.",
    "Your patterns.",
    "Your team's conventions."
  ]
}
```

---
