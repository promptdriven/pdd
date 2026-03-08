[Remotion] Three Pillars Equation Diagram — Synthesis Overlay

# Section 3.11: Three Pillars Equation Diagram

**Tool:** Remotion
**Duration:** ~10s
**Timestamp:** 4:30 - 4:40

## Visual Description
An animated equation diagram that appears during the synthesis moment. Three labeled pillars appear sequentially from left to right, connected by "+" signs, followed by an "=" sign and the result. The equation reads: **Prompt + Tests + Grounding = Complete Specification**. Each pillar is a rounded rectangle in its corresponding color (gold, green, purple) with an icon and label. Below the equation, a second row maps the abstract to the concrete: **Intent + Constraints + Style = The Mold**. After both rows are visible, the entire equation pulses once with a unified white glow, then holds.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo synthesis background
- Equation area: centered, (120, 300) to (1800, 780)

### Chart/Visual Elements
- Row 1 (primary equation, y=420):
  - Pillar 1: "Prompt" — rounded rect (200x100), #F59E0B fill at 20%, gold border, document icon
  - "+" connector: Inter Bold, 40px, #94A3B8, at x gap
  - Pillar 2: "Tests" — rounded rect (200x100), #22C55E fill at 20%, green border, checkmark icon
  - "+" connector: same style
  - Pillar 3: "Grounding" — rounded rect (200x100), #A855F7 fill at 20%, purple border, loop icon
  - "=" connector: Inter Bold, 48px, #FFFFFF, at x gap
  - Result: "Complete Specification" — rounded rect (360x100), white border, glow, bold text
- Row 2 (concrete mapping, y=600):
  - "Intent" — text only, #F59E0B, below Pillar 1
  - "+" — #94A3B8
  - "Constraints" — text only, #22C55E, below Pillar 2
  - "+" — #94A3B8
  - "Style" — text only, #A855F7, below Pillar 3
  - "=" — #FFFFFF
  - "The Mold" — text only, #FFFFFF, bold, below Result
- Connecting arrows: thin dashed lines from Row 1 pillars to Row 2 labels, 1px, 20% opacity

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Pillar 1 "Prompt" slides up from below — translateY(40)→0, opacity 0→1.
2. **Frame 15-25 (0.5-0.83s):** First "+" connector fades in.
3. **Frame 20-40 (0.67-1.33s):** Pillar 2 "Tests" slides up — same animation, staggered.
4. **Frame 35-45 (1.17-1.5s):** Second "+" connector fades in.
5. **Frame 40-60 (1.33-2s):** Pillar 3 "Grounding" slides up — same animation, staggered.
6. **Frame 55-70 (1.83-2.33s):** "=" sign fades in, scale 0.5→1.0.
7. **Frame 65-85 (2.17-2.83s):** "Complete Specification" result fades in with glow effect.
8. **Frame 85-120 (2.83-4s):** Row 2 labels fade in sequentially — "Intent", "+", "Constraints", "+", "Style", "=", "The Mold" (5-frame stagger each).
9. **Frame 115-130 (3.83-4.33s):** Connecting dashed arrows fade in.
10. **Frame 130-145 (4.33-4.83s):** Entire equation pulses — brief white glow overlay, scale 1.0→1.02→1.0.
11. **Frame 145-250 (4.83-8.33s):** Hold.
12. **Frame 250-300 (8.33-10s):** Fade out — opacity 1→0.

### Typography
- Pillar labels: Inter Bold, 24px, #FFFFFF
- Pillar icons: 28px, matching pillar color
- Connectors (+, =): Inter Bold, 40-48px
- Row 2 abstract labels: Inter Medium, 20px, matching pillar color
- "Complete Specification": Inter Black, 28px, #FFFFFF
- "The Mold": Inter Black, 24px, #FFFFFF, text-shadow glow

### Easing
- Pillar slide up: `spring({ damping: 14, stiffness: 200 })`
- Connector fades: `easeOutQuad`
- Result glow: `easeOutQuart`
- Pulse: `easeInOutSine`
- Fade out: `easeInCubic`

## Narration Sync
> "Prompt plus tests plus grounding equals intent plus constraints plus style equals a complete specification."

Each pillar appears as its name is spoken. The "=" and result appear on "equals a complete specification."

## Code Structure (Remotion)
```typescript
<Sequence from={PILLARS_START} durationInFrames={300}>
  <AbsoluteFill style={{
    opacity: interpolate(frame, [0, 5, 250, 300], [0, 1, 1, 0]),
  }}>
    {/* Row 1: Pillars */}
    <EquationRow y={420}>
      <Pillar
        label="Prompt"
        icon="document"
        color="#F59E0B"
        style={{
          opacity: interpolate(frame, [0, 20], [0, 1]),
          transform: `translateY(${interpolate(frame, [0, 20], [40, 0], { extrapolateRight: 'clamp' })}px)`,
        }}
      />
      <Connector text="+" opacity={interpolate(frame, [15, 25], [0, 1])} />
      <Pillar
        label="Tests"
        icon="checkmark"
        color="#22C55E"
        style={{
          opacity: interpolate(frame, [20, 40], [0, 1]),
          transform: `translateY(${interpolate(frame, [20, 40], [40, 0], { extrapolateRight: 'clamp' })}px)`,
        }}
      />
      <Connector text="+" opacity={interpolate(frame, [35, 45], [0, 1])} />
      <Pillar
        label="Grounding"
        icon="loop"
        color="#A855F7"
        style={{
          opacity: interpolate(frame, [40, 60], [0, 1]),
          transform: `translateY(${interpolate(frame, [40, 60], [40, 0], { extrapolateRight: 'clamp' })}px)`,
        }}
      />
      <Connector
        text="="
        fontSize={48}
        color="#FFFFFF"
        style={{
          opacity: interpolate(frame, [55, 70], [0, 1]),
          transform: `scale(${interpolate(frame, [55, 70], [0.5, 1.0], { extrapolateRight: 'clamp' })})`,
        }}
      />
      <ResultBox
        label="Complete Specification"
        glowOpacity={interpolate(frame, [65, 85], [0, 1])}
      />
    </EquationRow>

    {/* Row 2: Abstract mapping */}
    <EquationRow y={600}>
      {['Intent', '+', 'Constraints', '+', 'Style', '=', 'The Mold'].map((text, i) => (
        <MappingLabel
          key={text}
          text={text}
          color={labelColors[i]}
          opacity={interpolate(frame, [85 + i * 5, 95 + i * 5], [0, 1])}
        />
      ))}
    </EquationRow>

    {/* Pulse overlay */}
    <PulseOverlay
      opacity={interpolate(frame, [130, 138, 145], [0, 0.15, 0])}
      scale={interpolate(frame, [130, 138, 145], [1.0, 1.02, 1.0])}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "equation_row_1": [
    {"type": "pillar", "label": "Prompt", "color": "#F59E0B", "icon": "document"},
    {"type": "connector", "text": "+"},
    {"type": "pillar", "label": "Tests", "color": "#22C55E", "icon": "checkmark"},
    {"type": "connector", "text": "+"},
    {"type": "pillar", "label": "Grounding", "color": "#A855F7", "icon": "loop"},
    {"type": "connector", "text": "="},
    {"type": "result", "label": "Complete Specification"}
  ],
  "equation_row_2": ["Intent", "+", "Constraints", "+", "Style", "=", "The Mold"],
  "totalFrames": 300,
  "fps": 30
}
```

---
