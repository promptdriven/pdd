# Section 3.10: Injection Nozzle (Prompt Capital)

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 11:10 - 11:25

## Visual Description

Return to the mold cross-section. The injection nozzle highlights in blue. Labels appear: "intent", "requirements", "constraints". This introduces the second type of capital: the prompt specification.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Mold cross-section view

### Animation Elements

1. **Mold Cross-Section**
   - Full view returns
   - Walls dimmed slightly (not focus)
   - Nozzle area brightens

2. **Nozzle Highlight**
   - Blue glow (#4A90D9)
   - Pulsing animation
   - Clear focus point

3. **Concept Labels**
   - "intent" - what you want
   - "requirements" - what it needs
   - "constraints" - boundaries (but different from test walls)
   - Labels orbit or connect to nozzle

4. **Section Title**
   - "PROMPT CAPITAL" fades in
   - Subtitle: "The Specification"

### Animation Sequence

1. **Frame 0-90 (0-3s):** Return to mold
   - Cross-section fades in
   - Walls visible but dimmed
   - Preparing for nozzle focus

2. **Frame 90-180 (3-6s):** Nozzle highlights
   - Blue glow intensifies on nozzle
   - Walls fade to ~50% opacity
   - Nozzle becomes focal point

3. **Frame 180-240 (6-8s):** "Intent" label
   - First label appears
   - Connected to nozzle with line
   - Subtle pulse

4. **Frame 240-300 (8-10s):** "Requirements" label
   - Second label appears
   - Different position around nozzle

5. **Frame 300-360 (10-12s):** "Constraints" label
   - Third label appears
   - Note: conceptual constraints, not test walls

6. **Frame 360-450 (12-15s):** Section title
   - "PROMPT CAPITAL" fades in
   - "The Specification" subtitle
   - Hold for narration

### Visual Design: Nozzle Focus

```
                   ┌─────────────────┐
                   │                 │
           ┌───────┴───────┐         │
           │   ◆ NOZZLE ◆  │◄──── Blue glow (#4A90D9)
           │    (prompt)   │
           └───────┬───────┘
                   │
        intent ────┘────── requirements
                   │
               constraints

        ╔═══════════════════════════╗
        ║     PROMPT CAPITAL        ║
        ║    The Specification      ║
        ╚═══════════════════════════╝
```

### Code Structure (Remotion)

```typescript
const InjectionNozzle: React.FC = () => {
  const frame = useCurrentFrame();

  // Wall dimming
  const wallOpacity = interpolate(
    frame,
    [90, 150],
    [1, 0.4],
    { extrapolateRight: 'clamp' }
  );

  // Nozzle glow
  const nozzleGlow = interpolate(
    frame,
    [90, 180],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Pulse animation
  const pulseScale = 1 + Math.sin(frame * 0.1) * 0.05;

  // Labels
  const labels = [
    { text: "intent", start: 180, position: { x: -100, y: 50 } },
    { text: "requirements", start: 240, position: { x: 120, y: 30 } },
    { text: "constraints", start: 300, position: { x: 0, y: 100 } },
  ];

  // Title
  const titleOpacity = interpolate(
    frame,
    [360, 400],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      <MoldCrossSection wallOpacity={wallOpacity} />

      {/* Nozzle with glow */}
      <NozzleHighlight
        glowIntensity={nozzleGlow}
        scale={pulseScale}
        color="#4A90D9"
      />

      {/* Concept labels */}
      {labels.map((label, i) => {
        const opacity = interpolate(
          frame,
          [label.start, label.start + 30],
          [0, 1],
          { extrapolateRight: 'clamp' }
        );
        return (
          <ConceptLabel
            key={i}
            text={label.text}
            position={label.position}
            opacity={opacity}
            color="#4A90D9"
          />
        );
      })}

      {/* Section title */}
      <SectionTitle
        title="PROMPT CAPITAL"
        subtitle="The Specification"
        opacity={titleOpacity}
      />
    </AbsoluteFill>
  );
};
```

### Nozzle Glow Effect

```typescript
const NozzleHighlight: React.FC<{
  glowIntensity: number;
  scale: number;
  color: string;
}> = ({ glowIntensity, scale, color }) => {
  return (
    <g transform={`translate(960, 200) scale(${scale})`}>
      {/* Glow layers */}
      <ellipse
        cx={0}
        cy={0}
        rx={80 * glowIntensity}
        ry={40 * glowIntensity}
        fill={color}
        opacity={0.2 * glowIntensity}
        filter="url(#blur-lg)"
      />
      <ellipse
        cx={0}
        cy={0}
        rx={50 * glowIntensity}
        ry={25 * glowIntensity}
        fill={color}
        opacity={0.4 * glowIntensity}
        filter="url(#blur-md)"
      />
      {/* Nozzle shape */}
      <NozzleShape fill={color} opacity={0.8 + 0.2 * glowIntensity} />
    </g>
  );
};
```

### Easing

- Wall dimming: `easeOutQuad`
- Nozzle glow: `easeOutCubic`
- Pulse: `easeInOutSine`
- Label fade: `easeOutCubic`
- Title fade: `easeOutCubic`

## Narration Sync

> "Second: the prompt. Your specification of what you want."

The nozzle highlights and glows as "prompt" is spoken. Labels appear during "specification of what you want".

## Audio Notes

- Soft "rise" tone as nozzle highlights
- Subtle ping for each label
- Blue-coded audio (different timbre from amber walls)
- Building sense of second concept

## Visual Style Notes

- Blue contrasts with amber walls
- Nozzle is the SOURCE, walls are the BOUNDARIES
- Labels are conceptual, not technical like test labels
- This is about intent, not constraint
- 3Blue1Brown: different color = different concept

## Transition

Continues into Section 3.11 where prompt text flows into the mold.
