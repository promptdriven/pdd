# Section 3.2: Walls Illuminate

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 10:45 - 11:05

## Visual Description

The walls of the mold illuminate fully in amber. Each wall segment receives a specific test label: "null → None", "empty string → ''", "handles unicode", "latency < 100ms". This establishes tests as the constraining boundaries.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Continuation from Section 3.1

### Animation Elements

1. **Wall Segments**
   - Four distinct wall sections
   - Each becomes a glowing amber barrier
   - Clean, sharp edges (precision is key)

2. **Test Labels**
   - Monospace font for technical feel
   - Fade in sequentially
   - Connected to wall segments with subtle lines

3. **Glow Effect**
   - Soft outer glow on walls (#D9944A at 40% opacity)
   - Pulsing slightly to indicate "active" constraints

### Wall Labels

| Position | Label | Meaning |
|----------|-------|---------|
| Top | `null → None` | Handles null input |
| Right | `empty string → ''` | Handles empty strings |
| Bottom | `handles unicode` | Unicode support |
| Left | `latency < 100ms` | Performance constraint |

### Animation Sequence

1. **Frame 0-60 (0-2s):** Initial state
   - Mold visible from previous section
   - Walls highlighted but not labeled

2. **Frame 60-120 (2-4s):** First label appears
   - Top wall pulses brighter
   - "null → None" label fades in
   - Connecting line draws

3. **Frame 120-180 (4-6s):** Second label appears
   - Right wall pulses
   - "empty string → ''" label fades in

4. **Frame 180-240 (6-8s):** Third label appears
   - Bottom wall pulses
   - "handles unicode" label fades in

5. **Frame 240-300 (8-10s):** Fourth label appears
   - Left wall pulses
   - "latency < 100ms" label fades in

6. **Frame 300-450 (10-15s):** All labels visible
   - All walls glowing steadily
   - Labels clearly readable
   - Hold for narration

### Visual Design: Labeled Walls

```
                    ┌─────────────────┐
    null → None ───►│█████████████████│
                    │                 │
    latency    ───► │                 │ ◄─── empty string
    < 100ms         │                 │       → ''
                    │                 │
                    │█████████████████│◄─── handles unicode
                    └─────────────────┘
```

### Code Structure (Remotion)

```typescript
const WallsIlluminate: React.FC = () => {
  const frame = useCurrentFrame();

  const labels = [
    { text: "null → None", position: "top", start: 60 },
    { text: "empty string → ''", position: "right", start: 120 },
    { text: "handles unicode", position: "bottom", start: 180 },
    { text: "latency < 100ms", position: "left", start: 240 },
  ];

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      <MoldCrossSection />
      <WallGlow color="#D9944A" />
      {labels.map((label, i) => {
        const opacity = interpolate(
          frame,
          [label.start, label.start + 30],
          [0, 1],
          { extrapolateRight: 'clamp' }
        );
        return (
          <WallLabel
            key={i}
            text={label.text}
            position={label.position}
            opacity={opacity}
          />
        );
      })}
    </AbsoluteFill>
  );
};
```

### Typography

- Label font: `JetBrains Mono` or similar monospace
- Size: 24px for labels
- Color: White with slight amber tint (#FFF8F0)
- Shadow: Subtle drop shadow for readability

### Easing

- Wall pulse: `easeInOutSine`
- Label fade-in: `easeOutCubic`
- Line draw: `easeOutQuad`

## Narration Sync

> "First: tests. Tests are the walls of your mold."

Each wall segment pulses as the word "walls" is emphasized.

## Audio Notes

- Soft "click" as each label appears
- Ambient hum from glowing walls
- Building tension for the injection animation

## Visual Style Notes

- Labels should look like technical specifications
- Walls convey immutable constraint
- The precision of the labels matches the precision of the mold
- 3Blue1Brown style: clean, mathematical, elegant

## Transition

Continues into Section 3.3 where liquid (code generation) is injected and constrained by these walls.
