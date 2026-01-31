# Section 4.1: Split Screen - 3D Printer vs Injection Mold

**Tool:** Veo 3.1 (Video Generation)
**Duration:** ~15 seconds
**Timestamp:** 13:45 - 14:00

## Visual Description

Split screen introduction comparing two manufacturing paradigms. LEFT: A 3D printer depositing material layer by layer with precise movements. RIGHT: An injection mold with liquid plastic flowing freely until constrained by walls. This establishes the precision tradeoff metaphor.

## Veo 3.1 Prompt

```
Split screen comparison of two manufacturing processes.

LEFT SIDE:
- FDM 3D printer in operation
- Close-up of extruder nozzle depositing filament
- Precise, methodical layer-by-layer movement
- Clearly visible printed object taking shape
- Mechanical, deliberate motion

RIGHT SIDE:
- Injection mold cross-section view
- Liquid plastic flowing into mold cavity
- Material moves freely until hitting mold walls
- Walls constrain and shape the flow
- Organic, fluid motion that becomes precise at boundaries

COMPOSITION:
- Clean vertical divider between sides
- Both processes happening simultaneously
- Camera stable, no movement
- Professional industrial lighting
- Dark background, subject well-lit

ATMOSPHERE:
- Technical, precise feel on left
- Dynamic, constrained feel on right
- Both processes successful

NO PEOPLE
NO TEXT OVERLAY (will add in post)
DURATION: 15 seconds
```

## Technical Specifications

### Frame Composition

```
┌─────────────────┬─────────────────┐
│                 │                 │
│   3D PRINTER    │ INJECTION MOLD  │
│                 │                 │
│    ╔═══╗        │    ┌─────┐      │
│    ║   ║ ←nozzle│    │▓▓▓▓▓│←wall │
│    ║▒▒▒║ ←layer │    │▓████│←flow │
│    ╚═══╝        │    │▓▓▓▓▓│      │
│                 │    └─────┘      │
│                 │                 │
└─────────────────┴─────────────────┘
        ↑                   ↑
  Precise motion    Constrained flow
```

### Key Visual Contrasts

| Aspect | 3D Printer (LEFT) | Injection Mold (RIGHT) |
|--------|-------------------|------------------------|
| Motion | Precise, calculated | Free-flowing, then constrained |
| Control | Point-by-point specification | Boundary specification |
| Speed | Slow, methodical | Fast, fills instantly |
| Precision source | The machine path | The mold walls |

### Timing

1. **0-3s:** Both processes begin simultaneously
2. **3-8s:** Both in full operation, contrast visible
3. **8-12s:** Results becoming clear on both sides
4. **12-15s:** Hold on comparison, establish metaphor

## Post-Production (Remotion Overlay)

Minimal overlay for this section - the video carries the message:

```typescript
const SplitComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // Subtle divider line
  const dividerOpacity = interpolate(
    frame,
    [0, 30],
    [0, 0.5],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill>
      {/* Video base layer */}
      <Video src="3d_vs_mold.mp4" />

      {/* Center divider */}
      <div style={{
        position: 'absolute',
        left: '50%',
        top: 0,
        width: 2,
        height: '100%',
        backgroundColor: `rgba(255, 255, 255, ${dividerOpacity})`
      }} />
    </AbsoluteFill>
  );
};
```

## Narration Sync

> "Here's something subtle that changes how you think about prompts."

The split screen establishes the visual contrast before the narration explains what we're seeing.

## Audio Notes

- LEFT: Mechanical whirring, stepper motor sounds
- RIGHT: Hydraulic press sound, liquid flow
- Both sounds balanced, neither dominant
- Clean, industrial atmosphere

## Visual Style Notes

- Real manufacturing footage preferred over CGI
- Both processes should look successful and professional
- The contrast should be apparent without explanation
- Clean lighting, dark backgrounds
- No distracting elements

## Transition

Transitions to Section 4.2 where we focus on the 3D printer side with coordinate grid overlay.
