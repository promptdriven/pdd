# Section 4.3: Mold Flow Focus with Wall Highlights

**Tool:** Hybrid (Video + Remotion overlay)
**Duration:** ~15 seconds
**Timestamp:** 14:15 - 14:30

## Visual Description

Focus shifts to the injection mold. Remotion highlights the walls with amber glow as liquid flows into the cavity. The liquid moves chaotically until it hits the walls, then takes the precise shape. The message: Walls do the precision work, not the input specification.

## Video Base Options

### Option A: Extract from 4.1 Split Screen
Zoom/crop to right side of the split screen video from Section 4.1.

### Option B: Dedicated Veo 3.1 Generation

```
Cross-section view of injection mold filling with liquid plastic.

SUBJECT:
- Transparent/cutaway mold showing internal cavity
- Liquid plastic flowing into mold
- Clear mold walls visible
- Material taking shape of cavity

ACTION:
- Liquid enters from top (injection point)
- Flows freely through open space
- Hits walls and stops/redirects
- Eventually fills entire cavity

ENVIRONMENT:
- Dark background
- Well-lit mold interior
- Industrial setting
- Clean, technical look

CAMERA:
- Static cross-section view
- Side profile showing flow
- Walls clearly visible

NO PEOPLE
NO TEXT OVERLAY (Remotion will add)
DURATION: 15 seconds
```

## Remotion Overlay Specifications

### Canvas
- Resolution: 1920x1080
- Overlay on video base
- Amber glow effects on walls

### Overlay Elements

1. **Wall Highlight Glow**
   - Amber (#D9944A) glow around mold walls
   - Intensifies when liquid contacts wall
   - Pulsing effect at contact points

2. **Flow Path Indicators** (optional)
   - Subtle arrows showing liquid movement
   - Fade as liquid hits walls
   - Emphasizes free flow → constrained

3. **Label: "Walls do the precision work"**
   - Appears at bottom of frame
   - Fades in during second half

### Visual Design

```
┌────────────────────────────────────┐
│         ↓ injection point          │
│      ┌──────────────────┐          │
│      │                  │          │
│  ████│    ▓▓▓▓→         │████      │
│  ████│      ▓▓▓▓        │████      │  ← Walls glow
│  ████│        ▓▓▓▓      │████      │    amber (#D9944A)
│  ████│          ▓▓▓▓    │████      │
│  ████│            ↓     │████      │
│      └──────────────────┘          │
│                                    │
│    "Walls do the precision work"   │
└────────────────────────────────────┘
     ^liquid flows freely until walls
```

### Animation Sequence

1. **Frame 0-90 (0-3s):** Wall highlights fade in
   - Amber glow appears around mold walls
   - Subtle pulse animation
   - Liquid visible but not yet contacted

2. **Frame 90-180 (3-6s):** Flow contacts walls
   - Liquid hits first wall
   - Wall glow intensifies at contact point
   - Ripple effect from contact

3. **Frame 180-300 (6-10s):** Walls constrain flow
   - Multiple wall contacts
   - Each contact creates glow pulse
   - Liquid takes shape of cavity

4. **Frame 300-450 (10-15s):** Label appears
   - "Walls do the precision work" fades in
   - Walls maintain steady glow
   - Hold for narration

### Code Structure (Remotion)

```typescript
const MoldFlowFocus: React.FC = () => {
  const frame = useCurrentFrame();

  // Base wall glow
  const wallGlow = interpolate(
    frame,
    [0, 90],
    [0, 0.6],
    { extrapolateRight: 'clamp' }
  );

  // Contact pulse effect (multiple contact points)
  const contactPulse1 = frame > 90 ?
    Math.sin((frame - 90) * 0.2) * 0.3 + 0.7 : 0;
  const contactPulse2 = frame > 150 ?
    Math.sin((frame - 150) * 0.2) * 0.3 + 0.7 : 0;
  const contactPulse3 = frame > 210 ?
    Math.sin((frame - 210) * 0.2) * 0.3 + 0.7 : 0;

  // Label opacity
  const labelOpacity = interpolate(
    frame,
    [300, 360],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill>
      {/* Video base layer */}
      <Video src="mold_flow_closeup.mp4" />

      {/* Wall glow overlay */}
      <WallGlow
        baseOpacity={wallGlow}
        contactPoints={[
          { x: 300, y: 400, intensity: contactPulse1 },
          { x: 800, y: 350, intensity: contactPulse2 },
          { x: 550, y: 600, intensity: contactPulse3 },
        ]}
        color="#D9944A"
      />

      {/* Bottom label */}
      <Label
        text="Walls do the precision work"
        opacity={labelOpacity}
        position="bottom"
      />
    </AbsoluteFill>
  );
};
```

### Wall Glow Component

```typescript
interface ContactPoint {
  x: number;
  y: number;
  intensity: number;
}

const WallGlow: React.FC<{
  baseOpacity: number;
  contactPoints: ContactPoint[];
  color: string;
}> = ({ baseOpacity, contactPoints, color }) => {
  return (
    <>
      {/* Base wall outline glow */}
      <svg style={{
        position: 'absolute',
        width: '100%',
        height: '100%'
      }}>
        {/* Left wall */}
        <rect
          x={200} y={200}
          width={80} height={400}
          fill="none"
          stroke={color}
          strokeWidth={4}
          opacity={baseOpacity}
          filter="url(#glow)"
        />

        {/* Right wall */}
        <rect
          x={720} y={200}
          width={80} height={400}
          fill="none"
          stroke={color}
          strokeWidth={4}
          opacity={baseOpacity}
          filter="url(#glow)"
        />

        {/* Bottom wall */}
        <rect
          x={200} y={520}
          width={600} height={80}
          fill="none"
          stroke={color}
          strokeWidth={4}
          opacity={baseOpacity}
          filter="url(#glow)"
        />

        {/* Glow filter */}
        <defs>
          <filter id="glow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="8" result="coloredBlur"/>
            <feMerge>
              <feMergeNode in="coloredBlur"/>
              <feMergeNode in="SourceGraphic"/>
            </feMerge>
          </filter>
        </defs>
      </svg>

      {/* Contact point pulses */}
      {contactPoints.map((point, i) => (
        point.intensity > 0 && (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: point.x - 40,
              top: point.y - 40,
              width: 80,
              height: 80,
              borderRadius: '50%',
              background: `radial-gradient(circle, ${color}${Math.floor(point.intensity * 255).toString(16).padStart(2, '0')} 0%, transparent 70%)`,
            }}
          />
        )
      ))}
    </>
  );
};
```

### Easing

- Wall glow fade-in: `easeOutCubic`
- Contact pulses: `easeInOutSine` (organic feel)
- Label fade-in: `easeOutCubic`

## Narration Sync

> "In injection molding, precision comes from the walls. The material just flows until it's constrained."

The word "walls" lands as wall glow intensifies. "Constrained" emphasized by visible contact effects.

## Audio Notes

- Hydraulic/liquid sounds from video
- Subtle "thump" sound on wall contacts
- Organic, flowing audio that becomes solid

## Visual Style Notes

- Amber glow should be warm and visible
- Contact effects should be satisfying
- Contrast with the precise/mechanical feel of 4.2
- The walls are the heroes of this shot

## Transition

Cuts to Section 4.4 where we see the precision graph mapping this to PDD.
