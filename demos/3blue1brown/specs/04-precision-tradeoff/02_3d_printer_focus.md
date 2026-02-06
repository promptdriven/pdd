# Section 4.2: 3D Printer Focus with Coordinate Grid

**Tool:** Hybrid (Video + Remotion overlay)
**Duration:** ~15 seconds
**Timestamp:** 16:15 - 16:30

## Visual Description

Focus shifts to the 3D printer. A Remotion-generated coordinate grid overlays the video, emphasizing that every single point must be specified. X, Y, Z coordinates appear as the nozzle moves. The message: 3D printing requires complete, precise specification.

## Video Base Options

### Option A: Extract from 4.1 Split Screen
Zoom/crop to left side of the split screen video from Section 4.1.

### Option B: Dedicated Veo 3.1 Generation

```
Close-up of FDM 3D printer extruder in operation.

SUBJECT:
- 3D printer nozzle/extruder head
- Visible filament being deposited
- Partially printed object below
- Clear X-Y motion visible

ACTION:
- Continuous precise movements
- Layer-by-layer deposition
- Mechanical, calculated motion
- No pauses or hesitation

ENVIRONMENT:
- Dark background
- Well-lit subject
- Industrial/workshop setting
- Clean, uncluttered

CAMERA:
- Static shot, slightly above eye level
- Close enough to see detail
- Full nozzle assembly visible

NO PEOPLE
NO TEXT OVERLAY (Remotion will add)
DURATION: 15 seconds
```

## Remotion Overlay Specifications

### Canvas
- Resolution: 1920x1080
- Overlay on video base
- Semi-transparent elements

### Overlay Elements

1. **Coordinate Grid**
   - 3D perspective grid lines
   - Color: Light blue (#5A9FE9) at 30% opacity
   - Aligned to printer axes

2. **Axis Labels**
   - X, Y, Z labels at grid edges
   - Monospace font
   - White with subtle glow

3. **Current Position Indicator**
   - Tracks nozzle position
   - Shows current (X, Y, Z) values
   - Updates as nozzle moves

4. **Label: "Every point must be specified"**
   - Appears at bottom of frame
   - Fades in during second half

### Visual Design

```
┌────────────────────────────────────┐
│  X ─────────────────────────────   │
│  │                                 │
│  │     ┌───────────────────┐       │
│  │     │  ╔═══╗ ← [X: 142] │       │
│  │ Y   │  ║   ║   [Y: 87]  │       │
│  │     │  ║▒▒▒║   [Z: 23]  │       │
│  │     │  ╚═══╝            │       │
│  │     └───────────────────┘       │
│  │                           Z ↗   │
│                                    │
│   "Every point must be specified"  │
└────────────────────────────────────┘
```

### Animation Sequence

1. **Frame 0-90 (0-3s):** Grid fades in
   - Coordinate grid overlays video
   - X, Y, Z labels appear
   - Grid aligned to printer motion

2. **Frame 90-180 (3-6s):** Position tracking begins
   - Current position indicator follows nozzle
   - X, Y, Z values update
   - Emphasizes precise positioning

3. **Frame 180-300 (6-10s):** Continue tracking
   - Multiple coordinate updates visible
   - Grid pulses subtly with movement
   - Building visual complexity

4. **Frame 300-450 (10-15s):** Label appears
   - "Every point must be specified" fades in
   - Position tracking continues
   - Hold for narration

### Code Structure (Remotion)

```typescript
const PrinterFocus: React.FC = () => {
  const frame = useCurrentFrame();

  // Grid opacity
  const gridOpacity = interpolate(
    frame,
    [0, 90],
    [0, 0.3],
    { extrapolateRight: 'clamp' }
  );

  // Position indicator (simulated tracking)
  const nozzleX = 142 + Math.sin(frame * 0.05) * 30;
  const nozzleY = 87 + Math.cos(frame * 0.03) * 20;
  const nozzleZ = 23 + (frame > 180 ? 1 : 0);

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
      <Video src="3d_printer_closeup.mp4" />

      {/* Coordinate grid overlay */}
      <CoordinateGrid3D opacity={gridOpacity} />

      {/* Axis labels */}
      <AxisLabels opacity={gridOpacity} />

      {/* Position indicator */}
      {frame > 90 && (
        <PositionIndicator
          x={nozzleX}
          y={nozzleY}
          z={nozzleZ}
        />
      )}

      {/* Bottom label */}
      <Label
        text="Every point must be specified"
        opacity={labelOpacity}
        position="bottom"
      />
    </AbsoluteFill>
  );
};
```

### Coordinate Grid Component

```typescript
const CoordinateGrid3D: React.FC<{ opacity: number }> = ({ opacity }) => {
  return (
    <svg
      style={{
        position: 'absolute',
        width: '100%',
        height: '100%',
        opacity
      }}
    >
      {/* X-axis lines */}
      {[...Array(10)].map((_, i) => (
        <line
          key={`x-${i}`}
          x1={200 + i * 80}
          y1={100}
          x2={200 + i * 80 - 100}
          y2={600}
          stroke="#5A9FE9"
          strokeWidth={1}
        />
      ))}

      {/* Y-axis lines */}
      {[...Array(8)].map((_, i) => (
        <line
          key={`y-${i}`}
          x1={100}
          y1={150 + i * 60}
          x2={1000}
          y2={150 + i * 60 - 50}
          stroke="#5A9FE9"
          strokeWidth={1}
        />
      ))}

      {/* Z-axis indicator */}
      <line
        x1={150} y1={700}
        x2={250} y2={500}
        stroke="#5A9FE9"
        strokeWidth={2}
      />
    </svg>
  );
};
```

### Easing

- Grid fade-in: `easeOutCubic`
- Position updates: Linear (real-time tracking feel)
- Label fade-in: `easeOutCubic`

## Narration Sync

> "In 3D printing, there's no mold. The machine must know exactly where to place every single point of material. The specification must be extremely precise."

The word "exactly" lands as coordinates update. "Every single point" emphasized by visible coordinate tracking.

## Audio Notes

- Mechanical printer sounds from video
- Subtle digital "ping" on coordinate updates (optional)
- Building sense of complexity and precision

## Visual Style Notes

- Grid should enhance, not obscure the video
- Coordinate numbers should be readable but not dominant
- Technical, precise aesthetic
- Blue color ties to "specification" color palette

## Transition

Cuts to Section 4.3 focusing on the injection mold side with wall highlights.
