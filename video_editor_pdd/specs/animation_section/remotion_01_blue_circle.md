[Remotion] Blue Circle — Opening Animation

## Overlay Spec
- Type: animated shape
- Trigger: frame 0
- Duration: 5s
- Position: center screen

## Shape
- Geometry: circle, 200px diameter
- Fill: vibrant blue (#3B82F6)
- Stroke: none
- Shadow: 0 0 24px rgba(59, 130, 246, 0.4)

## Animation
- Appear: scale from 0 → 1 over 20 frames (ease-out)
- Pulse: scale interpolate [60, 90, 120] → [1.0, 1.15, 1.0] (ease-in-out)
- Glow: shadow opacity pulses in sync with scale (0.4 → 0.7 → 0.4)
- Hold at 1.0 scale until morph begins in Shot 2
