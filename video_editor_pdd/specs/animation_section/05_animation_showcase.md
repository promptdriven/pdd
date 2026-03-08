[Remotion]

# Section 1.5: Animation Showcase — Bouncing Elements

**Tool:** Remotion
**Duration:** ~2.5s (75 frames)
**Timestamp:** 0:05 - 0:08

## Visual Description
A grid of geometric shapes (circles, squares, triangles) bounces into view one-by-one in a cascading wave pattern, demonstrating the variety of Remotion animation primitives. Each shape lands with a squash-and-stretch effect. Once all shapes have landed, they briefly pulse in unison with a synchronized color shift, then settle into their final positions. The layout is a 4x3 grid of shapes, creating a playful mosaic.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (slate-950)
- No grid lines

### Chart/Visual Elements
- **Grid layout:** 4 columns x 3 rows, centered on canvas, cell size 160x160px, gap 40px
- **Shape palette (12 total):**
  - Row 1: Circle #38BDF8, Square #22C55E, Triangle #A78BFA, Circle #F472B6
  - Row 2: Square #FACC15, Triangle #38BDF8, Circle #22C55E, Square #A78BFA
  - Row 3: Triangle #F472B6, Circle #FACC15, Square #38BDF8, Triangle #22C55E
- **Shape sizes:** Circles 64px diameter, Squares 56px, Triangles 64px base
- **Shadow:** Each shape: `0 8px 24px rgba(0, 0, 0, 0.3)`

### Animation Sequence
1. **Frame 0-45 (0-1.5s):** Shapes drop in from above with staggered timing (3-frame delay between each). Each shape falls from Y-100px above its grid position to its target Y, with a spring overshoot and squash on landing (scaleY 0.7, scaleX 1.3 → normalize)
2. **Frame 45-55 (1.5-1.83s):** All shapes settled; brief hold
3. **Frame 55-65 (1.83-2.17s):** Synchronized pulse — all shapes scale to 1.15x and shift hue by +30deg, then return
4. **Frame 65-75 (2.17-2.5s):** Hold final state with subtle idle breathing (scale 1.0 → 1.02 loop)

### Typography
- No text elements on this component

### Easing
- Shape drop: `spring({ damping: 10, stiffness: 150, mass: 0.8 })`
- Squash/stretch: `spring({ damping: 8, stiffness: 200 })`
- Synchronized pulse: `easeInOutSine`
- Idle breathing: `easeInOutSine` (looping)

## Narration Sync
> "with no Veo clips."

Plays during the tail end of Segment 2 (4.9s-6.0s). The variety of animated shapes visually reinforces "only Remotion animations" — all motion is programmatic, no video footage.

## Code Structure (Remotion)
```typescript
<Sequence from={150} durationInFrames={75}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    <ShapeGrid
      rows={3}
      cols={4}
      cellSize={160}
      gap={40}
    >
      {SHAPES.map((shape, i) => (
        <Sequence key={i} from={i * 3}>
          <BouncingShape
            type={shape.type}
            color={shape.color}
            size={shape.size}
            dropDistance={100}
          />
        </Sequence>
      ))}
    </ShapeGrid>
    <Sequence from={55}>
      <SyncPulse targets={SHAPES} scaleTo={1.15} hueShift={30} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "grid": { "rows": 3, "cols": 4, "cellSize": 160, "gap": 40 },
  "shapes": [
    { "type": "circle", "color": "#38BDF8", "size": 64 },
    { "type": "square", "color": "#22C55E", "size": 56 },
    { "type": "triangle", "color": "#A78BFA", "size": 64 },
    { "type": "circle", "color": "#F472B6", "size": 64 },
    { "type": "square", "color": "#FACC15", "size": 56 },
    { "type": "triangle", "color": "#38BDF8", "size": 64 },
    { "type": "circle", "color": "#22C55E", "size": 64 },
    { "type": "square", "color": "#A78BFA", "size": 56 },
    { "type": "triangle", "color": "#F472B6", "size": 64 },
    { "type": "circle", "color": "#FACC15", "size": 64 },
    { "type": "square", "color": "#38BDF8", "size": 56 },
    { "type": "triangle", "color": "#22C55E", "size": 64 }
  ]
}
```

---
