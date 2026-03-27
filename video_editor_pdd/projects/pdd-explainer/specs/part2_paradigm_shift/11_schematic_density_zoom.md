[Remotion]

# Section 2.11: Schematic Density Zoom-Out

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 2:08 - 2:22

## Visual Description

An animated zoom-out from a hand-drawn schematic. The animation starts with a few visible transistor symbols — clean, legible, hand-drawn style (thin dark lines on off-white/cream paper). As the camera pulls back, more transistors appear: hundreds, then thousands. The drawing hand (stylized) slows down, struggling to keep up. The schematic becomes impossibly dense — a solid mass of interconnected symbols that no human could navigate.

The visual uses a 3B1B-style aesthetic on a paper-textured background: clean vector lines that accumulate into overwhelming density. A small counter in the corner tracks transistor count: 100... 1,000... 10,000... 50,000.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#F5F0E8` (warm cream/paper texture)
- Grid: Faint engineering paper grid, `#E0D8C8` at 0.15

### Chart/Visual Elements

#### Schematic Elements
- Transistor symbols: SVG path, `#2D3748` stroke, 1.5px, hand-drawn style with slight wobble
- Connection wires: `#4A5568`, 1px
- Starting view: ~20 visible transistors, legible
- Final view: ~50,000 transistors visible, unreadable dense mass

#### Drawing Hand (stylized)
- Simple vector hand silhouette holding pencil: `#78909C` at 0.5
- Starts moving at normal speed, progressively slows
- Fades out at 70% through animation (overwhelmed)

#### Transistor Counter (lower-right)
- Count: JetBrains Mono, 36px, `#4A5568`
- Label: "transistors", Inter, 14px, `#94A3B8`

### Animation Sequence
1. **Frame 0-60 (0-2s):** Close-up on schematic. ~20 transistors visible. Hand drawing. Clean, legible.
2. **Frame 60-150 (2-5s):** Camera begins pulling back. Counter: 100 → 500. More symbols appear. Hand still drawing but pace unchanged.
3. **Frame 150-240 (5-8s):** Zoom continues. Counter: 500 → 5,000. Schematic thickening. Hand slowing visibly.
4. **Frame 240-330 (8-11s):** Counter: 5,000 → 25,000. Schematic is dense. Hand stops, fades out. The density is overwhelming.
5. **Frame 330-420 (11-14s):** Counter: 25,000 → 50,000+. Full zoom-out. The schematic is a solid mass of dark lines — utterly unreviewable. Hold.

### Typography
- Counter: JetBrains Mono, 36px, regular (400), `#4A5568`
- Counter label: Inter, 14px, regular (400), `#94A3B8`

### Easing
- Zoom-out: `easeInOut(cubic)` — smooth continuous pull
- Counter: `easeIn(expo)` — accelerating count
- Hand slowdown: `easeOut(cubic)` — decelerating to stop
- Hand fade: `easeIn(quad)` over 30 frames

## Narration Sync
> "When transistor counts hit tens of thousands, they couldn't keep up. So in 1985, they moved up — from schematics to Verilog."

Segment: `part2_paradigm_shift_011` (middle/tail)

- **128.0s**: Zoom-out begins — schematic at ~20 transistors
- **132.0s**: Counter climbing — "transistor counts hit tens of thousands"
- **136.0s**: Hand slowing — "they couldn't keep up"
- **139.0s**: Dense schematic — "So in 1985, they moved up"
- **142.28s** (seg 011 ends): Schematic fully dense, hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#F5F0E8' }}>
    <EngineeringGrid spacing={40} color="#E0D8C8" opacity={0.15} />

    {/* Zoomable schematic */}
    <AnimatedZoom startScale={8} endScale={0.1} easing="easeInOutCubic">
      <SchematicCanvas
        transistorCount={50000}
        strokeColor="#2D3748" wireColor="#4A5568"
        strokeWidth={1.5} style="hand-drawn"
      />
    </AnimatedZoom>

    {/* Drawing hand */}
    <Sequence from={0} durationInFrames={300}>
      <DrawingHand
        color="#78909C" opacity={0.5}
        speedCurve="decelerating"
        fadeOutStart={240} fadeOutDuration={30}
      />
    </Sequence>

    {/* Counter */}
    <Sequence from={0}>
      <ExponentialCounter
        start={20} end={50000}
        font="JetBrains Mono" size={36}
        color="#4A5568" x={1600} y={900}
        easing="easeInExpo"
      />
      <Text text="transistors" font="Inter" size={14}
        color="#94A3B8" x={1600} y={945} align="center" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "schematic_zoom",
  "chartId": "schematic_density_zoom",
  "counter": {
    "start": 20,
    "end": 50000,
    "milestones": [100, 500, 5000, 25000, 50000]
  },
  "zoom": {
    "startScale": 8,
    "endScale": 0.1,
    "easing": "easeInOutCubic"
  },
  "narrationSegments": ["part2_paradigm_shift_011"]
}
```

---
