[Remotion] Chip Design Evolution Timeline — 1980s to Automated Synthesis

# Section 2.6: HDL Evolution Timeline — From Hand-Drawing to Automated Layout

**Tool:** Remotion
**Duration:** ~25s
**Timestamp:** 2:00 - 2:25

## Visual Description
A horizontal timeline overlay that animates the evolution of chip design methodology. Three era nodes are connected by a glowing progress line. Each node contains an icon, year label, and brief descriptor. The timeline draws from left to right as the narration progresses: (1) 1980s — hand-drawn pencil icon, "Manual Layout", (2) 1985 — code brackets icon, "Verilog HDL", (3) 1990s — chip icon, "Automated Synthesis." As each node activates, it scales up with a spring bounce and emits a small radial pulse. A running annotation below the timeline reads "specification replaced manual construction" and highlights with an underline sweep at the end.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Timeline region: bottom third, 1400x280px area at (260, 700) to (1660, 980)
- Backing panel: rounded rect, rgba(15, 23, 42, 0.8), blur(10px), border-radius 16px

### Chart/Visual Elements
- Timeline track: horizontal line from x=400 to x=1520, y=810
  - Base: 3px solid #1E293B (dim)
  - Progress fill: 3px solid gradient #F97316 → #3B82F6, draws left to right
- Node 1 — "1980s":
  - Position: (400, 810)
  - Icon: pencil/drafting tool silhouette, 40x40px, #F97316
  - Year: "1980s" above, #F97316
  - Descriptor: "Manual Layout" below, #CBD5E1
  - Circle: 56px diameter, #1E293B fill, #F97316 border (3px)
- Node 2 — "1985":
  - Position: (960, 810)
  - Icon: code brackets `{ }` silhouette, 40x40px, #A855F7
  - Year: "1985" above, #A855F7
  - Descriptor: "Verilog HDL" below, #CBD5E1
  - Circle: 56px diameter, #1E293B fill, #A855F7 border (3px)
- Node 3 — "1990s+":
  - Position: (1520, 810)
  - Icon: chip/die silhouette, 40x40px, #3B82F6
  - Year: "1990s+" above, #3B82F6
  - Descriptor: "Automated Synthesis" below, #CBD5E1
  - Circle: 56px diameter, #1E293B fill, #3B82F6 border (3px)
- Conclusion text: "Specification replaced manual construction"
  - Position: centered at (960, 940)
  - Underline sweep: #3B82F6, draws left-to-right beneath text

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Backing panel fades in. Base timeline track appears.
2. **Frame 25-55 (0.83-1.83s):** Progress line draws to Node 1. Node 1 activates — circle scales 0→1 (spring), icon fades in, year/descriptor appear. Radial pulse emits from node.
3. **Frame 55-90 (1.83-3s):** Hold on Node 1.
4. **Frame 90-130 (3-4.33s):** Progress line extends to Node 2. Node 2 activates — circle scales 0→1 (spring), icon fades in, year/descriptor appear. Radial pulse.
5. **Frame 130-180 (4.33-6s):** Hold on Node 2. Node 1 dims slightly (opacity 1.0→0.7).
6. **Frame 180-220 (6-7.33s):** Progress line extends to Node 3. Node 3 activates — circle scales 0→1 (spring), icon fades in, year/descriptor appear. Radial pulse.
7. **Frame 220-280 (7.33-9.33s):** Hold. All three nodes visible. Previous nodes dimmed.
8. **Frame 280-330 (9.33-11s):** Conclusion text fades in. Underline sweep animates left-to-right.
9. **Frame 330-600 (11-20s):** Hold at final state.
10. **Frame 600-750 (20-25s):** Entire timeline fades out — opacity 1→0.

### Typography
- Year labels: Inter Bold, 22px, node color
- Descriptors: Inter Medium, 16px, #CBD5E1
- Conclusion text: Inter SemiBold, 24px, #E2E8F0
- Underline: 2px solid #3B82F6

### Easing
- Node activation: `spring({ damping: 12, stiffness: 200 })`
- Progress line draw: `easeInOutCubic`
- Radial pulse: `easeOutQuad` (opacity 0.6→0, scale 1→2, 20 frames)
- Text fade: `easeOutCubic`
- Underline sweep: `easeInOutCubic`
- Dim previous nodes: `easeOutQuad`

## Narration Sync
> "1980s — engineers hand-drew gate layouts. 1985 — Verilog HDL: describe behavior, not wires. Synopsys added verification with SAT and SMT solvers. Same revolution: specification replaced manual construction."

Node 1 activates on "1980s." Node 2 activates on "1985 — Verilog HDL." Node 3 activates on "Synopsys." Conclusion text appears on "specification replaced manual construction."

## Code Structure (Remotion)
```typescript
<Sequence from={TIMELINE_START} durationInFrames={750}>
  <AbsoluteFill>
    {/* Backing panel */}
    <BackingPanel
      bounds={{ x: 260, y: 700, w: 1400, h: 280 }}
      opacity={interpolate(frame, [0, 25, 720, 750], [0, 0.8, 0.8, 0])}
    />

    {/* Base timeline track */}
    <TimelineTrack
      from={400} to={1520} y={810}
      baseColor="#1E293B"
      progressColor={['#F97316', '#3B82F6']}
      progress={interpolate(frame, [25, 220], [0, 1], {
        extrapolateLeft: 'clamp', extrapolateRight: 'clamp'
      })}
    />

    {/* Node 1 — 1980s */}
    <Sequence from={25} durationInFrames={725}>
      <TimelineNode
        position={[400, 810]}
        icon="pencil"
        year="1980s"
        descriptor="Manual Layout"
        color="#F97316"
        scale={spring({ frame: frame - 25, fps: 30, config: { damping: 12, stiffness: 200 } })}
        opacity={interpolate(frame, [130, 180], [1, 0.7], { extrapolateRight: 'clamp' })}
      />
    </Sequence>

    {/* Node 2 — 1985 */}
    <Sequence from={90} durationInFrames={660}>
      <TimelineNode
        position={[960, 810]}
        icon="code_brackets"
        year="1985"
        descriptor="Verilog HDL"
        color="#A855F7"
        scale={spring({ frame: frame - 90, fps: 30, config: { damping: 12, stiffness: 200 } })}
        opacity={interpolate(frame, [90, 130], [1, 0.7], { extrapolateRight: 'clamp' })}
      />
    </Sequence>

    {/* Node 3 — 1990s+ */}
    <Sequence from={180} durationInFrames={570}>
      <TimelineNode
        position={[1520, 810]}
        icon="chip"
        year="1990s+"
        descriptor="Automated Synthesis"
        color="#3B82F6"
        scale={spring({ frame: frame - 180, fps: 30, config: { damping: 12, stiffness: 200 } })}
      />
    </Sequence>

    {/* Conclusion text with underline */}
    <Sequence from={280} durationInFrames={470}>
      <ConclusionText
        text="Specification replaced manual construction"
        position={[960, 940]}
        opacity={interpolate(frame, [0, 30], [0, 1], { extrapolateRight: 'clamp' })}
        underlineProgress={interpolate(frame, [20, 50], [0, 1], { extrapolateRight: 'clamp' })}
        underlineColor="#3B82F6"
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "nodes": [
    {
      "year": "1980s",
      "descriptor": "Manual Layout",
      "icon": "pencil",
      "color": "#F97316",
      "x": 400,
      "activate_frame": 25
    },
    {
      "year": "1985",
      "descriptor": "Verilog HDL",
      "icon": "code_brackets",
      "color": "#A855F7",
      "x": 960,
      "activate_frame": 90
    },
    {
      "year": "1990s+",
      "descriptor": "Automated Synthesis",
      "icon": "chip",
      "color": "#3B82F6",
      "x": 1520,
      "activate_frame": 180
    }
  ],
  "timeline_y": 810,
  "conclusion": "Specification replaced manual construction",
  "total_frames": 750,
  "fps": 30
}
```

---
