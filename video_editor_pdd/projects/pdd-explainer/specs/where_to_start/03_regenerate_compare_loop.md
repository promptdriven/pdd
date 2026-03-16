[Remotion]

# Section 6.3: Regenerate-Compare Loop — Circular Flow Diagram

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 22:36 - 22:44

## Visual Description
A circular flow diagram showing the PDD regeneration loop that validates prompt quality. Three nodes arranged in a triangle: "Prompt" (top), "Regenerate" (bottom-right), and "Tests" (bottom-left). Directional arrows connect them in a clockwise cycle. The loop animates step by step — prompt feeds into regeneration, regeneration produces code that runs against tests, passing tests confirm the prompt is valid. When the cycle completes, the "Prompt" node pulses with a golden glow and gains a crown-like accent, signaling it as the new source of truth. A small status badge reads "Source of Truth ✓" beside the prompt node.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Prompt Node (top center):**
  - Position: (960, 260)
  - Circle: 80px radius, stroke `#4A90D9` at 0.6 opacity, 2px, fill `#4A90D9` at 0.08
  - Icon: Document outline inside (small rectangle with lines), `#4A90D9` at 0.5 opacity
  - Label: "Prompt" — `#FFFFFF`, 18px, Inter SemiBold, centered below circle at Y=360
- **Regenerate Node (bottom-right):**
  - Position: (1200, 640)
  - Circle: 80px radius, stroke `#D9944A` at 0.6 opacity, 2px, fill `#D9944A` at 0.08
  - Icon: Gear/cog outline inside, `#D9944A` at 0.5 opacity
  - Label: "Regenerate" — `#FFFFFF`, 18px, Inter SemiBold, centered below
- **Tests Node (bottom-left):**
  - Position: (720, 640)
  - Circle: 80px radius, stroke `#5AAA6E` at 0.6 opacity, 2px, fill `#5AAA6E` at 0.08
  - Icon: Checkmark list inside, `#5AAA6E` at 0.5 opacity
  - Label: "Tests" — `#FFFFFF`, 18px, Inter SemiBold, centered below
- **Directional Arrows:** Curved paths connecting nodes clockwise
  - Prompt → Regenerate: Bezier curve, `rgba(255,255,255,0.25)`, 2px, with arrowhead
  - Regenerate → Tests: Bezier curve, same style
  - Tests → Prompt: Bezier curve, same style
- **Traveling Dot:** Small circle (6px) that follows the arrow path, `#FBBF24` at 0.8 opacity, with a 20px motion blur trail
- **Source of Truth Badge:** Appears at (1100, 230) after cycle completes
  - Rounded rectangle: `#FBBF24` at 0.15 fill, `#FBBF24` at 0.4 stroke, 1px
  - Text: "Source of Truth ✓" — `#FBBF24`, 14px, Inter Medium

### Animation Sequence
1. **Frame 0-30 (0-1s):** Three node circles draw in simultaneously (stroke draws clockwise). Icons and labels fade in
2. **Frame 30-60 (1-2s):** Arrow from Prompt → Regenerate draws along its bezier path. Traveling dot begins at Prompt node
3. **Frame 60-90 (2-3s):** Dot arrives at Regenerate node (brief pulse on arrival). Arrow from Regenerate → Tests draws
4. **Frame 90-120 (3-4s):** Dot travels to Tests node (brief pulse). Arrow from Tests → Prompt draws
5. **Frame 120-150 (4-5s):** Dot returns to Prompt node. All three arrows now visible. Prompt node receives a golden glow ring (`#FBBF24` at 0.2, expanding from 80→100px radius, then settling at 90px with breathing)
6. **Frame 150-190 (5-6.33s):** Source of Truth badge slides in from right with 20px horizontal drift. Prompt node stroke transitions from `#4A90D9` to `#FBBF24` (golden)
7. **Frame 190-240 (6.33-8s):** Hold. Prompt node glow breathes subtly (0.15→0.22→0.15 opacity). Traveling dot completes one more full cycle at reduced opacity (0.3)

### Typography
- Node Labels: Inter, 18px, semi-bold (600), `#FFFFFF`
- Badge Text: Inter, 14px, medium (500), `#FBBF24`

### Easing
- Node circle draw: `easeOut(cubic)`
- Arrow draw: `easeInOut(cubic)`
- Traveling dot: `easeInOut(quad)` along bezier path
- Node pulse on arrival: `easeOut(quad)`
- Golden glow: `easeOut(cubic)` for expansion, `easeInOut(sine)` for breathing
- Badge slide: `easeOut(cubic)`

## Narration Sync
> "When the regenerated version passes all tests, the prompt is your new source of truth for that module."

Segment: `where_to_start_001` (9.40s – 15.12s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  {/* Nodes */}
  <Sequence from={0} durationInFrames={30}>
    <CircleNode x={960} y={260} color="#4A90D9" icon="document" label="Prompt" />
    <CircleNode x={1200} y={640} color="#D9944A" icon="gear" label="Regenerate" />
    <CircleNode x={720} y={640} color="#5AAA6E" icon="checklist" label="Tests" />
  </Sequence>

  {/* Arrows + Traveling Dot */}
  <Sequence from={30} durationInFrames={30}>
    <BezierArrow from={[960,260]} to={[1200,640]} />
  </Sequence>
  <Sequence from={60} durationInFrames={30}>
    <BezierArrow from={[1200,640]} to={[720,640]} />
  </Sequence>
  <Sequence from={90} durationInFrames={30}>
    <BezierArrow from={[720,640]} to={[960,260]} />
  </Sequence>

  <Sequence from={30} durationInFrames={120}>
    <TravelingDot
      path={[[960,260],[1200,640],[720,640],[960,260]]}
      color="#FBBF24"
      radius={6}
    />
  </Sequence>

  {/* Golden Glow on Prompt */}
  <Sequence from={120} durationInFrames={30}>
    <GoldenGlow targetNode="prompt" color="#FBBF24" maxRadius={100} />
  </Sequence>

  {/* Source of Truth Badge */}
  <Sequence from={150} durationInFrames={40}>
    <Badge
      text="Source of Truth ✓"
      x={1100}
      y={230}
      color="#FBBF24"
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "nodes": [
    { "label": "Prompt", "x": 960, "y": 260, "color": "#4A90D9", "icon": "document" },
    { "label": "Regenerate", "x": 1200, "y": 640, "color": "#D9944A", "icon": "gear" },
    { "label": "Tests", "x": 720, "y": 640, "color": "#5AAA6E", "icon": "checklist" }
  ],
  "arrows": [
    { "from": [960, 260], "to": [1200, 640] },
    { "from": [1200, 640], "to": [720, 640] },
    { "from": [720, 640], "to": [960, 260] }
  ],
  "travelingDot": {
    "color": "#FBBF24",
    "radius": 6,
    "trailLength": 20
  },
  "badge": {
    "text": "Source of Truth ✓",
    "color": "#FBBF24",
    "x": 1100,
    "y": 230
  }
}
```

---
