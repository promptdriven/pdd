[Remotion]

# Section 3.8: Fork in the Road — Code Bug vs. Prompt Defect

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 2:26 - 2:44

## Visual Description

A fork-in-the-road diagram. At the top, a starting node: "Bug found" in a red-bordered box. Two branches diverge downward:

**LEFT branch** — "Code bug — add a wall." The branch is blue (test color). It leads to a wall segment being added to the mold. Below, the liquid regenerates and conforms. This is the familiar flow from earlier shots.

**RIGHT branch** — "Prompt defect — change the mold itself." The branch is amber (prompt color). It leads to the nozzle/prompt region of the mold being modified. The entire mold shape changes subtly — the specification was wrong, so the mold itself needs reshaping.

Both branches resolve cleanly, but the distinction is critical: PDD separates code failures from specification failures.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Starting Node
- "Bug found" — 200px × 50px box, `#1E1E2E` fill, `#EF4444` border 2px, rounded 8px
- Text: Inter, 16px, bold (700), `#EF4444`
- Position: centered at (960, 180)

#### Fork Lines
- Two diagonal lines diverging from the starting node
- Left line: `#4A90D9` (blue), 2px, to (480, 360)
- Right line: `#D9944A` (amber), 2px, to (1440, 360)

#### Left Branch — Code Bug
- Node: "Code bug" — 180px × 45px, `#1E1E2E` fill, `#4A90D9` border 2px
- Text: Inter, 14px, semi-bold (600), `#4A90D9`
- Action: "Add a wall" — Inter, 14px, regular (400), `#94A3B8`
- Below: small mold icon showing a new wall being added
- Arrow down to resolution: `#4A90D9` at 0.3

#### Right Branch — Prompt Defect
- Node: "Prompt defect" — 200px × 45px, `#1E1E2E` fill, `#D9944A` border 2px
- Text: Inter, 14px, semi-bold (600), `#D9944A`
- Action: "Change the mold itself" — Inter, 14px, regular (400), `#94A3B8`
- Below: small mold icon showing the nozzle/prompt region being reshaped
- Arrow down to resolution: `#D9944A` at 0.3

### Animation Sequence
1. **Frame 0-30 (0-1s):** "Bug found" node fades in at top center.
2. **Frame 30-60 (1-2s):** Fork lines draw downward and outward, diverging left and right.
3. **Frame 60-120 (2-4s):** LEFT: "Code bug" node fades in. "Add a wall" text appears below. Small mold icon shows wall addition.
4. **Frame 120-180 (4-6s):** RIGHT: "Prompt defect" node fades in. "Change the mold itself" text appears below. Small mold icon shows prompt reshaping.
5. **Frame 180-270 (6-9s):** Both branches animate their mini-mold icons. LEFT: wall slides into mold. RIGHT: nozzle shape morphs.
6. **Frame 270-420 (9-14s):** Hold. Both paths visible. The distinction is clear.
7. **Frame 420-540 (14-18s):** Fade hold, transition readiness.

### Typography
- Starting node: Inter, 16px, bold (700), `#EF4444`
- Branch nodes: Inter, 14px, semi-bold (600), matching branch color
- Action text: Inter, 14px, regular (400), `#94A3B8`

### Easing
- Node fade-in: `easeOut(quad)` over 20 frames
- Fork lines draw: `easeInOut(cubic)` over 30 frames
- Mini-mold animations: `easeOut(back)` over 25 frames
- Action text: `easeOut(quad)` over 15 frames

## Narration Sync
> "And sometimes the bug isn't in the code — it's in the prompt. The code correctly implements a wrong specification. PDD distinguishes between these. A code bug? Add a wall. A prompt defect? Change the mold itself."

Segment: `part3_mold_parts_012`

- **145.72s** (seg 012): "Bug found" node appears
- **149.0s**: Fork lines diverge — "it's in the prompt"
- **154.0s**: Left branch — "A code bug? Add a wall."
- **158.0s**: Right branch — "A prompt defect? Change the mold itself."
- **163.94s** (seg 012 ends): Both branches visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Starting node */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <FlowNode text="Bug found" borderColor="#EF4444"
          textColor="#EF4444" x={960} y={180}
          width={200} height={50} />
      </FadeIn>
    </Sequence>

    {/* Fork lines */}
    <Sequence from={30}>
      <DrawLine from={[960, 205]} to={[480, 360]}
        color="#4A90D9" width={2} drawDuration={30} />
      <DrawLine from={[960, 205]} to={[1440, 360]}
        color="#D9944A" width={2} drawDuration={30} />
    </Sequence>

    {/* Left: Code bug */}
    <Sequence from={60}>
      <FadeIn duration={20}>
        <FlowNode text="Code bug" borderColor="#4A90D9"
          textColor="#4A90D9" x={480} y={380} />
      </FadeIn>
      <Sequence from={20}>
        <FadeIn duration={15}>
          <Text text="Add a wall" color="#94A3B8"
            font="Inter" size={14} x={480} y={440} />
        </FadeIn>
      </Sequence>
      <Sequence from={120}>
        <MiniMold action="addWall" x={480} y={540}
          wallColor="#4A90D9" />
      </Sequence>
    </Sequence>

    {/* Right: Prompt defect */}
    <Sequence from={120}>
      <FadeIn duration={20}>
        <FlowNode text="Prompt defect" borderColor="#D9944A"
          textColor="#D9944A" x={1440} y={380} />
      </FadeIn>
      <Sequence from={20}>
        <FadeIn duration={15}>
          <Text text="Change the mold itself" color="#94A3B8"
            font="Inter" size={14} x={1440} y={440} />
        </FadeIn>
      </Sequence>
      <Sequence from={60}>
        <MiniMold action="reshapeNozzle" x={1440} y={540}
          nozzleColor="#D9944A" />
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "fork_diagram",
  "root": { "label": "Bug found", "color": "#EF4444" },
  "branches": [
    { "label": "Code bug", "action": "Add a wall", "color": "#4A90D9", "side": "left" },
    { "label": "Prompt defect", "action": "Change the mold itself", "color": "#D9944A", "side": "right" }
  ],
  "narrationSegments": ["part3_mold_parts_012"],
  "durationSeconds": 18.0
}
```

---
