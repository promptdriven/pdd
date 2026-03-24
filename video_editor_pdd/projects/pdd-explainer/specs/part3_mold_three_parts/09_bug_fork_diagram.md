[Remotion]

# Section 3.9: Bug Fork — Code Bug vs Prompt Defect

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 2:24 - 2:36

## Visual Description

A fork-in-the-road diagram. At the top center, a node labeled "Bug found" with a red alert icon. Two branches diverge downward-left and downward-right:

**LEFT branch — "Code bug → add a wall":** The path leads to a mold wall being added. Color: amber `#D9944A`. The wall materializes. A test file icon glows. Label: "Add a test."

**RIGHT branch — "Prompt defect → change the mold itself":** The path leads to the prompt/nozzle region being modified. Color: teal `#2DD4BF`. The nozzle shape subtly reshapes. A `.prompt` file icon glows. Label: "Fix the specification."

The fork makes the distinction visual: PDD separates code bugs (wrong implementation) from prompt defects (wrong specification). Both paths lead to a regeneration step at the bottom.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Root Node
- Position: centered at (960, 150)
- Circle: 60px radius, stroke `#EF4444` at 0.5, fill `#1E1015` at 0.3
- Text: "Bug found" — Inter, 16px, bold, `#EF4444`
- Warning icon: 20px, `#EF4444`, above text

#### Left Branch — Code Bug
- Branch line: curved from (960, 210) to (400, 500), 2px, `#D9944A` at 0.4
- Node at (400, 500): rounded rect 250×80px, border `#D9944A` at 0.5, fill `#1A1508` at 0.3
- Text: "Code bug — add a wall" — Inter, 14px, bold, `#D9944A`
- Below: mold wall icon materializing, 80×40px, `#D9944A` at 0.6
- File icon: `test_user_parser.py`, `#D9944A` at 0.4

#### Right Branch — Prompt Defect
- Branch line: curved from (960, 210) to (1520, 500), 2px, `#2DD4BF` at 0.4
- Node at (1520, 500): rounded rect 250×80px, border `#2DD4BF` at 0.5, fill `#081A1A` at 0.3
- Text: "Prompt defect — change the mold" — Inter, 14px, bold, `#2DD4BF`
- Below: nozzle shape reshaping, 80×40px, `#2DD4BF` at 0.6
- File icon: `user_parser.prompt`, `#2DD4BF` at 0.4

#### Convergence Node
- Position: centered at (960, 780)
- Rounded rect: 200×60px, border `#4ADE80` at 0.4, fill `#0F1E15` at 0.3
- Text: "Regenerate" — Inter, 16px, bold, `#4ADE80`
- Both branches converge here

### Animation Sequence
1. **Frame 0-45 (0-1.5s):** Root node "Bug found" appears with red pulse.
2. **Frame 45-120 (1.5-4s):** Left branch draws. "Code bug — add a wall" node appears. Wall icon materializes.
3. **Frame 120-210 (4-7s):** Right branch draws. "Prompt defect — change the mold" node appears. Nozzle reshapes.
4. **Frame 210-280 (7-9.33s):** Both branches converge to "Regenerate" node at bottom.
5. **Frame 280-360 (9.33-12s):** Hold. Both paths glow. The distinction is clear.

### Typography
- Root node: Inter, 16px, bold (700), `#EF4444`
- Branch labels: Inter, 14px, bold (700), respective branch color
- File names: JetBrains Mono, 11px, respective branch color at 0.4
- Convergence: Inter, 16px, bold (700), `#4ADE80`

### Easing
- Root appear: `easeOut(expo)` over 15 frames
- Branch draw: `easeInOut(cubic)` over 40 frames
- Node appear: `easeOut(back)` over 20 frames
- Wall materialize: `easeOut(back)` over 15 frames
- Nozzle reshape: `easeInOut(cubic)` over 20 frames
- Convergence appear: `easeOut(quad)` over 20 frames

## Narration Sync
> "And sometimes the bug isn't in the code — it's in the prompt. The code correctly implements a wrong specification. PDD distinguishes between these. A code bug? Add a wall. A prompt defect? Change the mold itself."

Segment: `part3_mold_three_parts_016`

- **2:24** ("sometimes the bug isn't in the code"): Root node appears
- **2:28** ("PDD distinguishes"): Both branches visible
- **2:33** ("code bug? Add a wall"): Left branch highlights, then right branch

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.05} />

    {/* Root node */}
    <Sequence from={0}>
      <ForkNode x={960} y={150} label="Bug found"
        icon="warning" color="#EF4444"
        radius={60} pulseDuration={15} />
    </Sequence>

    {/* Left branch: Code bug */}
    <Sequence from={45}>
      <CurvedBranch from={[960, 210]} to={[400, 500]}
        color="#D9944A" opacity={0.4} drawDuration={40} />
      <Sequence from={40}>
        <BranchNode x={400} y={500}
          label="Code bug — add a wall" color="#D9944A"
          icon="wall" fileLabel="test_user_parser.py" />
      </Sequence>
    </Sequence>

    {/* Right branch: Prompt defect */}
    <Sequence from={120}>
      <CurvedBranch from={[960, 210]} to={[1520, 500]}
        color="#2DD4BF" opacity={0.4} drawDuration={40} />
      <Sequence from={40}>
        <BranchNode x={1520} y={500}
          label="Prompt defect — change the mold" color="#2DD4BF"
          icon="nozzle" fileLabel="user_parser.prompt" />
      </Sequence>
    </Sequence>

    {/* Convergence */}
    <Sequence from={210}>
      <CurvedBranch from={[400, 580]} to={[960, 780]} color="#4ADE80" opacity={0.3} drawDuration={30} />
      <CurvedBranch from={[1520, 580]} to={[960, 780]} color="#4ADE80" opacity={0.3} drawDuration={30} />
      <Sequence from={40}>
        <ForkNode x={960} y={780} label="Regenerate"
          color="#4ADE80" radius={30} />
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "bug_fork",
  "root": { "label": "Bug found", "color": "#EF4444" },
  "branches": [
    {
      "id": "code_bug",
      "label": "Code bug — add a wall",
      "color": "#D9944A",
      "action": "add_test",
      "file": "test_user_parser.py"
    },
    {
      "id": "prompt_defect",
      "label": "Prompt defect — change the mold",
      "color": "#2DD4BF",
      "action": "fix_specification",
      "file": "user_parser.prompt"
    }
  ],
  "convergence": { "label": "Regenerate", "color": "#4ADE80" },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_three_parts_016"]
}
```

---
