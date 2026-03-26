[Remotion]

# Section 3.9: Bug Fork — Code Bug vs Prompt Defect

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 1:52 - 2:06

## Visual Description

A fork-in-the-road diagram. At the top center, a node labeled "Bug found" with a red alert icon. Two diverging paths branch downward:

**LEFT branch — "Code bug → add a wall."** The path curves left, colored amber. It leads to a mold with a new wall being added. Label: "The code didn't meet the spec." Below: a test icon and the text "Add a failing test."

**RIGHT branch — "Prompt defect → change the mold itself."** The path curves right, colored teal. It leads to a prompt file being edited. Label: "The spec was wrong." Below: a file-edit icon and the text "Modify the prompt."

The fork makes PDD's diagnostic precision clear: not all bugs are equal. The system distinguishes between implementation errors and specification errors.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Root Node
- "Bug found" — Inter, 18px, bold, `#EF4444` at 0.8, centered at (960, 120)
- Red alert icon: 24px, `#EF4444` at 0.6
- Circle background: 80px diameter, `#1E1015`, border `#EF4444` at 0.3

#### Left Branch — Code Bug
- Curved path from root to (400, 500), 2px, `#D9944A` at 0.4
- Destination node: "Code bug" — Inter, 16px, bold, `#D9944A`
- Sub-label: "The code didn't meet the spec" — Inter, 12px, `#94A3B8` at 0.5
- Action: "Add a wall (failing test)" — Inter, 14px, `#D9944A` at 0.7
- Icon: mold wall icon, 40px, `#D9944A` at 0.4

#### Right Branch — Prompt Defect
- Curved path from root to (1520, 500), 2px, `#2DD4BF` at 0.4
- Destination node: "Prompt defect" — Inter, 16px, bold, `#2DD4BF`
- Sub-label: "The spec was wrong" — Inter, 12px, `#94A3B8` at 0.5
- Action: "Change the mold itself" — Inter, 14px, `#2DD4BF` at 0.7
- Icon: file-edit icon, 40px, `#2DD4BF` at 0.4

#### Decision Point Labels
- Left arrow label: "Code doesn't pass tests" — Inter, 11px, `#D9944A` at 0.4
- Right arrow label: "Code passes tests, wrong behavior" — Inter, 11px, `#2DD4BF` at 0.4

### Animation Sequence
1. **Frame 0-60 (0-2s):** Root "Bug found" node appears with alert flash.
2. **Frame 60-120 (2-4s):** Fork paths begin drawing — left amber, right teal. Simultaneous.
3. **Frame 120-210 (4-7s):** Left destination appears: "Code bug" node, sub-label, action.
4. **Frame 210-300 (7-10s):** Right destination appears: "Prompt defect" node, sub-label, action.
5. **Frame 300-360 (10-12s):** Decision point labels fade in along the paths.
6. **Frame 360-420 (12-14s):** Hold. Both branches complete. Subtle pulse on both destination nodes.

### Typography
- Root: Inter, 18px, bold (700), `#EF4444`
- Branch labels: Inter, 16px, bold (700), respective colors
- Sub-labels: Inter, 12px, `#94A3B8` at 0.5
- Actions: Inter, 14px, respective colors at 0.7
- Path labels: Inter, 11px, respective colors at 0.4

### Easing
- Root appear: `easeOut(back)` over 20 frames
- Path draw: `easeInOut(cubic)` over 40 frames
- Destination nodes: `easeOut(cubic)` over 20 frames
- Labels fade: `easeOut(quad)` over 15 frames
- Destination pulse: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "And sometimes the bug isn't in the code — it's in the prompt. The code correctly implements a wrong specification. PDD distinguishes between these. A code bug? Add a wall. A prompt defect? Change the mold itself."

Segment: `part3_mold_has_three_parts_014`

- **1:52** ("sometimes the bug isn't in the code"): Root node appears, fork begins
- **1:58** ("code bug? Add a wall"): Left branch completes
- **2:02** ("prompt defect? Change the mold"): Right branch completes

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.03} />

    {/* Root node */}
    <Sequence from={0}>
      <ForkNode x={960} y={120}
        text="Bug found" icon="alert"
        color="#EF4444" bg="#1E1015" />
    </Sequence>

    {/* Fork paths */}
    <Sequence from={60}>
      <CurvedPath from={[960, 160]} to={[400, 440]}
        color="#D9944A" opacity={0.4} width={2}
        drawDuration={40} />
      <CurvedPath from={[960, 160]} to={[1520, 440]}
        color="#2DD4BF" opacity={0.4} width={2}
        drawDuration={40} />
    </Sequence>

    {/* Left: Code bug */}
    <Sequence from={120}>
      <ForkNode x={400} y={500}
        text="Code bug" subtext="The code didn't meet the spec"
        action="Add a wall (failing test)"
        color="#D9944A" icon="wall" />
    </Sequence>

    {/* Right: Prompt defect */}
    <Sequence from={210}>
      <ForkNode x={1520} y={500}
        text="Prompt defect" subtext="The spec was wrong"
        action="Change the mold itself"
        color="#2DD4BF" icon="file_edit" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "bug_fork_diagram",
  "root": { "text": "Bug found", "color": "#EF4444" },
  "branches": [
    {
      "id": "code_bug",
      "label": "Code bug",
      "action": "Add a wall (failing test)",
      "color": "#D9944A",
      "condition": "Code doesn't pass tests"
    },
    {
      "id": "prompt_defect",
      "label": "Prompt defect",
      "action": "Change the mold itself",
      "color": "#2DD4BF",
      "condition": "Code passes tests, wrong behavior"
    }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_has_three_parts_014"]
}
```

---
