[split:]

# Section 3.5: Split — Traditional Bug Fix vs. PDD Bug Fix

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 13:57 - 14:11

## Visual Description
A split-screen comparison showing two approaches to the same bug. LEFT side: "Traditional" — a sequential chain where a bug is found, code is patched, a similar bug appears elsewhere, code is patched again, a different bug appears, patched again. The chain grows downward, accumulating. RIGHT side: "PDD" — a bug is found, a test is added (`pdd bug`), code is regenerated (`pdd fix`), and the bug is permanently impossible. The right side is clean and final. Below, a fork-in-the-road diagram distinguishes between code bugs (add a wall) and prompt defects (change the mold itself).

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None
- Vertical divider: 2px line at X=960, `rgba(255,255,255,0.15)`, full height

### Chart/Visual Elements
- **LEFT Header:** "Traditional" — `#FFFFFF`, 28px bold, centered at X=480, Y=60
- **RIGHT Header:** "PDD" — `#FFFFFF`, 28px bold, centered at X=1440, Y=60
- **LEFT Chain (sequential patches):**
  - Step 1: "Bug found" — red circle icon `#EF4444`, label 16px white, Y=140
  - Step 2: "Patch code" → green-ish box `rgba(34,197,94,0.3)`, Y=220
  - Arrow down (dashed, `rgba(255,255,255,0.3)`)
  - Step 3: "Similar bug elsewhere" — red circle, Y=310
  - Step 4: "Patch again" → yellow-ish box `rgba(245,158,11,0.3)`, Y=390
  - Arrow down
  - Step 5: "Different bug" — red circle, Y=480
  - Step 6: "Patch again..." → orange box `rgba(239,68,68,0.2)`, Y=560
  - Trailing ellipsis dots, suggesting infinite continuation
  - Overall: chain tints progressively warmer/redder, implying accumulating fragility
- **RIGHT Chain (PDD approach):**
  - Step 1: "Bug found" — red circle icon `#EF4444`, Y=140
  - Step 2: "Add test" → amber wall icon `#D9944A`, label: `pdd bug`, Y=260
  - Step 3: "Regenerate" → blue pulse icon `#4A90D9`, label: `pdd fix`, Y=380
  - Step 4: "Bug impossible forever" — green checkmark `#22C55E`, with permanent glow, Y=500
  - Clean, final. No continuation. The chain ends.
- **Fork Diagram (bottom third, centered):**
  - Starting node: "Bug found" — white circle, centered at X=960, Y=750
  - LEFT branch: "Code bug → add a wall" — arrow to amber wall icon, X=660, Y=850
  - RIGHT branch: "Prompt defect → change the mold" — arrow to blue document icon, X=1260, Y=850

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Divider line draws top-to-bottom. Headers fade in
2. **Frame 20-80 (0.67-2.67s):** LEFT: Steps 1-2 animate in sequence (bug circle pulses, patch box slides in). RIGHT: Step 1 animates in simultaneously
3. **Frame 80-140 (2.67-4.67s):** LEFT: Steps 3-4 animate (arrow draws, second bug, second patch). RIGHT: Step 2 — amber wall materializes with "pdd bug" label
4. **Frame 140-200 (4.67-6.67s):** LEFT: Steps 5-6 animate (third bug, third patch, ellipsis). Chain visibly accumulating weight. RIGHT: Step 3 — blue regeneration pulse
5. **Frame 200-260 (6.67-8.67s):** RIGHT: Step 4 — green checkmark scales in with glow. "Bug impossible forever" text. The RIGHT side is done. The LEFT side's ellipsis continues to pulse, suggesting it never ends
6. **Frame 260-340 (8.67-11.33s):** Fork diagram fades in at bottom. Starting node appears, then branches animate left and right simultaneously. Amber wall icon and blue document icon pulse at their endpoints
7. **Frame 340-420 (11.33-14.0s):** Hold. LEFT chain pulses faintly with accumulated red tint. RIGHT side glows clean green. Fork diagram steady

### Typography
- Headers: Inter, 28px, bold (700), `#FFFFFF`
- Step Labels: Inter, 16px, regular (400), `#FFFFFF` at 0.9 opacity
- Command Labels: JetBrains Mono, 14px, regular (400), `#94A3B8`
- Fork Labels: Inter, 16px, semi-bold (600), respective colors
- "Bug impossible forever": Inter, 18px, bold (700), `#22C55E`

### Easing
- Divider draw: `easeOut(cubic)`
- Bug circles: `easeOut(back(1.3))`
- Patch boxes: `easeOut(quad)`
- Arrows: `linear` draw
- Green checkmark: `easeOut(back(1.5))`
- Fork branches: `easeOut(cubic)`

## Narration Sync
> "In traditional development, a bug fix helps one place. In PDD, a test prevents that bug everywhere, forever."
> "And sometimes the bug isn't in the code — it's in the prompt. The code correctly implements a wrong specification. PDD distinguishes between these. A code bug? Add a wall. A prompt defect? Change the mold itself."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  {/* Divider and Headers */}
  <Sequence from={0} durationInFrames={20}>
    <VerticalDivider x={960} />
    <SplitHeaders left="Traditional" right="PDD" />
  </Sequence>

  {/* LEFT: Traditional chain */}
  <Sequence from={20} durationInFrames={180}>
    <TraditionalChain
      steps={[
        { type: "bug", label: "Bug found" },
        { type: "patch", label: "Patch code" },
        { type: "bug", label: "Similar bug elsewhere" },
        { type: "patch", label: "Patch again" },
        { type: "bug", label: "Different bug" },
        { type: "patch", label: "Patch again..." }
      ]}
      stagger={30}
    />
  </Sequence>

  {/* RIGHT: PDD chain */}
  <Sequence from={20} durationInFrames={240}>
    <PDDChain
      steps={[
        { type: "bug", label: "Bug found", frame: 0 },
        { type: "wall", label: "Add test", cmd: "pdd bug", frame: 60 },
        { type: "regen", label: "Regenerate", cmd: "pdd fix", frame: 120 },
        { type: "done", label: "Bug impossible forever", frame: 180 }
      ]}
    />
  </Sequence>

  {/* Fork Diagram */}
  <Sequence from={260} durationInFrames={80}>
    <ForkDiagram
      startLabel="Bug found"
      leftBranch={{ label: "Code bug → add a wall", icon: "wall", color: "#D9944A" }}
      rightBranch={{ label: "Prompt defect → change the mold", icon: "document", color: "#4A90D9" }}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "dividerColor": "rgba(255,255,255,0.15)",
  "traditional": {
    "header": "Traditional",
    "steps": [
      { "type": "bug", "label": "Bug found" },
      { "type": "patch", "label": "Patch code" },
      { "type": "bug", "label": "Similar bug elsewhere" },
      { "type": "patch", "label": "Patch again" },
      { "type": "bug", "label": "Different bug" },
      { "type": "patch", "label": "Patch again..." }
    ]
  },
  "pdd": {
    "header": "PDD",
    "steps": [
      { "type": "bug", "label": "Bug found" },
      { "type": "wall", "label": "Add test", "command": "pdd bug" },
      { "type": "regen", "label": "Regenerate", "command": "pdd fix" },
      { "type": "done", "label": "Bug impossible forever" }
    ]
  },
  "fork": {
    "codeBug": { "label": "Code bug → add a wall", "color": "#D9944A" },
    "promptDefect": { "label": "Prompt defect → change the mold", "color": "#4A90D9" }
  }
}
```

---
