[Remotion]

# Section 3.6: Bug Found — Add a Wall, Not a Patch

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 1:02 - 1:20

## Visual Description

A code editor panel sits on the left half of the screen. A red "BUG" alert flashes on a highlighted line. Instead of the code being patched, the scene transitions to the mold view: a new wall materializes inside the mold, labeled with the bug condition. In the lower-right corner, a subtle terminal shows `pdd bug user_parser` running, outputting "Creating failing test..."

Then the mold regenerates: the code in the editor is replaced entirely. The new code is different but passes all tests. Terminal shows `pdd fix user_parser → "All tests passing"`. The wall that was just added glows — it's permanent. That bug can never recur.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Code Editor Panel (Left)
- Position: x: 60, y: 100, width: 800, height: 600
- Background: `#1E1E2E` (VS Code dark), rounded 8px
- Code lines: JetBrains Mono, 12px, syntax-highlighted
- Bug line: highlighted with `#EF4444` at 0.15 background, line 14
- "BUG" badge: `#EF4444` background, white text, 10px, bold, top-right of highlighted line

#### Mold View (Right)
- Position: x: 920, y: 100, width: 900, height: 600
- Mold cross-section at smaller scale, walls visible
- New wall: materializes with amber glow `#D9944A`, labeled with bug condition

#### Terminal Overlay
- Position: x: 920, y: 740, width: 500, height: 200
- Background: `#0D1117` (terminal dark), rounded 6px
- Prompt: `$` in `#4ADE80`, command in `#E2E8F0`
- Output: `#94A3B8` at 0.7

### Animation Sequence
1. **Frame 0-60 (0-2s):** Code editor visible. A line highlights red. "BUG" badge appears with a pulse.
2. **Frame 60-120 (2-4s):** Camera zooms slightly. The bug line is emphasized. Terminal shows: `$ pdd bug user_parser`.
3. **Frame 120-210 (4-7s):** In the mold view, a new wall materializes — it grows from nothing, solidifies, and gets labeled with the bug condition. Terminal: "Creating failing test... ✓"
4. **Frame 210-330 (7-11s):** The code in the editor dissolves (particle effect). New code regenerates line by line. Terminal: `$ pdd fix user_parser`.
5. **Frame 330-420 (11-14s):** New code fully visible. All test checkmarks appear. Terminal: "All tests passing ✓". The new wall glows permanently.
6. **Frame 420-540 (14-18s):** Label appears: "That wall is permanent. That bug can never occur again." Wall continues to glow.

### Typography
- Code: JetBrains Mono, 12px, syntax-highlighted
- Bug badge: Inter, 10px, bold, `#FFFFFF` on `#EF4444`
- Wall label: JetBrains Mono, 11px, `#D9944A` at 0.8
- Terminal: JetBrains Mono, 11px, `#E2E8F0`
- Bottom label: Inter, 16px, `#D9944A` at 0.7, centered

### Easing
- Bug highlight: `easeOut(expo)` over 10 frames — sharp flash
- New wall materialize: `easeOut(back)` over 30 frames — slight spring
- Code dissolve: `easeIn(quad)` over 30 frames
- Code regenerate: stagger 2 frames per line, `easeOut(quad)`
- Wall glow: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "Now watch what happens when you find a bug..."
> "...you don't patch the code. You add a wall."
> "That wall is permanent. That bug can never occur again — not in this generation, not in any future generation."

Segments: `part3_mold_has_three_parts_009`, `part3_mold_has_three_parts_010`, `part3_mold_has_three_parts_011`

- **1:02** ("watch what happens"): Bug highlight flashes on code
- **1:06** ("don't patch the code"): New wall materializes in mold
- **1:10** ("wall is permanent"): Code regenerates, wall glows

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.05} />

    {/* Code editor panel */}
    <CodeEditor
      x={60} y={100} width={800} height={600}
      bg="#1E1E2E" font="JetBrains Mono" fontSize={12}>
      <Sequence from={0}>
        <BugHighlight line={14} color="#EF4444" badgeText="BUG"
          flashDuration={10} />
      </Sequence>
      <Sequence from={210}>
        <CodeDissolve duration={30} />
      </Sequence>
      <Sequence from={240}>
        <CodeRegenerate lines={NEW_CODE} stagger={2} />
      </Sequence>
    </CodeEditor>

    {/* Mold view */}
    <MoldView x={920} y={100} width={900} height={600}>
      <Sequence from={120}>
        <NewWall
          label="handles_null_userid"
          color="#D9944A"
          materializeDuration={30}
          easing="easeOut(back)" />
      </Sequence>
    </MoldView>

    {/* Terminal */}
    <Sequence from={60}>
      <TerminalPanel x={920} y={740} width={500} height={200}>
        <TypeCommand delay={0} command="pdd bug user_parser" />
        <TypeOutput delay={60} text="Creating failing test... ✓" />
        <TypeCommand delay={150} command="pdd fix user_parser" />
        <TypeOutput delay={270} text="All tests passing ✓" color="#4ADE80" />
      </TerminalPanel>
    </Sequence>

    {/* Bottom label */}
    <Sequence from={420}>
      <FadeIn duration={20}>
        <Text text="That wall is permanent. That bug can never occur again."
          font="Inter" size={16} color="#D9944A" opacity={0.7}
          x={960} y={960} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "bug_add_wall",
  "phases": [
    { "id": "bug_found", "action": "highlight_bug_line", "color": "#EF4444" },
    { "id": "add_wall", "action": "materialize_wall", "label": "handles_null_userid", "color": "#D9944A" },
    { "id": "regenerate", "action": "dissolve_and_regenerate_code" },
    { "id": "permanent", "action": "wall_glows_permanently" }
  ],
  "terminalCommands": ["pdd bug user_parser", "pdd fix user_parser"],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_has_three_parts_009", "part3_mold_has_three_parts_010", "part3_mold_has_three_parts_011"]
}
```

---
