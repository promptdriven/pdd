[Remotion]

# Section 0.7: Code Cursor Blink — The Weight of Patches

**Tool:** Remotion
**Duration:** ~2s (48 frames @ 30fps)
**Timestamp:** 0:14 - 0:16

## Visual Description
Return to the code side. A dark-themed code editor fills the screen. A complex function is visible — roughly 40 lines — riddled with patches. Comment annotations like `// PATCH: fixed null check`, `// TODO: refactor this`, `// HOTFIX: edge case from #1247` are scattered throughout. The code has layers of fixes on top of fixes. Colors show the age of different patches: recent ones in brighter green, older ones in faded olive. A cursor blinks at line 23, inside the thicket of patched code. The screen holds for a beat — letting the viewer feel the weight of accumulated technical debt. This is the "darning" of code.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#1E1E2E` (VS Code dark theme background)
- Editor chrome: Minimal — line numbers on left, no sidebar

### Chart/Visual Elements

#### Code Editor
- Line numbers: 1-40, `#6C7086` at 0.5, monospace, left gutter (60px)
- Code text: JetBrains Mono, 14px, syntax-highlighted
- Function signature (line 1): `def process_order(order: Dict, ctx: Context) -> Result:` in standard Python highlighting
- Patch comments scattered at lines 5, 12, 18, 23, 31, 37:
  - `// PATCH: fixed null check` — `#6C7086` italic
  - `// TODO: refactor this block` — `#F9E2AF` (yellow warning)
  - `// HOTFIX: edge case #1247` — `#F38BA8` (red)
- Patch age visualization: Faint colored left-border on patched lines
  - Recent patches: `#A6E3A1` at 0.15 (green)
  - Older patches: `#A6E3A1` at 0.05 (faded green)
  - Oldest patches: `#F9E2AF` at 0.05 (faded amber)

#### Cursor
- Position: Line 23, column 4
- Style: Block cursor, `#CDD6F4` (white-blue)
- Blink: 500ms on / 500ms off (15 frames on, 15 frames off)

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Editor fades in from black. Code visible immediately — no typing animation.
2. **Frame 10-48 (0.33-1.6s):** Hold. Cursor blinks twice. The complexity and weight of the patched function sinks in.

### Typography
- Code: JetBrains Mono, 14px, standard syntax colors (Catppuccin Mocha theme)
- Line numbers: JetBrains Mono, 12px, `#6C7086` at 0.5
- Comments: JetBrains Mono, 14px, italic, `#6C7086`

### Easing
- Editor fade-in: `easeOut(quad)` over 10 frames
- Cursor blink: step function (no easing — hard on/off)

## Narration Sync
> "Code just got that cheap."

Segment: `cold_open_005`

- **14.24s**: Editor appears — cursor blinking on heavily patched function
- **15.80s**: Hold ends, transition to code regeneration

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={48}>
  <AbsoluteFill style={{ backgroundColor: '#1E1E2E' }}>
    <FadeIn duration={10}>
      <CodeEditor
        language="python"
        theme="catppuccin-mocha"
        fontSize={14}
        fontFamily="JetBrains Mono"
        code={PATCHED_FUNCTION_CODE}
        lineHighlights={[
          { lines: [5, 12], color: '#A6E3A1', opacity: 0.05 },
          { lines: [18, 31], color: '#F9E2AF', opacity: 0.05 },
          { lines: [23, 37], color: '#A6E3A1', opacity: 0.15 },
        ]}
      />
      <BlinkingCursor
        line={23} column={4}
        color="#CDD6F4"
        blinkFrames={15}
      />
    </FadeIn>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_editor",
  "language": "python",
  "theme": "catppuccin-mocha",
  "functionName": "process_order",
  "totalLines": 40,
  "patchComments": [
    { "line": 5, "text": "// PATCH: fixed null check", "age": "old" },
    { "line": 12, "text": "// TODO: refactor this block", "age": "old" },
    { "line": 18, "text": "// HOTFIX: edge case #1247", "age": "medium" },
    { "line": 23, "text": "// PATCH: handle empty list", "age": "recent" },
    { "line": 31, "text": "// PATCH: timezone fix", "age": "medium" },
    { "line": 37, "text": "// HOTFIX: race condition", "age": "recent" }
  ],
  "cursor": { "line": 23, "column": 4, "blinkMs": 500 },
  "narrationSegments": ["cold_open_005"],
  "durationSeconds": 1.6
}
```

---
