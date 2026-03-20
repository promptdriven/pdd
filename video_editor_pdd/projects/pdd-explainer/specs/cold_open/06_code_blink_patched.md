[Remotion]

# Section 0.6: Code Blink — The Patched Function

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:21 - 0:26

## Visual Description

Return to code — the screen transitions from the sock toss to a full-screen code editor view. A single function occupies the center of the screen: `processUserInput()`, 18 lines long, visibly scarred with patch residue. Inline comments tell the story of accumulated repair: `// fixed null case`, `// workaround for #412`, `// TODO: refactor this`, `// legacy — do not touch`. The function works but groans under the weight of its history. A cursor blinks at line 1. The code is static for a beat — letting the viewer read and recognize the pattern from their own codebase. Then the cursor blinks once more, deliberately, as if asking: "...really?"

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (GitHub dark theme)
- Editor chrome: line numbers in `#484F58` at 0.5, gutter background `#0D1117`

### Chart/Visual Elements

**Code Block**
- Position: centered, x: 200-1720, y: 160-920
- Font: JetBrains Mono, 18px, line-height: 28px
- Base code color: `#C9D1D9`
- Keyword color: `#FF7B72` (return, if, const)
- String color: `#A5D6FF`
- Comment color: `#8B949E` at 0.7
- Function name: `#D2A8FF` (purple)
- Line numbers: `#484F58`, right-aligned in gutter (x: 160-190)

**Patch Scar Comments (highlighted)**
- `// fixed null case` — line 5, `#F85149` at 0.5 background highlight
- `// workaround for #412` — line 9, `#F85149` at 0.5 background highlight
- `// TODO: refactor this` — line 13, `#D29922` at 0.4 background highlight
- `// legacy — do not touch` — line 16, `#F85149` at 0.5 background highlight

**Cursor**
- Position: line 1, column 0
- Size: 2px wide, 22px tall
- Color: `#58A6FF`
- Blink rate: 530ms on / 530ms off

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Hard cut from sock toss. Editor appears instantly — no fade, no transition. The abruptness mirrors the narrative shift.
2. **Frame 10-60 (0.33-2s):** Code is fully visible. Patch scar highlights fade in sequentially with 8-frame (0.27s) staggered delay: line 5 → line 9 → line 13 → line 16. Each highlight fades from 0 → target opacity.
3. **Frame 60-120 (2-4s):** Hold. Cursor blinks. The viewer reads the code — the scars are immediately recognizable. A very subtle scan line effect scrolls vertically (1px, `#FFFFFF` at 0.02) to reinforce the "screen" feeling.
4. **Frame 120-150 (4-5s):** Cursor blinks two more deliberate times. The final blink is longer — held for 800ms instead of 530ms, as if pausing with intent.

### Typography
- Code: JetBrains Mono, 18px, `#C9D1D9`
- Comments: JetBrains Mono, 18px, `#8B949E` at 0.7
- Line numbers: JetBrains Mono, 14px, `#484F58` at 0.5

### Easing
- Highlight fade-in: `easeOut(quad)` — soft appearance
- Scan line: `linear` — steady scroll

## Narration Sync
> "Code just got that cheap."

| Segment ID | Text | Sync Point |
|---|---|---|
| `cold_open_007` | "Code just got that cheap." | Frame 10 — lands on the hard cut to code, deliberate and flat |

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  {/* Editor background */}
  <EditorChrome background="#0D1117" gutterWidth={200}>
    {/* Code block with syntax highlighting */}
    <SyntaxHighlightedCode
      code={patchedFunction}
      language="typescript"
      font="JetBrains Mono"
      fontSize={18}
      lineHeight={28}
    />

    {/* Staggered patch scar highlights */}
    <Sequence from={10} durationInFrames={50}>
      <StaggeredHighlights
        lines={[5, 9, 13, 16]}
        colors={["#F85149", "#F85149", "#D29922", "#F85149"]}
        opacities={[0.5, 0.5, 0.4, 0.5]}
        staggerFrames={8}
      />
    </Sequence>

    {/* Blinking cursor */}
    <BlinkingCursor
      line={1}
      column={0}
      color="#58A6FF"
      width={2}
      height={22}
      onMs={530}
      offMs={530}
    />

    {/* Subtle scan line */}
    <Sequence from={60} durationInFrames={90}>
      <ScanLine color="#FFFFFF" opacity={0.02} speed={1} />
    </Sequence>
  </EditorChrome>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_editor",
  "function": {
    "name": "processUserInput",
    "lineCount": 18,
    "language": "typescript",
    "code": [
      "function processUserInput(raw: string): ProcessedInput {",
      "  const sanitized = raw.trim().toLowerCase();",
      "  let result: ProcessedInput;",
      "",
      "  // fixed null case",
      "  if (!sanitized || sanitized === 'undefined') {",
      "    return { valid: false, value: '', error: 'empty input' };",
      "  }",
      "",
      "  // workaround for #412",
      "  const cleaned = sanitized.replace(/[^\\w@.\\-]/g, '');",
      "  if (cleaned !== sanitized) {",
      "    result = { valid: true, value: cleaned, warning: 'chars stripped' };",
      "  // TODO: refactor this",
      "  } else if (cleaned.length > MAX_INPUT_LENGTH) {",
      "    result = { valid: true, value: cleaned.slice(0, MAX_INPUT_LENGTH) };",
      "  // legacy — do not touch",
      "  } else { result = { valid: true, value: cleaned }; }",
      "  return result;",
      "}"
    ]
  },
  "patchScars": [
    { "line": 5, "text": "// fixed null case", "highlightColor": "#F85149", "opacity": 0.5 },
    { "line": 9, "text": "// workaround for #412", "highlightColor": "#F85149", "opacity": 0.5 },
    { "line": 13, "text": "// TODO: refactor this", "highlightColor": "#D29922", "opacity": 0.4 },
    { "line": 16, "text": "// legacy — do not touch", "highlightColor": "#F85149", "opacity": 0.5 }
  ],
  "cursor": { "line": 1, "column": 0, "color": "#58A6FF", "blinkMs": 530 },
  "narrationSegments": ["cold_open_007"]
}
```
