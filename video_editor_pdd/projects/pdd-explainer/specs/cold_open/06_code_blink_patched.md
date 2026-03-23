[Remotion]

# Section 0.6: Code Blink Patched — The Weight of Legacy

**Tool:** Remotion
**Duration:** ~1.7s (52 frames @ 30fps)
**Timestamp:** 0:14 - 0:16

## Visual Description

Return to the code side. A single code editor fills the screen — dark IDE theme, the same `#0D1117` background from earlier. The cursor blinks on a complex function that's clearly been patched many times. The function is `processUserData()` — 45 lines long, with visible band-aid comments: `// patched for edge case #247`, `// TODO: this shouldn't be here`, `// workaround for legacy API`. Highlighted diff markers show layers of changes over time.

The shot is held and still. No animation except the cursor blink. The viewer sits with the weight of accumulated patches. After the sock toss's bright energy, the return to the dark IDE is sobering — this is the code equivalent of the grandmother's mending drawer, but without the love.

This is a "breath" beat — quiet, contemplative, setting up the delete+regenerate payoff that follows.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (IDE dark background)
- Grid lines: None

### Chart/Visual Elements

#### Editor Chrome
- Title bar: `#161B22`, with window controls (red/yellow/green dots, dimmed)
- File tab: `UserService.ts` — Inter, 11px, `#E2E8F0` at 0.7, with amber dot (modified)
- Line numbers: JetBrains Mono, 11px, `#6E7681` at 0.4, right-aligned, lines 127-171

#### Code Content
- Font: JetBrains Mono, 13px
- Function signature: `async function processUserData(input: UserInput): Promise<Result>` — keywords `#FF7B72`, types `#79C0FF`, function name `#D2A8FF`
- Function body: 45 lines of TypeScript with realistic syntax highlighting
- Patch comments (highlighted with `#D9944A` at 0.08 background):
  - Line 131: `// patched for edge case #247` — `#6E7681` italic
  - Line 139: `// TODO: this shouldn't be here` — `#E74C3C` at 0.6
  - Line 145: `// workaround for legacy API` — `#6E7681` italic
  - Line 152: `// HACK: don't ask` — `#E74C3C` at 0.5
  - Line 158: `// temporary fix, see ticket PD-1892` — `#6E7681` italic

#### Cursor
- Position: end of line 145, after the workaround comment
- Blink: 530ms on / 530ms off (standard VS Code cursor rate)
- Color: `#E2E8F0` at 0.8, 2px wide

#### Subtle Indicators
- Git gutter: thin green/amber/red bars in the gutter — `#5AAA6E`, `#D9944A`, `#E74C3C` at 0.3, 3px wide
  - Most lines show amber (modified) — the function is heavily edited

### Animation Sequence
1. **Frame 0-5 (0-0.17s):** Hard cut from sock toss. Full IDE view appears instantly.
2. **Frame 5-52 (0.17-1.7s):** Hold. Only the cursor blinks (16-frame on, 16-frame off cycle). Nothing else moves. The stillness is the point.

### Typography
- Code: JetBrains Mono, 13px, VS Code Dark+ syntax colors
- Comments: JetBrains Mono, 13px, italic, `#6E7681` or `#E74C3C`
- Line numbers: JetBrains Mono, 11px, `#6E7681` at 0.4
- File tab: Inter, 11px, `#E2E8F0` at 0.7

### Easing
- Hard cut in: instant
- Cursor blink: `step(2)` — binary on/off, no fade
- No other animations

## Narration Sync
> "Code just got that cheap."

Segment: `cold_open_005`

- **0:14** ("Code just got"): IDE visible, cursor blinking on patched function
- **0:15** ("that cheap"): Hold — the viewer reads the patch comments, absorbs the weight

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={52}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Editor chrome */}
    <EditorTitleBar color="#161B22" />
    <FileTab name="UserService.ts" modified dotColor="#D9944A" />

    {/* Code content */}
    <CodeBlock
      language="typescript"
      startLine={127}
      fontSize={13}
      font="JetBrains Mono"
      theme="vscode-dark-plus"
      code={PROCESS_USER_DATA_CODE}
      highlightComments={[
        { line: 131, text: '// patched for edge case #247', color: '#6E7681' },
        { line: 139, text: '// TODO: this shouldn\'t be here', color: '#E74C3C' },
        { line: 145, text: '// workaround for legacy API', color: '#6E7681' },
        { line: 152, text: '// HACK: don\'t ask', color: '#E74C3C' },
        { line: 158, text: '// temporary fix, see ticket PD-1892', color: '#6E7681' }
      ]}
      commentBgColor="#D9944A"
      commentBgOpacity={0.08}
    />

    {/* Blinking cursor */}
    <CursorBlink
      line={145} column={42}
      color="#E2E8F0" opacity={0.8}
      width={2}
      onFrames={16} offFrames={16}
    />

    {/* Git gutter indicators */}
    <GitGutter
      lines={{ modified: [128, 131, 133, 139, 140, 145, 146, 152, 153, 158, 159, 162, 165],
               added: [134, 135, 160],
               deleted: [168] }}
      colors={{ modified: '#D9944A', added: '#5AAA6E', deleted: '#E74C3C' }}
      opacity={0.3}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "remotion_animation",
  "animationType": "static_code_display",
  "file": "UserService.ts",
  "functionName": "processUserData",
  "lineRange": [127, 171],
  "patchComments": [
    { "line": 131, "text": "// patched for edge case #247" },
    { "line": 139, "text": "// TODO: this shouldn't be here" },
    { "line": 145, "text": "// workaround for legacy API" },
    { "line": 152, "text": "// HACK: don't ask" },
    { "line": 158, "text": "// temporary fix, see ticket PD-1892" }
  ],
  "cursorPosition": { "line": 145, "column": 42 },
  "gitGutterDensity": "heavy_modified",
  "backgroundColor": "#0D1117",
  "narrationSegments": ["cold_open_005"]
}
```

---
