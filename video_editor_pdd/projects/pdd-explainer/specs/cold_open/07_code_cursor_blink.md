[Remotion]

# Section 0.7: Cursor Blink on Patched Function

**Tool:** Remotion
**Duration:** ~2s
**Timestamp:** 0:14 - 0:16

## Visual Description
Return to code. A dark-themed code editor fills the screen showing a complex function (~30 lines) riddled with visible patches — inline comments like `// HACK:`, `// TODO: refactor`, `// patch for #1247`, diff-style `+` markers in the gutter, and inconsistent indentation suggesting layers of fixes over time. A blinking cursor sits at line 14, mid-function. The code is still, the cursor blinks twice. This is a beat — a moment of recognition for the viewer.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #1E1E1E (VS Code dark theme)
- Font: JetBrains Mono or Fira Code
- Line numbers: visible, #858585

### Chart/Visual Elements
- Code editor mock with syntax highlighting:
  - Keywords (`function`, `if`, `return`): #569CD6
  - Strings: #CE9178
  - Comments: #6A9955
  - HACK/TODO comments: #FF6B6B (bright red, attention-drawing)
  - Variables: #9CDCFE
- Gutter annotations: `+` markers in green (#4EC9B0) on ~8 lines
- Blinking cursor: white (#FFFFFF), 500ms on/off cycle at line 14, column 4

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Code fades in from black (opacity 0 → 1)
2. **Frame 15-60 (0.5-2.0s):** Static code, cursor blinks twice (on/off/on/off). Viewer absorbs the messy, patched code.

### Typography
- Code font: JetBrains Mono, 16px, #D4D4D4
- Line numbers: JetBrains Mono, 14px, #858585
- Comment highlights: JetBrains Mono, 16px, #FF6B6B

### Easing
- Fade in: `easeOutQuad`
- Cursor blink: step function (no easing, binary on/off)

## Narration Sync
> "Code just got that cheap."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <FadeIn durationInFrames={15}>
    <CodeEditor
      code={PATCHED_FUNCTION_CODE}
      language="typescript"
      theme="vscode-dark"
      highlightLines={[3, 7, 12, 18, 22, 25]}
      gutterAnnotations={{ 3: "+", 7: "+", 12: "+", 18: "+", 22: "+", 25: "+" }}
    />
  </FadeIn>
  <BlinkingCursor
    line={14}
    column={4}
    blinkRate={500}
    color="#FFFFFF"
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_editor",
  "language": "typescript",
  "lineCount": 30,
  "patchIndicators": ["// HACK:", "// TODO: refactor", "// patch for #1247"],
  "gutterPlusLines": [3, 7, 12, 18, 22, 25],
  "cursorPosition": { "line": 14, "column": 4 },
  "theme": "vscode-dark"
}
```
