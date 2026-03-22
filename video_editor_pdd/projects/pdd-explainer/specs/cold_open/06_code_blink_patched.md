[Remotion]

# Section 0.4: Cursor Blink on Patched Code

**Tool:** Remotion
**Duration:** ~2s
**Timestamp:** 0:14 - 0:16

## Visual Description
Return to the code world. A code editor view (dark theme) shows a complex function that has clearly been patched multiple times — visible signs include inconsistent indentation, inline comments like `// FIXME`, `// patched for edge case`, mixed naming conventions, and a conditional block that's been bolted on. A blinking cursor sits at the end of the function. The code looks functional but tired — a visual metaphor for accumulated technical debt. The cursor blinks twice, waiting. The feeling: is this really worth one more patch?

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #1E1E1E (VS Code dark)
- Line gutter: #2D2D2D, 48px wide

### Chart/Visual Elements
- **Code block:** monospace text, syntax-highlighted
  - Keywords: #569CD6 (blue)
  - Strings: #CE9178 (orange)
  - Comments: #6A9955 (green), with `// FIXME` and `// patched` in #F44747 (red)
  - Functions: #DCDCAA (yellow)
  - Variables: #9CDCFE (light blue)
- **Cursor:** 2px wide, #AEAFAD, blinking at 530ms interval
- **Line highlight:** current line background #282828
- **Gutter line numbers:** #858585, `JetBrains Mono` 13px

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Code fades in from black, opacity 0 → 1
2. **Frame 15-60 (0.5-2.0s):** Static code display, cursor blinks twice (530ms on, 530ms off cycle). Subtle attention — viewer reads the messy patches.

### Typography
- Code: `JetBrains Mono`, 14px, line-height 1.6
- Comment highlights: `JetBrains Mono`, 14px, #F44747

### Easing
- Fade-in: `easeOutQuad`
- Cursor blink: step function (binary on/off)

## Narration Sync
> "Code just got that cheap."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <AbsoluteFill style={{ background: '#1E1E1E' }}>
    <Sequence from={0} durationInFrames={15}>
      <FadeIn>
        <CodeEditor code={patchedFunction} language="typescript" />
      </FadeIn>
    </Sequence>
    <Sequence from={15} durationInFrames={45}>
      <BlinkingCursor interval={530} color="#AEAFAD" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_editor",
  "language": "typescript",
  "theme": "vscode_dark",
  "annotations": [
    { "line": 4, "text": "// FIXME: edge case from PR #847", "color": "#F44747" },
    { "line": 12, "text": "// patched — original logic broke on null", "color": "#F44747" },
    { "line": 18, "text": "// TODO: refactor this entire block", "color": "#F4A347" }
  ],
  "cursorPosition": { "line": 23, "column": 0 },
  "cursorBlinkMs": 530
}
```
