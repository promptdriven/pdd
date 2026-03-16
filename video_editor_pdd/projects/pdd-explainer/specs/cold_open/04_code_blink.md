[Remotion]

# Section 0.4: Code Blink — "Code Just Got That Cheap"

**Tool:** Remotion
**Duration:** ~2s (60 frames @ 30fps)
**Timestamp:** 0:14 - 0:16

## Visual Description

Hard cut back to the code side. A single function fills the screen — a complex, heavily-patched function with visible scars of maintenance. Inline comments mark past fixes: `// fixed null case`, `// workaround for #412`, `// TODO: refactor`. Diff-colored lines (amber, faded red) indicate layers of patches.

The cursor blinks at the top of the function. One beat of stillness. Then the entire function selects (blue highlight sweeps top-to-bottom), and deletes — the lines dissolve into particles that drift downward and fade. A brief moment of blank editor. Then new, clean code types in rapidly from top to bottom — no comments, no patches, no workarounds. Just clean, purposeful code.

In the bottom-right corner, a subtle terminal widget shows `pdd generate` completing with a green checkmark.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #1E1E2E (VS Code dark theme)
- Line numbers: visible, #4A5568, left gutter 60px wide

### Chart/Visual Elements

**Patched Function (before)**
- 18 lines of code, monospace
- Syntax highlighting: keywords #78DCE8, strings #A9DC76, comments #6A737D
- Patch indicators: 3 lines with amber left-border #D9944A (3px), 2 lines with faded red left-border #EF4444 at 30% opacity
- Inline comments: `// fixed null case`, `// workaround for #412`, `// TODO: refactor` in #6A737D
- Cursor: white block cursor #FFFFFF at line 1, blinking 500ms

**Selection Highlight**
- Blue sweep: #4A90D9 at 25% opacity
- Sweeps from line 1 to line 18

**Particle Dissolution**
- Each character becomes a particle on delete
- Particles: 2×2px, inherit syntax color, drift downward with slight random x-spread
- Fade: opacity 1 → 0 over 15 frames

**Clean Function (after)**
- 14 lines of clean code, same syntax highlighting
- No patch indicators, no inline comments
- Types in top-to-bottom, 2 lines per frame

**Terminal Widget (bottom-right)**
- Position: (1580, 980), 300×60px
- Background: #0F172A at 80% opacity, rounded corners 6px
- Text: `$ pdd generate ✓` in #5AAA6E, JetBrains Mono 11px
- Green checkmark appears after code finishes typing

### Animation Sequence
1. **Frame 0-12 (0-0.4s):** Patched function visible. Cursor blinks once. Stillness.
2. **Frame 12-20 (0.4-0.67s):** Blue selection highlight sweeps from line 1 to line 18.
3. **Frame 20-35 (0.67-1.17s):** All selected lines dissolve into particles. Particles drift down and fade.
4. **Frame 35-38 (1.17-1.27s):** Empty editor. Brief beat.
5. **Frame 38-52 (1.27-1.73s):** Clean code types in rapidly, 2 lines per frame, top-to-bottom.
6. **Frame 52-60 (1.73-2.0s):** Terminal widget fades in. Checkmark appears. Hold.

### Typography
- Code text: `JetBrains Mono`, 14px
- Line numbers: `JetBrains Mono`, 12px, #4A5568
- Terminal text: `JetBrains Mono`, 11px, #5AAA6E

### Easing
- Selection sweep: `linear` (constant speed down the file)
- Particle dissolution: `easeIn(quad)` (accelerating downward drift)
- Particle fade: `linear`
- Code type-in: `linear` (rapid, mechanical)
- Terminal fade-in: `easeOut(quad)`

## Narration Sync
> "Code just got that cheap."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <EditorBackground theme="dark" lineNumbers={true} />
  <Sequence from={0} durationInFrames={20}>
    <PatchedFunction lines={18} patchMarkers={5} />
    <BlinkingCursor line={1} />
    <Sequence from={12} durationInFrames={8}>
      <SelectionSweep fromLine={1} toLine={18} color="rgba(74,144,217,0.25)" />
    </Sequence>
  </Sequence>
  <Sequence from={20} durationInFrames={15}>
    <ParticleDissolution particleSize={2} driftDirection="down" />
  </Sequence>
  <Sequence from={38} durationInFrames={14}>
    <CleanFunction lines={14} typeSpeed={2} />
  </Sequence>
  <Sequence from={52} durationInFrames={8}>
    <TerminalWidget
      command="pdd generate"
      status="success"
      position={[1580, 980]}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "editor": {
    "background": "#1E1E2E",
    "lineNumberColor": "#4A5568",
    "gutterWidth": 60
  },
  "patchedFunction": {
    "lineCount": 18,
    "syntaxColors": {
      "keywords": "#78DCE8",
      "strings": "#A9DC76",
      "comments": "#6A737D"
    },
    "patchMarkers": [
      { "line": 4, "color": "#D9944A", "width": 3 },
      { "line": 7, "color": "#D9944A", "width": 3 },
      { "line": 11, "color": "#D9944A", "width": 3 },
      { "line": 14, "color": "#EF4444", "opacity": 0.3, "width": 3 },
      { "line": 16, "color": "#EF4444", "opacity": 0.3, "width": 3 }
    ],
    "inlineComments": [
      { "line": 4, "text": "// fixed null case" },
      { "line": 11, "text": "// workaround for #412" },
      { "line": 16, "text": "// TODO: refactor" }
    ]
  },
  "selection": {
    "color": "rgba(74,144,217,0.25)",
    "fromLine": 1,
    "toLine": 18
  },
  "particles": {
    "size": 2,
    "fadeFrames": 15,
    "driftSpeed": 3
  },
  "cleanFunction": {
    "lineCount": 14,
    "typeLinesPerFrame": 2
  },
  "terminal": {
    "position": [1580, 980],
    "size": [300, 60],
    "background": "#0F172A",
    "backgroundOpacity": 0.8,
    "borderRadius": 6,
    "command": "pdd generate",
    "checkColor": "#5AAA6E"
  },
  "narrationSegments": ["cold_open_005"],
  "narrationTimingSeconds": { "start": 14.12, "end": 15.86 }
}
```

---
