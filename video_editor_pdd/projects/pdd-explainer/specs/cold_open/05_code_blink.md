[Remotion]

# Section 0.5: Code Blink — Delete and Regenerate

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:20 - 0:25

## Visual Description

Hard cut back to code. A single function fills the screen in a dark IDE — a complex, heavily-patched function with visible scars of maintenance. Inline comments mark past fixes: `// fixed null case`, `// workaround for #412`, `// TODO: refactor`. Diff-colored left-margin indicators (amber, faded red) show layers of patches accumulated over time.

The cursor blinks at the top of the function. One beat of stillness — the viewer registers the mess. Then the entire function selects (blue highlight sweeps top-to-bottom in a single smooth motion), and deletes. The lines dissolve into particles that drift downward and fade to nothing. A brief moment of empty editor — just line numbers and a blinking cursor.

Then new, clean code types in rapidly from top to bottom — no comments, no patches, no workarounds. Just clean, purposeful code. Fewer lines. Better structure. In the bottom-right corner, a subtle terminal widget shows `$ pdd generate ✓` completing with a green checkmark.

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
- Inline comments: `// fixed null case` (line 4), `// workaround for #412` (line 11), `// TODO: refactor` (line 16) in #6A737D
- Cursor: white block cursor #FFFFFF at line 1, blinking 500ms

**Selection Highlight**
- Blue sweep: #4A90D9 at 25% opacity
- Sweeps from line 1 to line 18 in a single downward motion

**Particle Dissolution**
- Each character becomes a particle on delete
- Particles: 2×2px, inherit their syntax color
- Drift downward with slight random x-spread (±30px)
- Fade: opacity 1 → 0 over 15 frames
- ~300 total particles

**Clean Function (after)**
- 14 lines of clean code, same syntax highlighting palette
- No patch indicators, no inline comments, no TODOs
- Types in top-to-bottom, 2 lines per frame (rapid)

**Terminal Widget (bottom-right)**
- Position: (1580, 980), 300×60px
- Background: #0F172A at 80% opacity, rounded corners 6px
- Text: `$ pdd generate ✓` in #5AAA6E, JetBrains Mono 11px
- Green checkmark appears after code finishes typing

### Animation Sequence

1. **Frame 0-20 (0-0.67s):** Patched function visible. Cursor blinks twice. Viewer reads the mess. Stillness.
2. **Frame 20-30 (0.67-1.0s):** Blue selection highlight sweeps from line 1 to line 18.
3. **Frame 30-50 (1.0-1.67s):** All selected lines dissolve into particles. Particles drift down and fade. Editor empties.
4. **Frame 50-55 (1.67-1.83s):** Empty editor. Brief beat. Just line numbers and cursor. The absence is felt.
5. **Frame 55-75 (1.83-2.5s):** Clean code types in rapidly, 2 lines per frame, top-to-bottom. Green highlight briefly trails each line.
6. **Frame 75-90 (2.5-3.0s):** Terminal widget fades in bottom-right. `$ pdd generate` appears, then checkmark `✓` in green.
7. **Frame 90-150 (3.0-5.0s):** Hold. Clean code and terminal visible. Cursor blinks. The contrast with the patched version settles in.

### Typography

- Code text: `JetBrains Mono`, 14px, syntax-colored
- Line numbers: `JetBrains Mono`, 12px, #4A5568
- Terminal text: `JetBrains Mono`, 11px, #5AAA6E
- Inline comments (before): `JetBrains Mono`, 14px, #6A737D italic

### Easing

- Selection sweep: `linear` (constant speed down the file)
- Particle dissolution: `easeIn(quad)` (accelerating downward drift)
- Particle fade: `linear`
- Code type-in: `linear` (rapid, mechanical feel)
- Terminal fade-in: `easeOut(quad)`
- Checkmark appear: `easeOut(back(1.3))` (slight overshoot)

## Narration Sync

> "Code just got that cheap."
Segment: `cold_open_005`
Timing: 0:20 - 0:22

> (Beat of silence — the visual carries the moment)
Timing: 0:22 - 0:25

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#1E1E2E' }}>
    <LineNumberGutter width={60} color="#4A5568" lineCount={18} />

    {/* Phase 1: Patched function with selection */}
    <Sequence from={0} durationInFrames={30}>
      <PatchedFunction
        lines={18}
        patchMarkers={[
          { line: 4, color: "#D9944A", width: 3 },
          { line: 7, color: "#D9944A", width: 3 },
          { line: 11, color: "#D9944A", width: 3 },
          { line: 14, color: "#EF4444", opacity: 0.3, width: 3 },
          { line: 16, color: "#EF4444", opacity: 0.3, width: 3 }
        ]}
        inlineComments={[
          { line: 4, text: "// fixed null case" },
          { line: 11, text: "// workaround for #412" },
          { line: 16, text: "// TODO: refactor" }
        ]}
      />
      <BlinkingCursor line={1} color="#FFFFFF" />
      <Sequence from={20} durationInFrames={10}>
        <SelectionSweep
          fromLine={1}
          toLine={18}
          color="rgba(74,144,217,0.25)"
        />
      </Sequence>
    </Sequence>

    {/* Phase 2: Particle dissolution */}
    <Sequence from={30} durationInFrames={20}>
      <ParticleDissolution
        particleSize={2}
        driftDirection="down"
        xSpread={30}
        fadeFrames={15}
      />
    </Sequence>

    {/* Phase 3: Clean code types in */}
    <Sequence from={55} durationInFrames={20}>
      <CleanFunction lines={14} typeSpeed={2} trailColor="#5AAA6E" />
    </Sequence>

    {/* Terminal widget */}
    <Sequence from={75} durationInFrames={75}>
      <TerminalWidget
        command="pdd generate"
        status="success"
        position={[1580, 980]}
        size={[300, 60]}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON

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
    "driftSpeed": 3,
    "xSpread": 30,
    "totalCount": 300
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
  "narrationTimingSeconds": { "start": 20.0, "end": 25.0 }
}
```

---
