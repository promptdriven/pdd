[Remotion]

# Section 0.5: Code Regeneration — The Punchline

**Tool:** Remotion
**Duration:** ~15s (450 frames @ 30fps)
**Timestamp:** 0:40 - 0:55

## Visual Description
Return to the code editor view (full frame, no split). A complex function sits on screen — visibly messy, full of accumulated patches. The cursor blinks on it for a beat. Then the narration lands: "Code just got that cheap." The entire function DELETES — lines dissolve upward like smoke, leaving a blank editor. A brief pause. Then clean, fresh code regenerates from the top, flowing downward line by line. It's the same function but pristine — no patches, no TODOs, no hacks. In the bottom-right corner, a subtle terminal snippet shows `pdd generate` completing with a green checkmark.

This is the emotional payoff of the cold open: the sock-toss metaphor made concrete in code.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Editor dark `#1A1B26`
- Grid lines: None

### Chart/Visual Elements
- **Code Editor (full frame):**
  - Line numbers: `#4A5568`, left gutter
  - Tab bar: single tab "process_data.py" with amber modified indicator `#D9944A`
  - Initial code: 25 lines of patched Python-like code with visible debt:
    - Lines with `// HACK:` comments in `#EF4444`
    - Lines with `// TODO: refactor` in `#F59E0B`
    - Inconsistent indentation regions highlighted in faint `#EF4444` at 5% opacity
    - 3 visible diff markers (amber `#D9944A` blocks in gutter)

- **Regenerated Code:**
  - Same 25 lines but clean: consistent indentation, no HACK/TODO comments
  - Subtle blue tint `#4A90D9` at 3% opacity over the code block — the "prompt-generated" glow
  - Clean syntax highlighting: keywords `#81A1C1`, strings `#A3BE8C`, functions `#88C0D0`

- **Terminal Snippet (bottom-right corner):**
  - Dark rounded rectangle `#0D1117` with 8px border-radius, ~300x40px
  - Text: `$ pdd generate` in `#94A3B8` monospace, followed by green `✓` in `#50C878`
  - Position: anchored at (1580, 1010), right-aligned, 40px from edges

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Messy code visible. Cursor blinks at line 12. Camera holds. Beat.
2. **Frame 30-45 (1.0-1.5s):** Narration: "Code just got that cheap." — no visual change yet. Tension builds.
3. **Frame 45-90 (1.5-3.0s):** Code deletion cascade. Lines dissolve from bottom to top — each line fades out (opacity 1→0) and translates upward 20px, staggered 2 frames apart. Produces a "smoke dissolving upward" effect. HACK/TODO lines dissolve first (they go 3x faster than clean lines).
4. **Frame 90-120 (3.0-4.0s):** Empty editor. Just line numbers and the blank gutter. Brief pause. The emptiness is intentional — a visual breath.
5. **Frame 120-210 (4.0-7.0s):** Regeneration cascade. Clean code lines appear from top to bottom — each line fades in (opacity 0→1) and slides down from 10px above, staggered 3 frames apart. Each line has a brief blue flash `#4A90D9` at 20% opacity that fades to the subtle 3% tint.
6. **Frame 210-240 (7.0-8.0s):** Terminal snippet fades in at bottom-right. `$ pdd generate` text appears, then green `✓` pops in with a small scale bounce (0.5→1.2→1.0)
7. **Frame 240-330 (8.0-11.0s):** Narration: "So why are we still patching?" — code holds, fully regenerated. The clean code glows faintly.
8. **Frame 330-450 (11.0-15.0s):** Hold on clean code with terminal snippet visible. Idle cursor blink.

### Typography
- Code: JetBrains Mono, 16px, syntax-highlighted
- HACK comments: JetBrains Mono, 16px, `#EF4444`
- TODO comments: JetBrains Mono, 16px, `#F59E0B`
- Line numbers: JetBrains Mono, 14px, `#4A5568`
- Terminal text: JetBrains Mono, 14px, `#94A3B8`
- Terminal checkmark: 16px, `#50C878`
- Tab filename: Inter, 13px, `#94A3B8`

### Easing
- Line dissolve (up): `easeIn(quad)` — accelerates out
- Line regenerate (down): `easeOut(cubic)` — decelerates in, feels weighty
- Blue flash per line: `easeOut(expo)` — sharp flash, slow fade
- Terminal fade-in: `easeOut(quad)`
- Checkmark bounce: `easeOut(elastic)` with 0.3 damping

## Narration Sync
> "Code just got that cheap."
> "So why are we still patching?"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={450}>
  <EditorChrome tab="process_data.py" tabIndicator="#D9944A">
    {/* Phase 1: Messy Code */}
    <Sequence from={0} durationInFrames={90}>
      <CodeBlock lines={messyCodeLines} syntaxTheme="nord">
        <HackHighlights color="#EF4444" />
        <TodoHighlights color="#F59E0B" />
        <GutterDiffMarkers color="#D9944A" lines={[4, 11, 19]} />
      </CodeBlock>
    </Sequence>

    {/* Phase 2: Dissolve Cascade */}
    <Sequence from={45}>
      <DissolveCascade
        direction="bottom-to-top"
        staggerFrames={2}
        translateY={-20}
        priorityLines={{ hack: 3, todo: 3, normal: 1 }}
      />
    </Sequence>

    {/* Phase 3: Regeneration Cascade */}
    <Sequence from={120}>
      <RegenerateCascade
        lines={cleanCodeLines}
        direction="top-to-bottom"
        staggerFrames={3}
        flashColor="#4A90D9"
        flashOpacity={0.2}
        restTint={0.03}
      />
    </Sequence>
  </EditorChrome>

  {/* Terminal Snippet */}
  <Sequence from={210}>
    <TerminalSnippet
      position={[1580, 1010]}
      command="pdd generate"
      checkmarkColor="#50C878"
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "editor": {
    "background": "#1A1B26",
    "tab": "process_data.py",
    "tabIndicator": "#D9944A",
    "lineCount": 25
  },
  "messyCode": {
    "hackLines": [3, 7, 15],
    "todoLines": [9, 21],
    "diffMarkerLines": [4, 11, 19],
    "hackColor": "#EF4444",
    "todoColor": "#F59E0B"
  },
  "dissolve": {
    "direction": "bottom-to-top",
    "staggerFrames": 2,
    "translateY": -20
  },
  "regeneration": {
    "direction": "top-to-bottom",
    "staggerFrames": 3,
    "flashColor": "#4A90D9",
    "flashOpacity": 0.2,
    "restTint": 0.03
  },
  "terminal": {
    "position": [1580, 1010],
    "background": "#0D1117",
    "command": "pdd generate",
    "checkmarkColor": "#50C878"
  }
}
```

---
