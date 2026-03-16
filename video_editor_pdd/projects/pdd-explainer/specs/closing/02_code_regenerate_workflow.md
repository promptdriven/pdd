[Remotion]

# Section 7.2: Code Regenerate Workflow — Bug → Fix → Check

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 24:23 - 24:33

## Visual Description
A terminal-style animation shows the PDD workflow in action. A buggy code file appears on the left half of the screen — a simplified code block with a visible red squiggle on one line. Instead of opening the file and patching, a developer adds a test (a green line appears in a test file on the right), then executes a three-step terminal sequence: `pdd bug` → `pdd fix` → `✓ check`. Each command types out in the terminal with a brief processing animation, and a green checkmark confirms success. The code block on the left dissolves and is replaced by a fresh version — clean, no squiggles. The key insight: the developer never touched the code directly.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A1628` (deep navy)
- Grid lines: None

### Chart/Visual Elements
- **Code Block (Left, X: 80-880):**
  - Container: Rounded rectangle, `#1E293B` fill, border `rgba(255,255,255,0.06)`, border-radius 8px
  - Title bar: "module.py" in `#94A3B8`, 13px JetBrains Mono, with red dot `#EF4444` at 8px diameter (unsaved indicator)
  - Code lines: 12 rows of simulated code — horizontal bars at varying widths (60-320px), `rgba(255,255,255,0.08)` fill, height 8px, spaced 24px apart, starting at Y=160
  - Bug indicator: Line 7 has a wavy red underline (`#EF4444` at 0.5 opacity), 3px stroke
  - Post-regenerate: All lines are fresh bars (slightly different widths), bug line replaced with clean bar, green tint `rgba(90,170,110,0.1)` background flash on entire block
- **Test Block (Right, X: 960-1840):**
  - Container: Same style as code block, `#1E293B` fill
  - Title bar: "test_module.py" in `#94A3B8`, 13px JetBrains Mono, with green dot `#5AAA6E` at 8px
  - Existing test lines: 6 rows of simulated code bars, `rgba(255,255,255,0.08)`
  - New test line: Appears at row 7, bar colored `#5AAA6E` at 0.3 opacity with a typing/extend animation (width grows 0→240px)
- **Terminal Strip (Bottom, Y: 740-980):**
  - Container: Full-width rounded rectangle, `#0D1117` fill, border `rgba(255,255,255,0.04)`, height 240px
  - Prompt prefix: `$` in `#6E7681`, 14px JetBrains Mono
  - Command 1: `pdd bug` — types out in `#C9D1D9`, 14px JetBrains Mono, followed by spinner (⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏ cycle), then `→ found: line 7` in `#D9944A`
  - Command 2: `pdd fix` — types out, spinner, then `→ regenerated module.py` in `#5AAA6E`
  - Command 3: `pdd test` — types out, spinner, then `✓ all tests pass` in `#5AAA6E`
- **"Never opened the file" annotation:** Appears at bottom-center, `#FFFFFF` at 0.4 opacity, 16px Inter italic

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Code block fades in on left. Bug squiggle pulses once (attention). Test block fades in on right
2. **Frame 30-60 (1.0-2.0s):** New test line types/extends into the test block at row 7. Green dot on test file pulses
3. **Frame 60-90 (2.0-3.0s):** Terminal strip slides up from bottom. `$ pdd bug` types out character by character (2 frames/char)
4. **Frame 90-120 (3.0-4.0s):** Spinner cycles 6 times. Output: `→ found: line 7` appears. Bug squiggle in code block brightens momentarily
5. **Frame 120-150 (4.0-5.0s):** `$ pdd fix` types out. Spinner cycles 6 times. Output: `→ regenerated module.py`
6. **Frame 150-180 (5.0-6.0s):** Code block dissolves — all lines simultaneously fade out (opacity 1→0 over 15 frames), then new lines fade in (0→1, slightly different widths). Green tint flash on the entire block (0→0.1→0 opacity, 20 frames)
7. **Frame 180-210 (6.0-7.0s):** `$ pdd test` types out. Spinner cycles 4 times. Output: `✓ all tests pass` in green
8. **Frame 210-240 (7.0-8.0s):** Green checkmark scales up briefly (1.0→1.2→1.0) in the terminal. Red dot on code file transitions to green dot
9. **Frame 240-270 (8.0-9.0s):** Annotation fades in: "Never opened the file"
10. **Frame 270-300 (9.0-10.0s):** Hold at final state. Subtle ambient glow on the green elements

### Typography
- File titles: JetBrains Mono, 13px, regular (400), `#94A3B8`
- Terminal commands: JetBrains Mono, 14px, regular (400), `#C9D1D9`
- Terminal output: JetBrains Mono, 14px, regular (400), varies by context
- Annotation: Inter, 16px, italic, `#FFFFFF` at 0.4 opacity

### Easing
- Block fade-in: `easeOut(quad)`
- Test line extend: `easeOut(cubic)`
- Terminal slide-up: `easeOut(cubic)`
- Code dissolve/regenerate: `easeInOut(sine)`
- Green flash: `easeInOut(sine)`
- Checkmark scale pulse: `easeOut(quad)`
- Annotation fade: `easeOut(quad)`

## Narration Sync
> "Code just got that cheap."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0A1628' }}>
    {/* Code Block */}
    <Sequence from={0} durationInFrames={300}>
      <CodeBlock
        title="module.py"
        x={80}
        width={800}
        lines={12}
        bugLine={7}
        regenerateAtFrame={150}
      />
    </Sequence>

    {/* Test Block */}
    <Sequence from={0} durationInFrames={300}>
      <TestBlock
        title="test_module.py"
        x={960}
        width={880}
        existingLines={6}
        newTestAtFrame={30}
      />
    </Sequence>

    {/* Terminal Strip */}
    <Sequence from={60} durationInFrames={240}>
      <TerminalStrip y={740} height={240}>
        <TerminalCommand
          from={0}
          command="pdd bug"
          output="→ found: line 7"
          outputColor="#D9944A"
        />
        <TerminalCommand
          from={60}
          command="pdd fix"
          output="→ regenerated module.py"
          outputColor="#5AAA6E"
        />
        <TerminalCommand
          from={120}
          command="pdd test"
          output="✓ all tests pass"
          outputColor="#5AAA6E"
        />
      </TerminalStrip>
    </Sequence>

    {/* Annotation */}
    <Sequence from={240} durationInFrames={60}>
      <FadeText
        text="Never opened the file"
        fontSize={16}
        fontStyle="italic"
        opacity={0.4}
        y={1020}
        align="center"
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0A1628",
  "codeBlock": {
    "title": "module.py",
    "lines": 12,
    "bugLine": 7,
    "bugColor": "#EF4444",
    "blockFill": "#1E293B"
  },
  "testBlock": {
    "title": "test_module.py",
    "existingLines": 6,
    "newTestColor": "#5AAA6E"
  },
  "terminal": {
    "background": "#0D1117",
    "commands": [
      { "cmd": "pdd bug", "output": "→ found: line 7", "outputColor": "#D9944A" },
      { "cmd": "pdd fix", "output": "→ regenerated module.py", "outputColor": "#5AAA6E" },
      { "cmd": "pdd test", "output": "✓ all tests pass", "outputColor": "#5AAA6E" }
    ]
  },
  "annotation": "Never opened the file"
}
```

---
