[Remotion]

# Section 6.4: Three Commands — The PDD Workflow in Practice

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 22:50 - 23:06

## Visual Description
A terminal-style animation showing the actual PDD workflow in three concrete commands. A realistic dark terminal window occupies the center of the screen. Commands type in one-by-one with visible output, showing the full cycle: (1) `pdd init csv_parser` — initializes a module with prompt scaffold and existing tests, (2) `pdd generate csv_parser` — generates code from the prompt, (3) `pdd test csv_parser` — runs the test suite with all tests passing. Each command is preceded by a numbered step label that floats to the left of the terminal. After all three commands complete, a brief "loop" arrow animates to show that steps 2-3 repeat: edit prompt → regenerate → test. The viewer leaves knowing exactly what commands to type.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Terminal Window:** Centered, 1000px wide x 600px tall, positioned at (460, 200)
  - Background: `#0C1222`, border-radius 8px
  - Title bar: 32px tall, `#1E293B`, three dots (red `#EF4444`, yellow `#F59E0B`, green `#22C55E`) at 8px each, left-aligned with 8px spacing
  - Title text: "csv_parser — zsh" — JetBrains Mono 11px, `#94A3B8`, centered in title bar
  - Inner padding: 16px
- **Step Labels (left of terminal, X=160):**
  - Step 1: Circle 36px, border `#4A90D9` 2px, number "1" inside — Inter 18px bold, `#4A90D9`. Y=310
  - Step 2: Circle 36px, border `#5AAA6E` 2px, number "2" inside — Inter 18px bold, `#5AAA6E`. Y=430
  - Step 3: Circle 36px, border `#D9944A` 2px, number "3" inside — Inter 18px bold, `#D9944A`. Y=560
- **Terminal Content (typed character-by-character):**
  - **Block 1 (Init):**
    - `$ pdd init csv_parser` — prompt `$` in `#5AAA6E`, command in `#C8CCD4`
    - Output line 1: `✓ Created csv_parser.prompt (from existing docstring)` — `#5AAA6E`
    - Output line 2: `✓ Found 12 existing tests — linked as walls` — `#D9944A`
    - Output line 3: `  Ready to generate.` — `#94A3B8`
  - **Block 2 (Generate):**
    - `$ pdd generate csv_parser` — same prompt style
    - Output line 1: `Generating from prompt + 12 test walls...` — `#94A3B8`
    - Output line 2: `✓ csv_parser.py generated (187 lines)` — `#5AAA6E`
  - **Block 3 (Test):**
    - `$ pdd test csv_parser` — same prompt style
    - Output line 1: `Running 12 tests...` — `#94A3B8`
    - Output line 2: `12 passed ✓  0 failed` — `#22C55E`, bold
- **Loop Arrow (after terminal, Y=850):**
  - Curved arrow from Step 3 back to Step 2, `rgba(255,255,255,0.2)`, 2px stroke
  - Label on arrow: "edit prompt → regenerate → test" — Inter 14px, `rgba(255,255,255,0.4)`

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Terminal window fades in with slight scale (0.95→1.0). Title bar details appear
2. **Frame 30-50 (1.0-1.67s):** Step 1 circle scales in with back easing. Brief pause
3. **Frame 50-130 (1.67-4.33s):** Block 1 types in — command first (~3 chars/frame), then output lines appear with 15-frame delays between lines. "12 existing tests" text in amber to connect to the mold metaphor
4. **Frame 130-150 (4.33-5.0s):** Step 2 circle scales in. Brief pause
5. **Frame 150-230 (5.0-7.67s):** Block 2 types in — command, then generating message with a brief "processing" ellipsis animation (3 dots cycle for 30 frames), then success output
6. **Frame 230-250 (7.67-8.33s):** Step 3 circle scales in. Brief pause
7. **Frame 250-340 (8.33-11.33s):** Block 3 types in — command, running message, then "12 passed" result. The "12 passed ✓" line gets a brief green flash/glow on appear
8. **Frame 340-410 (11.33-13.67s):** Loop arrow draws from Step 3 back to Step 2. Arrow animates as a curved path draw. Label fades in alongside the arrow
9. **Frame 410-480 (13.67-16.0s):** Hold at final state. Terminal cursor blinks. Loop arrow has subtle animated dashes flowing along its path (indicating repetition)

### Typography
- Terminal Title: JetBrains Mono, 11px, regular (400), `#94A3B8`
- Terminal Prompt ($): JetBrains Mono, 14px, bold (700), `#5AAA6E`
- Terminal Commands: JetBrains Mono, 14px, regular (400), `#C8CCD4`
- Terminal Output: JetBrains Mono, 13px, regular (400), respective colors
- Step Numbers: Inter, 18px, bold (700), respective step colors
- Loop Label: Inter, 14px, regular (400), `rgba(255,255,255,0.4)`

### Easing
- Terminal window appear: `easeOut(quad)`
- Step circles: `easeOut(back(1.5))`
- Character typing: `steps(1)` per character (typewriter)
- Output line reveals: `easeOut(quad)`
- Processing dots: `steps(1)` (cycle)
- Green flash: `easeInOut(sine)`
- Loop arrow draw: `easeInOut(cubic)`
- Loop label fade: `easeOut(quad)`

## Narration Sync
> "The workflow is three commands. First, initialize — PDD reads your existing code and tests, creates a prompt scaffold. Second, generate — it produces code from your prompt, constrained by those test walls. Third, test — run the suite. If it passes, you're done. If not, you have a choice: strengthen the prompt, or add a test. Then regenerate again."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  {/* Terminal Window */}
  <Sequence from={0} durationInFrames={30}>
    <TerminalWindow
      width={1000} height={600}
      x={460} y={200}
      title="csv_parser — zsh"
    />
  </Sequence>

  {/* Step 1: Init */}
  <Sequence from={30} durationInFrames={20}>
    <StepCircle number={1} color="#4A90D9" y={310} x={160} />
  </Sequence>
  <Sequence from={50} durationInFrames={80}>
    <TypedBlock lines={initLines} charSpeed={3} lineDelay={15} />
  </Sequence>

  {/* Step 2: Generate */}
  <Sequence from={130} durationInFrames={20}>
    <StepCircle number={2} color="#5AAA6E" y={430} x={160} />
  </Sequence>
  <Sequence from={150} durationInFrames={80}>
    <TypedBlock lines={generateLines} charSpeed={3} lineDelay={15}>
      <ProcessingDots duration={30} />
    </TypedBlock>
  </Sequence>

  {/* Step 3: Test */}
  <Sequence from={230} durationInFrames={20}>
    <StepCircle number={3} color="#D9944A" y={560} x={160} />
  </Sequence>
  <Sequence from={250} durationInFrames={90}>
    <TypedBlock lines={testLines} charSpeed={3} lineDelay={15} />
    <GlowFlash target="12 passed ✓" color="#22C55E" delay={70} />
  </Sequence>

  {/* Loop Arrow */}
  <Sequence from={340} durationInFrames={70}>
    <LoopArrow
      from={{ step: 3, y: 560 }}
      to={{ step: 2, y: 430 }}
      label="edit prompt → regenerate → test"
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "terminal": {
    "width": 1000,
    "height": 600,
    "background": "#0C1222",
    "titleBar": "#1E293B"
  },
  "steps": [
    {
      "number": 1,
      "label": "Init",
      "color": "#4A90D9",
      "command": "pdd init csv_parser",
      "output": [
        "✓ Created csv_parser.prompt (from existing docstring)",
        "✓ Found 12 existing tests — linked as walls",
        "  Ready to generate."
      ]
    },
    {
      "number": 2,
      "label": "Generate",
      "color": "#5AAA6E",
      "command": "pdd generate csv_parser",
      "output": [
        "Generating from prompt + 12 test walls...",
        "✓ csv_parser.py generated (187 lines)"
      ]
    },
    {
      "number": 3,
      "label": "Test",
      "color": "#D9944A",
      "command": "pdd test csv_parser",
      "output": [
        "Running 12 tests...",
        "12 passed ✓  0 failed"
      ]
    }
  ],
  "loopLabel": "edit prompt → regenerate → test"
}
```

---
