[Remotion]

# Section 7.2: Code Regenerate Workflow — "Code Just Got That Cheap"

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 24:23 - 24:33

## Visual Description
Hard cut to a code editor view. A function with a visible bug sits on screen — a red squiggly underline marks the problematic line. Instead of the developer opening the file and manually patching, the workflow is different: a test file appears in a split pane on the right, a new assertion is typed that captures the expected behavior, and then the terminal at the bottom runs `pdd bug → pdd fix → ✓`. The buggy code dissolves and clean code regenerates — the same visual vocabulary from Section 0.5 but faster and more practiced. This makes the closing argument concrete: this is what "cheap code" looks like in practice.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Editor dark `#1A1B26`
- Grid lines: None

### Chart/Visual Elements
- **Code Editor (left pane, 60% width):**
  - Line numbers: `#4A5568`, left gutter
  - Tab bar: single tab "calculate_total.py" with red modified indicator `#EF4444`
  - Code: 18 lines of Python-like code. Line 11 has the bug — a red squiggly underline `#EF4444` beneath `total += item.price * item.qty`
  - Bug comment visible: `# BUG: doesn't apply discount` in `#EF4444` at line 12

- **Test Pane (right pane, 40% width):**
  - Tab: "test_calculate.py" with green indicator `#50C878`
  - Initially shows 3 existing test functions (collapsed, just signatures visible)
  - New test assertion types in at line 15: `assert calculate_total(cart, discount=0.1) == 90.0`

- **Terminal Strip (bottom, 80px tall):**
  - Dark background `#0D1117`
  - Commands appear sequentially:
    - `$ pdd bug calculate_total` → amber text `#D9944A`
    - `$ pdd fix` → white text `#E2E8F0`
    - Green checkmark `✓ All 4 tests passing` in `#50C878`

- **Vertical Divider:** 1px `#FFFFFF` at 15% opacity between code and test panes

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Code editor fades in. Buggy code visible. Red squiggly underline pulses once.
2. **Frame 20-50 (0.67-1.67s):** Test pane slides in from right (width 0→40%). Existing tests visible. Cursor blinks at end of test file.
3. **Frame 50-100 (1.67-3.33s):** New test assertion types in character-by-character (monospace typewriter effect, ~2 chars/frame). Green highlight flash on the new line when complete.
4. **Frame 100-130 (3.33-4.33s):** Terminal strip slides up from bottom. `$ pdd bug calculate_total` appears (typewriter, fast).
5. **Frame 130-160 (4.33-5.33s):** Brief spinner (3 dots cycling), then `$ pdd fix` appears below.
6. **Frame 160-210 (5.33-7.0s):** Left pane: buggy code dissolves (same smoke-upward effect from Section 0.5 but faster — stagger 1 frame). Clean code regenerates top-to-bottom (stagger 2 frames). Blue flash `#4A90D9` per line.
7. **Frame 210-240 (7.0-8.0s):** Terminal shows `✓ All 4 tests passing` in green. Scale bounce on checkmark (0.5→1.2→1.0).
8. **Frame 240-300 (8.0-10.0s):** Hold. Clean code visible. All tests passing. The new test assertion is highlighted with a subtle amber glow `#D9944A` at 10% — this test caught the bug.

### Typography
- Code: JetBrains Mono, 15px, syntax-highlighted (keywords `#81A1C1`, strings `#A3BE8C`, functions `#88C0D0`)
- Bug comment: JetBrains Mono, 15px, `#EF4444`
- Test code: JetBrains Mono, 14px, same syntax theme
- Line numbers: JetBrains Mono, 13px, `#4A5568`
- Terminal: JetBrains Mono, 14px, `#94A3B8` (commands), `#50C878` (success)
- Tab filenames: Inter, 12px, `#94A3B8`

### Easing
- Pane slide-in: `easeOut(cubic)`
- Typewriter effect: `linear` (fixed chars/frame)
- Code dissolve: `easeIn(quad)`
- Code regeneration: `easeOut(cubic)`
- Blue flash per line: `easeOut(expo)`
- Terminal slide-up: `easeOut(quad)`
- Checkmark bounce: `easeOut(elastic)` with 0.3 damping

## Narration Sync
> "Code just got that cheap."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <EditorChrome tab="calculate_total.py" tabIndicator="#EF4444">
    {/* Left Pane — Buggy Code */}
    <Sequence from={0} durationInFrames={160}>
      <CodeBlock lines={buggyCodeLines} syntaxTheme="nord" width="60%">
        <BugSquiggly line={11} color="#EF4444" />
        <BugComment line={12} text="# BUG: doesn't apply discount" />
      </CodeBlock>
    </Sequence>

    {/* Code Dissolve & Regenerate */}
    <Sequence from={160}>
      <DissolveCascade staggerFrames={1} direction="bottom-to-top" />
    </Sequence>
    <Sequence from={180}>
      <RegenerateCascade
        lines={cleanCodeLines}
        staggerFrames={2}
        flashColor="#4A90D9"
        width="60%"
      />
    </Sequence>

    {/* Vertical Divider */}
    <VerticalDivider x="60%" color="#FFFFFF" opacity={0.15} />

    {/* Right Pane — Test File */}
    <Sequence from={20}>
      <SlideIn direction="right" durationInFrames={30}>
        <TestPane tab="test_calculate.py" tabIndicator="#50C878" width="40%">
          <ExistingTests count={3} collapsed={true} />
          <Sequence from={30}>
            <TypewriterLine
              text='assert calculate_total(cart, discount=0.1) == 90.0'
              line={15}
              charsPerFrame={2}
              highlightOnComplete="#50C878"
            />
          </Sequence>
        </TestPane>
      </SlideIn>
    </Sequence>
  </EditorChrome>

  {/* Terminal Strip */}
  <Sequence from={100}>
    <TerminalStrip height={80} background="#0D1117">
      <TypewriterCommand text="pdd bug calculate_total" color="#D9944A" startFrame={0} />
      <Sequence from={30}>
        <LoadingDots durationInFrames={15} />
      </Sequence>
      <Sequence from={30}>
        <TypewriterCommand text="pdd fix" color="#E2E8F0" startFrame={15} />
      </Sequence>
      <Sequence from={110}>
        <SuccessMessage text="✓ All 4 tests passing" color="#50C878" bounce={true} />
      </Sequence>
    </TerminalStrip>
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "editor": {
    "background": "#1A1B26",
    "leftTab": "calculate_total.py",
    "rightTab": "test_calculate.py",
    "leftWidth": "60%",
    "rightWidth": "40%"
  },
  "buggyCode": {
    "lineCount": 18,
    "bugLine": 11,
    "bugComment": "# BUG: doesn't apply discount",
    "squigglyColor": "#EF4444"
  },
  "testPane": {
    "existingTests": 3,
    "newAssertion": "assert calculate_total(cart, discount=0.1) == 90.0",
    "newAssertionLine": 15
  },
  "dissolve": {
    "staggerFrames": 1,
    "direction": "bottom-to-top"
  },
  "regeneration": {
    "staggerFrames": 2,
    "flashColor": "#4A90D9"
  },
  "terminal": {
    "background": "#0D1117",
    "height": 80,
    "commands": [
      { "text": "pdd bug calculate_total", "color": "#D9944A" },
      { "text": "pdd fix", "color": "#E2E8F0" }
    ],
    "success": { "text": "✓ All 4 tests passing", "color": "#50C878" }
  }
}
```

---
