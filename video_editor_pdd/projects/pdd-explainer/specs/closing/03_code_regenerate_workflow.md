[Remotion]

# Section 7.3: Code Regenerate Workflow — Never Opened the File

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 24:23 - 24:33

## Visual Description

A terminal-style demonstration that makes the PDD workflow viscerally concrete. The screen is divided into three zones: a code block (left), a test file (right), and a terminal strip (bottom). The narration says "Code just got that cheap" — and the visual proves it.

A bug is highlighted in the code block in red. Instead of the cursor entering the code file, a terminal command `pdd bug` runs — a failing test materializes in the test panel. Then `pdd fix` runs — the entire code block dissolves and regenerates from scratch. The tests all pass. A subtle annotation appears: "Never opened the file."

The whole sequence emphasizes that the developer never touched the code directly. The code was disposable. The test was the fix.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A1628` (deep navy)
- Grid lines: none

### Chart/Visual Elements

#### Code Block (Left Zone)
- Position: x: 60, y: 80, width: 860, height: 700
- Background: `#1E293B` at 0.4, rounded 8px
- Header: "user_parser.py" — JetBrains Mono, 11px, `#64748B` at 0.5
- Code content: ~20 lines of Python, syntax-highlighted
  - Default: `#E2E8F0` at 0.7
  - Keywords: `#4A90D9` (blue)
  - Strings: `#5AAA6E` (green)
  - Bug line: highlighted with `#EF4444` at 0.08 background, red border-left 2px
- File tab dot: red `#EF4444` indicator (bug present)

#### Test Panel (Right Zone)
- Position: x: 940, y: 80, width: 920, height: 700
- Background: `#1E293B` at 0.3, rounded 8px
- Header: "test_user_parser.py" — JetBrains Mono, 11px, `#64748B` at 0.5
- Existing tests: 4 lines with green `✓` marks, `#5AAA6E` at 0.5
- New test line: appears highlighted with `#D9944A` at 0.08 background

#### Terminal Strip (Bottom Zone)
- Position: x: 60, y: 820, width: 1800, height: 200
- Background: `#0F172A` at 0.6, rounded 8px
- Prompt: `$` — JetBrains Mono, 12px, `#64748B`
- Commands: JetBrains Mono, 13px, `#E2E8F0`
- Output: JetBrains Mono, 11px, `#94A3B8`

#### Annotation
- "Never opened the file." — Inter, 16px, italic, `#E2E8F0` at 0.5
- Position: centered at (480, 760), below code block
- Subtle underline: 1px, `#4A90D9` at 0.15

### Animation Sequence
1. **Frame 0-30 (0-1s):** Layout fades in. Code block visible with bug line highlighted red. Test panel shows 4 existing tests with green checks. Terminal is empty.
2. **Frame 30-70 (1-2.3s):** Terminal: `$ pdd bug user_parser` types in. Output: "Creating failing test..." A new test line appears in the test panel, highlighted amber. The test shows a red `✗` — it's failing.
3. **Frame 70-100 (2.3-3.3s):** Terminal: `$ pdd fix user_parser` types in. Output: "Regenerating..."
4. **Frame 100-160 (3.3-5.3s):** The entire code block dissolves — characters scatter as particles drifting upward, fading. The code panel is briefly empty (just the dark background). Then new code streams in from top to bottom — clean, reformatted, different variable names. The bug line is gone.
5. **Frame 160-200 (5.3-6.7s):** Terminal output: "All tests passing." The new test's `✗` flips to `✓`. All 5 tests now show green checks. A green pulse ripples across the test panel.
6. **Frame 200-250 (6.7-8.3s):** Annotation fades in below the code block: "Never opened the file." The code block's file tab dot changes from red to green.
7. **Frame 250-300 (8.3-10s):** Hold. The regenerated code is clean. The developer never touched it.

### Typography
- File headers: JetBrains Mono, 11px, `#64748B` at 0.5
- Code: JetBrains Mono, 12px, syntax-highlighted
- Terminal commands: JetBrains Mono, 13px, `#E2E8F0`
- Terminal output: JetBrains Mono, 11px, `#94A3B8`
- Annotation: Inter, 16px, italic, `#E2E8F0` at 0.5

### Easing
- Layout fade-in: `easeOut(quad)` over 20 frames
- Terminal type: `linear`, 2 frames per character
- Code dissolve: each character `easeIn(quad)` with staggered 1-frame delays, upward drift
- Code stream-in: `easeOut(quad)` per line, 3-frame stagger between lines
- Test check flip (`✗` → `✓`): `easeOut(back(1.6))` scale bounce, 10 frames
- Annotation fade: `easeOut(quad)` over 18 frames

## Narration Sync
> "Code just got that cheap."

Segment: `closing_002`

- **24:23** ("Code just got that cheap"): Bug visible in code block
- **24:25** (visual: `pdd bug` runs): Failing test created
- **24:27** (visual: `pdd fix` runs): Code dissolves and regenerates
- **24:30** (visual: all tests pass): Green checks, annotation appears
- **24:33** (hold): "Never opened the file" visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0A1628' }}>
    {/* Code block — left zone */}
    <CodePanel x={60} y={80} width={860} height={700}
      file="user_parser.py" language="python"
      bgColor="#1E293B" bgOpacity={0.4} borderRadius={8}>
      <Sequence from={100} durationInFrames={60}>
        <DissolveEffect direction="up" stagger={1}
          easing="easeIn(quad)" />
      </Sequence>
      <Sequence from={130}>
        <StreamIn lines={newCodeLines} lineDelay={3}
          easing="easeOut(quad)" />
      </Sequence>
    </CodePanel>

    {/* Test panel — right zone */}
    <TestPanel x={940} y={80} width={920} height={700}
      file="test_user_parser.py"
      bgColor="#1E293B" bgOpacity={0.3} borderRadius={8}>
      <TestLine text="test_basic_parse" status="pass" />
      <TestLine text="test_empty_input" status="pass" />
      <TestLine text="test_unicode_name" status="pass" />
      <TestLine text="test_max_length" status="pass" />
      <Sequence from={50}>
        <FadeIn duration={12}>
          <TestLine text="test_null_injection"
            status="fail" highlight="#D9944A" />
        </FadeIn>
      </Sequence>
      <Sequence from={160}>
        <FlipStatus testIndex={4} from="fail" to="pass"
          easing="easeOut(back(1.6))" duration={10} />
        <GreenPulse duration={15} />
      </Sequence>
    </TestPanel>

    {/* Terminal strip — bottom */}
    <TerminalStrip x={60} y={820} width={1800} height={200}
      bgColor="#0F172A" bgOpacity={0.6} borderRadius={8}>
      <Sequence from={30}>
        <TerminalCommand command="pdd bug user_parser"
          output="Creating failing test..." charDelay={2} />
      </Sequence>
      <Sequence from={70}>
        <TerminalCommand command="pdd fix user_parser"
          output="Regenerating..." charDelay={2} />
      </Sequence>
      <Sequence from={160}>
        <TerminalOutput text="All tests passing."
          color="#5AAA6E" />
      </Sequence>
    </TerminalStrip>

    {/* Annotation */}
    <Sequence from={200}>
      <FadeIn duration={18}>
        <Text text="Never opened the file."
          font="Inter" size={16} italic
          color="#E2E8F0" opacity={0.5}
          x={480} y={760} align="center" />
        <Line from={[380, 780]} to={[580, 780]}
          color="#4A90D9" opacity={0.15} width={1} />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "terminal_demo",
  "demoId": "closing_regenerate_workflow",
  "zones": {
    "codeBlock": {
      "file": "user_parser.py",
      "language": "python",
      "bugLine": 12,
      "action": "dissolve_and_regenerate"
    },
    "testPanel": {
      "file": "test_user_parser.py",
      "existingTests": 4,
      "newTest": "test_null_injection",
      "finalStatus": "all_pass"
    },
    "terminal": {
      "commands": ["pdd bug user_parser", "pdd fix user_parser"],
      "finalOutput": "All tests passing."
    }
  },
  "annotation": "Never opened the file.",
  "backgroundColor": "#0A1628",
  "narrationSegments": ["closing_002"]
}
```

---
