[Remotion]

# Section 7.2: Code Regenerate Workflow — Bug → Test → Regenerate

**Tool:** Remotion
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:03 - 0:09

## Visual Description

A stylized code editor fills the screen. A function is visible with a subtle red highlight indicating a bug. A developer cursor moves — but instead of editing the buggy line, a new test appears below the code: `test_edge_case`. The terminal at the bottom of screen runs `pdd bug → pdd fix → ✓`. The code dissolves and regenerates clean. All green checkmarks.

The visual message: you don't fix code, you constrain the mold and regenerate.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none

### Chart/Visual Elements

#### Code Editor Panel
- Position: (120, 80) to (1800, 680)
- Background: `#0F1629` at 0.9
- Border: 1px `#1E293B`
- Border radius: 8px
- Code font: JetBrains Mono, 14px, `#E2E8F0`

#### Code Content
- Function: ~12 lines of Python-like pseudocode
- Bug highlight: line 7, background `#F5240B` at 0.08, left border 3px `#EF4444`
- Keywords: `#A78BFA` (purple)
- Strings: `#4ADE80` (green)
- Comments: `#64748B`

#### New Test (appears)
- Position: below function, line 14-16
- Test name: `test_edge_case` — JetBrains Mono, 14px, `#4ADE80`
- Glow on appearance: `#4ADE80` at 0.15

#### Terminal Strip
- Position: (120, 720) to (1800, 960)
- Background: `#0A0E17`
- Border: 1px `#1E293B`
- Font: JetBrains Mono, 13px, `#94A3B8`
- Commands appear sequentially:
  - `$ pdd bug user_parser` — `#94A3B8`
  - `$ pdd fix user_parser` — `#94A3B8`
  - `✓ All tests passing` — `#4ADE80`, bold

### Animation Sequence
1. **Frame 0-30 (0-1s):** Code editor visible with bug-highlighted line. Terminal empty.
2. **Frame 30-60 (1-2s):** Bug line pulses red briefly. New test `test_edge_case` fades in below the code with green glow. `easeOut(quad)`.
3. **Frame 60-90 (2-3s):** Terminal: `$ pdd bug user_parser` types in. Brief pause. `$ pdd fix user_parser` appears.
4. **Frame 90-120 (3-4s):** Code dissolves — all lines fade to 0.05 opacity, then new code fades in. Bug line is gone. Clean code. `easeInOut(cubic)`.
5. **Frame 120-150 (4-5s):** `✓ All tests passing` appears in terminal in green. Test line glows briefly.
6. **Frame 150-180 (5-6s):** Hold on clean state. Gentle pulse on checkmark.

### Typography
- Code: JetBrains Mono, 14px, regular (400)
- Terminal: JetBrains Mono, 13px, regular (400)
- Test pass: JetBrains Mono, 13px, bold (700), `#4ADE80`

### Easing
- Bug pulse: `easeInOut(sine)` over 15 frames
- Test appear: `easeOut(quad)` over 20 frames
- Code dissolve: `easeInOut(cubic)` over 20 frames
- Code regenerate: `easeOut(cubic)` over 20 frames
- Terminal text: `linear` (instant per line, 15 frame delay between)
- Checkmark: `easeOut(back)` over 10 frames

## Narration Sync
> "Code just got that cheap."

Segment: `closing_001` (tail) → `closing_002` (start)

- **0:03** ("Code"): Code editor visible, bug line highlighted
- **0:04** ("just got"): Test appears, terminal starts
- **0:06** ("that cheap"): Code dissolves and regenerates clean
- **0:08** (hold): All tests passing, clean state

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Code editor panel */}
    <CodeEditor
      x={120} y={80} width={1680} height={600}
      bg="#0F1629" borderColor="#1E293B"
      font="JetBrains Mono" fontSize={14}
    >
      {/* Bug highlight */}
      <Sequence from={0} durationInFrames={90}>
        <CodeLine line={7} highlight={{ bg: "#F5240B0A", border: "#EF4444" }} />
      </Sequence>

      {/* New test appears */}
      <Sequence from={30}>
        <FadeIn duration={20}>
          <CodeBlock startLine={14} content={TEST_CODE}
            glowColor="#4ADE80" glowOpacity={0.15} />
        </FadeIn>
      </Sequence>

      {/* Code dissolve and regenerate */}
      <Sequence from={90}>
        <DissolveRegenerate
          dissolveDuration={20} regenDuration={20}
          oldCode={BUGGY_CODE} newCode={CLEAN_CODE} />
      </Sequence>
    </CodeEditor>

    {/* Terminal strip */}
    <TerminalStrip x={120} y={720} width={1680} height={240}
      bg="#0A0E17" borderColor="#1E293B"
      font="JetBrains Mono" fontSize={13}>
      <Sequence from={60}>
        <TerminalLine text="$ pdd bug user_parser" color="#94A3B8" />
      </Sequence>
      <Sequence from={75}>
        <TerminalLine text="$ pdd fix user_parser" color="#94A3B8" />
      </Sequence>
      <Sequence from={120}>
        <TerminalLine text="✓ All tests passing" color="#4ADE80" weight={700} />
      </Sequence>
    </TerminalStrip>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_animation",
  "chartId": "code_regenerate_workflow",
  "phases": [
    { "id": "bug_highlight", "frame": 0, "description": "Buggy code with red highlight on line 7" },
    { "id": "test_add", "frame": 30, "description": "New test_edge_case fades in" },
    { "id": "terminal_commands", "frame": 60, "description": "pdd bug → pdd fix sequence" },
    { "id": "dissolve_regen", "frame": 90, "description": "Code dissolves, regenerates clean" },
    { "id": "all_pass", "frame": 120, "description": "All tests passing checkmark" }
  ],
  "terminalCommands": ["pdd bug user_parser", "pdd fix user_parser", "✓ All tests passing"],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["closing_001", "closing_002"]
}
```

---
