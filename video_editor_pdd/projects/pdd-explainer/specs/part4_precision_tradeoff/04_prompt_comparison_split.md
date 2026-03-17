[split:]

# Section 4.4: Prompt Comparison — Dense vs Minimal Prompt Files

**Tool:** Split
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 19:09 - 19:23

## Visual Description

A vertical split screen shows two concrete prompt file examples side by side, making the precision tradeoff tangible. LEFT panel shows a long, detailed prompt file (`parser_v1.prompt` — 50 lines). RIGHT panel shows a short, minimal prompt file (`parser_v2.prompt` — 10 lines) surrounded by a dense wall of passing tests.

LEFT panel: The prompt document fills most of the space. It's clearly visible as a `.prompt` file in an editor-like view. The text is dense — edge case after edge case, explicit error handling instructions, exact behavioral specifications. A line counter on the left margin shows ~50 lines. The file is overwhelming. A subtle red-amber tint suggests effort and fragility.

RIGHT panel: The prompt document is compact — just a few lines of clear intent. But below it, a terminal window shows `pdd test parser` with 47 green checkmarks scrolling by. The wall icons from the previous visualization reappear around the prompt, now larger and more prominent. The prompt is minimal because the tests carry the precision. A green tint suggests safety and confidence.

Both panels then show identical generated code flowing out, emphasizing that the outputs are equivalent — the difference is only in how the specification is expressed.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x=960, color `#334155` at 0.25

### Chart/Visual Elements

#### Panel Headers
- LEFT: "FEW TESTS" — Inter, 14px, semi-bold (600), `#D9944A` at 0.5, letter-spacing 2px, centered at y: 30
- RIGHT: "MANY TESTS" — Inter, 14px, semi-bold (600), `#5AAA6E` at 0.5, letter-spacing 2px, centered at y: 30

#### Left Panel — Dense Prompt (x: 0 to x: 958)
- Background: `#0F172A`
- **File header bar:** 30px tall, `#1E293B`, with filename `parser_v1.prompt` in JetBrains Mono, 11px, `#4A90D9` at 0.7
- **Line numbers:** 1-50, JetBrains Mono, 10px, `#64748B` at 0.3, left gutter 40px
- **Prompt content:** JetBrains Mono, 10px, `#CBD5E1` at 0.7
  - Lines 1-5: "Parse user IDs from untrusted input..." (intent)
  - Lines 6-15: "Handle null input by returning None..." (explicit null handling)
  - Lines 16-25: "For unicode characters, normalize to NFC..." (unicode edge cases)
  - Lines 26-35: "Error conditions: ValueError for malformed..." (error handling)
  - Lines 36-45: "Performance: must process 10k IDs in < 100ms..." (performance constraints)
  - Lines 46-50: "Return type: Optional[str], never throw..." (return contract)
- **Line count badge:** "50 lines" — Inter, 12px, bold (700), `#D9944A` at 0.6, bottom-right

#### Right Panel — Minimal Prompt + Tests (x: 962 to x: 1920)
- Background: `#0A0F1A`
- **File header bar:** 30px tall, `#1E293B`, with filename `parser_v2.prompt` in JetBrains Mono, 11px, `#4A90D9` at 0.7
- **Line numbers:** 1-10, JetBrains Mono, 10px, `#64748B` at 0.3
- **Prompt content:** JetBrains Mono, 10px, `#CBD5E1` at 0.7
  - Lines 1-3: "Parse user IDs from untrusted input."
  - Lines 4-6: "Return None on failure, never throw."
  - Lines 7-8: "Handle unicode."
  - Lines 9-10: "Latency < 100ms for batch of 10k."
- **Line count badge:** "10 lines" — Inter, 12px, bold (700), `#5AAA6E` at 0.6, below prompt
- **Terminal window:** below prompt, dark background `#0F172A`, 300px tall
  - Header: `pdd test parser` in JetBrains Mono, 11px, `#94A3B8`
  - Scrolling output: 47 lines of "✓ test_name" in JetBrains Mono, 9px, `#5AAA6E` at 0.7
  - Final line: "47 passed ✓" in Inter, 12px, bold (700), `#5AAA6E`

#### Code Output (bottom, y: 850-1000, spans both panels)
- After both panels are shown, identical code blocks emerge from each side
- Code: 5 visible lines of Python, JetBrains Mono, 9px, `#94A3B8` at 0.3
- Label centered: "Same output. Different specification strategy." — Inter, 13px, `#E2E8F0` at 0.5

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Split line draws. Panel headers fade in.
2. **Frame 20-90 (0.67-3s):** LEFT: File header appears. Prompt text scrolls in from top, line by line. Line numbers populate. Dense. RIGHT: File header appears. Prompt text appears — only 10 lines, quick.
3. **Frame 90-150 (3-5s):** LEFT: Still scrolling — lines 20, 30, 40 appearing. The density is visible. "50 lines" badge appears. RIGHT: Terminal window opens below the prompt.
4. **Frame 150-280 (5-9.3s):** LEFT: Full prompt visible, stationary. RIGHT: Terminal shows `pdd test parser` command. Test results scroll in rapidly — green checkmarks accumulating. "✓ test_null_input", "✓ test_unicode_nfc", "✓ test_empty_string"...
5. **Frame 280-330 (9.3-11s):** RIGHT: "47 passed ✓" appears at bottom of terminal. The contrast: 10-line prompt + 47 tests = same safety as 50-line prompt.
6. **Frame 330-370 (11-12.3s):** Code output blocks fade in at bottom of both panels. Identical-looking code. Center label appears.
7. **Frame 370-420 (12.3-14s):** Hold. Both panels visible. The economy of the right approach is stark.

### Typography
- Panel headers: Inter, 14px, semi-bold (600), respective colors, letter-spacing 2px
- File headers: JetBrains Mono, 11px, `#4A90D9` at 0.7
- Prompt text: JetBrains Mono, 10px, `#CBD5E1` at 0.7
- Line numbers: JetBrains Mono, 10px, `#64748B` at 0.3
- Test output: JetBrains Mono, 9px, `#5AAA6E` at 0.7
- Badge/counter: Inter, 12px, bold (700), respective colors
- Bottom label: Inter, 13px, `#E2E8F0` at 0.5

### Easing
- Split line draw: `easeOut(cubic)` over 15 frames
- Prompt scroll: `linear`, 1.5 lines per frame (left), instant (right)
- Terminal scroll: `linear`, 3 results per frame
- Code output fade: `easeOut(quad)` over 20 frames
- Badge appear: `spring({ stiffness: 200, damping: 12 })`

## Narration Sync
> "With few tests, your prompt needs to specify everything. Edge cases. Error handling. Exact behavior in every situation."
> "With many tests, the prompt only needs to specify intent. The tests handle the constraints."

Segments: `part4_precision_tradeoff_005`, `part4_precision_tradeoff_006`

- **30.1s** ("With few tests, your prompt needs to specify everything"): Left panel dense prompt scrolling in
- **34.28s** ("Edge cases"): Line 16+ visible — unicode edge cases
- **35.72s** ("Error handling"): Line 26+ visible — error conditions
- **37.24s** ("Exact behavior in every situation"): Full 50-line prompt shown
- **40.7s** ("With many tests"): Right panel terminal opens
- **42.44s** ("the prompt only needs to specify intent"): 10-line prompt visible
- **45.2s** ("The tests handle the constraints"): 47 tests scrolling through

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Dense Prompt */}
    <Panel x={0} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
        <PanelHeader text="FEW TESTS" color="#D9944A"
          opacity={0.5} letterSpacing={2} y={30} />
        <FileHeader filename="parser_v1.prompt" color="#4A90D9" y={60} />
        <Sequence from={20}>
          <ScrollingCodeBlock
            lines={densePromptLines} lineHeight={16}
            font="JetBrains Mono" fontSize={10}
            color="#CBD5E1" lineNumberColor="#64748B"
            scrollSpeed={1.5} y={90} />
        </Sequence>
        <Sequence from={90}>
          <SpringScale stiffness={200} damping={12}>
            <Badge text="50 lines" color="#D9944A" x={880} y={830} />
          </SpringScale>
        </Sequence>
      </AbsoluteFill>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.25} drawDuration={15} />

    {/* Right panel — Minimal Prompt + Tests */}
    <Panel x={962} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
        <PanelHeader text="MANY TESTS" color="#5AAA6E"
          opacity={0.5} letterSpacing={2} y={30} />
        <FileHeader filename="parser_v2.prompt" color="#4A90D9" y={60} />
        <Sequence from={20}>
          <CodeBlock lines={minimalPromptLines} lineHeight={16}
            font="JetBrains Mono" fontSize={10}
            color="#CBD5E1" lineNumberColor="#64748B" y={90} />
        </Sequence>
        <Sequence from={90}>
          <Badge text="10 lines" color="#5AAA6E" x={880} y={280} />
        </Sequence>
        <Sequence from={150}>
          <TerminalWindow y={330} height={300}
            command="pdd test parser" commandColor="#94A3B8">
            <ScrollingTestResults
              results={testResults47}
              checkColor="#5AAA6E" font="JetBrains Mono" fontSize={9}
              scrollSpeed={3} />
            <Sequence from={130}>
              <Text text="47 passed ✓" font="Inter" size={12}
                weight={700} color="#5AAA6E"
                x={480} y={280} align="center" />
            </Sequence>
          </TerminalWindow>
        </Sequence>
      </AbsoluteFill>
    </Panel>

    {/* Bottom — identical code output */}
    <Sequence from={330}>
      <FadeIn duration={20}>
        <CodeOutputPreview y={870}
          leftCode={generatedCode} rightCode={generatedCode}
          font="JetBrains Mono" fontSize={9} color="#94A3B8" opacity={0.3} />
        <Text text="Same output. Different specification strategy."
          font="Inter" size={13} color="#E2E8F0" opacity={0.5}
          x={960} y={980} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_split",
  "splitPosition": 960,
  "leftPanel": {
    "label": "FEW TESTS",
    "filename": "parser_v1.prompt",
    "lineCount": 50,
    "concept": "Prompt must specify everything — edge cases, errors, constraints",
    "background": "#0F172A",
    "accentColor": "#D9944A"
  },
  "rightPanel": {
    "label": "MANY TESTS",
    "filename": "parser_v2.prompt",
    "lineCount": 10,
    "testCount": 47,
    "concept": "Prompt only needs intent — tests carry the precision",
    "background": "#0A0F1A",
    "accentColor": "#5AAA6E",
    "terminalCommand": "pdd test parser"
  },
  "callout": "Same output. Different specification strategy.",
  "backgroundColor": "#000000",
  "narrationSegments": ["part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]
}
```

---
