[Remotion]

# Section 4.5: Minimal Prompt with Test Walls — parser_v2.prompt

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 0:56 - 1:04

## Visual Description

A two-part composition showing a short prompt file surrounded by test walls. This is the visual counterpoint to the previous spec — same parser, radically different approach.

**Upper section:** A small, clean editor window shows `parser_v2.prompt` — just 10 lines. The file is visually compact, with breathing room. A blue glow around the border (contrasting the amber glow of v1). A badge reads "10 lines."

**Lower section:** A terminal window shows `pdd test parser` running. Lines of green checkmarks cascade — "47 tests passing". The terminal pulses with each passing test. Around the prompt file, stylized "wall" lines extend outward from the terminal to frame the prompt — the tests are the walls constraining the output. The walls glow `#4A90D9`.

The visual message: the prompt is tiny because the tests do the precision work.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Prompt Editor (upper)
- Window frame: `#1E293B`, 1px border, rounded 8px corners
- Window position: x: 360, y: 80, 600×280px (compact)
- Title bar: `#151B28`, 36px tall
- Filename: "parser_v2.prompt" — JetBrains Mono, 13px, `#E2E8F0`
- Line count badge: "10 lines" — Inter, 11px, `#4A90D9`, background `#4A90D9` at 0.15
- Content: 10 lines of concise prompt text, JetBrains Mono 13px, `#CBD5E1`
- Border glow: `#4A90D9` at 0.1, 12px blur

#### Terminal Window (lower)
- Window frame: `#1E293B`, 1px border, rounded 8px corners
- Window position: x: 360, y: 420, 600×520px
- Title bar: `#151B28`, 36px, with terminal icon
- Command line: `$ pdd test parser` — JetBrains Mono, 13px, `#5AAA6E`
- Test output rows (cascading):
  - `✓ test_basic_parsing` — `#5AAA6E` at 0.8
  - `✓ test_edge_case_empty_input` — `#5AAA6E` at 0.8
  - (47 lines, scrolling rapidly)
- Summary line: "47 tests passing" — JetBrains Mono, 14px, bold, `#5AAA6E`

#### Test Walls (surrounding prompt)
- 8-12 horizontal/vertical lines radiating from terminal area toward prompt editor
- Color: `#4A90D9` at 0.4, 2px
- Glow on each wall line: `#4A90D9` at 0.15, 6px blur
- These visually "frame" and "constrain" the small prompt — the walls do the work

#### Comparison Label
- Right side: "With tests: prompt specifies only intent" — Inter, 15px, `#4A90D9` at 0.7

### Animation Sequence
1. **Frame 0-30 (0-1s):** Prompt editor fades in at top — compact, clean. Badge appears.
2. **Frame 30-60 (1-2s):** All 10 lines of prompt visible. Breathing room apparent.
3. **Frame 60-120 (2-4s):** Terminal window appears below. `$ pdd test parser` types in. Test results begin cascading — green checkmarks flowing rapidly.
4. **Frame 120-165 (4-5.5s):** Test wall lines draw outward from terminal, framing the prompt editor. Each wall pulses blue on completion. "47 tests passing" summary appears.
5. **Frame 165-210 (5.5-7s):** Comparison label appears. Hold — the visual contrast with v1 is stark.
6. **Frame 210-240 (7-8s):** Hold, begin fade-out.

### Typography
- Filename: JetBrains Mono, 13px, regular (400), `#E2E8F0`
- Badge: Inter, 11px, semi-bold (600), `#4A90D9`
- Prompt text: JetBrains Mono, 13px, regular (400), `#CBD5E1`
- Terminal command: JetBrains Mono, 13px, regular (400), `#5AAA6E`
- Test results: JetBrains Mono, 12px, regular (400), `#5AAA6E` at 0.8
- Summary: JetBrains Mono, 14px, bold (700), `#5AAA6E`
- Label: Inter, 15px, regular (400), `#4A90D9` at 0.7

### Easing
- Editor fade-in: `easeOut(quad)` over 30 frames
- Terminal fade-in: `easeOut(quad)` over 30 frames
- Test cascade: `linear`, 3 results per frame
- Wall draw: `easeOut(cubic)` over 15 frames each, staggered by 5 frames
- Wall glow pulse: `easeOut(quad)` over 10 frames
- Label fade: `easeOut(quad)` over 20 frames

## Narration Sync
> "This is why test accumulation matters. It's not just about catching bugs. It's about making prompts simpler and regeneration safer over time."

Segment: `part4_precision_tradeoff_003` (second half)

- **56.00s**: Prompt editor appears — continuation of "making prompts simpler"
- **58.00s**: Terminal cascade — "regeneration safer over time"
- **62.00s**: Test walls complete, summary visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Prompt editor — compact */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <EditorWindow
          position={{ x: 360, y: 80 }}
          width={600} height={280}
          borderColor="#1E293B"
          glowColor="#4A90D9" glowOpacity={0.1}
        >
          <TitleBar>
            <Filename text="parser_v2.prompt" />
            <Badge text="10 lines" color="#4A90D9" />
          </TitleBar>
          <PromptContent lines={parserV2Lines} />
        </EditorWindow>
      </FadeIn>
    </Sequence>

    {/* Terminal window */}
    <Sequence from={60}>
      <FadeIn duration={30}>
        <TerminalWindow
          position={{ x: 360, y: 420 }}
          width={600} height={520}
        >
          <TypeWriter text="$ pdd test parser"
            color="#5AAA6E" charDelay={1} />
          <Sequence from={30}>
            <TestCascade
              testCount={47}
              checkColor="#5AAA6E"
              ratePerFrame={3}
            />
          </Sequence>
          <Sequence from={90}>
            <FadeIn duration={15}>
              <Text text="47 tests passing"
                font="JetBrains Mono" size={14}
                weight={700} color="#5AAA6E" />
            </FadeIn>
          </Sequence>
        </TerminalWindow>
      </FadeIn>
    </Sequence>

    {/* Test wall lines */}
    <Sequence from={120}>
      <TestWalls
        count={10}
        color="#4A90D9" opacity={0.4}
        glowColor="#4A90D9" glowOpacity={0.15}
        sourceArea={{ x: 360, y: 420, w: 600, h: 520 }}
        targetArea={{ x: 360, y: 80, w: 600, h: 280 }}
        stagger={5} drawDuration={15}
      />
    </Sequence>

    {/* Label */}
    <Sequence from={165}>
      <FadeIn duration={20}>
        <Text text="With tests: prompt specifies only intent"
          font="Inter" size={15} color="#4A90D9" opacity={0.7}
          x={1200} y={500} align="center" />
      </FadeIn>
    </Sequence>

    {/* Fade out */}
    <Sequence from={210}>
      <FadeOut duration={30} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_editor_with_terminal",
  "chartId": "minimal_prompt_with_tests",
  "promptFile": {
    "name": "parser_v2.prompt",
    "lineCount": 10,
    "accentColor": "#4A90D9"
  },
  "terminal": {
    "command": "pdd test parser",
    "testCount": 47,
    "allPassing": true,
    "accentColor": "#5AAA6E"
  },
  "testWalls": {
    "count": 10,
    "color": "#4A90D9",
    "metaphor": "Tests as constraining walls around prompt"
  },
  "narrationSegments": ["part4_precision_tradeoff_003"]
}
```

---
