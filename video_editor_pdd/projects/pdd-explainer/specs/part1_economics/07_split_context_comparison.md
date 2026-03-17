[split:]

# Section 1.7: Split Context Comparison — Agentic Patching vs PDD Regeneration

**Tool:** Split
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 4:17 - 4:37

## Visual Description

A vertical split screen contrasts two approaches to using the context window. LEFT panel is labeled "AGENTIC PATCHING" and RIGHT panel "PDD REGENERATION." This is the visual proof of the context window advantage.

**Left panel:** A context window visualization fills with 15,000 tokens of raw code — dense, syntax-highlighted monospace text. Red highlighted sections mark irrelevant code the AI grabbed through retrieval (~40% of the content). A tiny green-highlighted section (~5%) shows the actually relevant code. A label: "15,000 tokens — mostly noise." The window feels cramped, chaotic. A small meter shows "Effective signal: ~5%."

**Right panel:** The same-sized context window contains a clean, readable natural language prompt (~300 tokens), a test file (~2,000 tokens), and a small grounding example (~500 tokens). The content is organized, legible, purposeful. A label: "2,800 tokens — all signal." Abundant whitespace shows room to think. A small meter shows "Effective signal: ~100%."

Below both panels, a comparison line appears: "Same context window. 20× more effective."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.25

### Chart/Visual Elements

#### Panel Headers
- LEFT: "AGENTIC PATCHING" — Inter, 14px, semi-bold (600), `#94A3B8` at 0.5, letter-spacing 2px, centered at y: 40
- RIGHT: "PDD REGENERATION" — Inter, 14px, semi-bold (600), `#4A90D9` at 0.5, letter-spacing 2px, centered at y: 40

#### Left Panel — Code-Filled Context (x: 0 to x: 958)
- Background: `#0F172A`
- **Context window mock:** centered, 420x580, `#1A1A2E` background, 1px `#334155` border
  - Dense monospace code lines filling the entire window — 60+ lines visible
  - Code coloring: keywords `#569CD6` at 0.3, strings `#CE9178` at 0.3, variables `#9CDCFE` at 0.3
  - **Red highlights:** ~12 scattered regions (2-4 lines each), `#EF4444` at 0.06 background — irrelevant retrieved code
  - **Green highlight:** 1 small region (3 lines), `#5AAA6E` at 0.08 background — the actually relevant code
  - The overall impression: dense, noisy, overwhelming
- **Token counter:** "15,000 tokens" — JetBrains Mono, 11px, `#94A3B8`, below window
- **Signal meter:** thin bar, 120px wide, filled 5% with `#5AAA6E`, rest `#334155` at 0.2
  - Label: "Effective signal: ~5%" — Inter, 10px, `#94A3B8` at 0.4
- **Subtitle:** "mostly noise" — Inter, 11px, `#EF4444` at 0.3

#### Right Panel — Prompt-Filled Context (x: 962 to x: 1920)
- Background: `#0A0F1A`
- **Context window mock:** centered, 420x580, `#1A1A2E` background, 1px `#334155` border
  - **Prompt section:** top portion, ~60px tall, `#4A90D9` at 0.04 background
    - Header: "prompt" — JetBrains Mono, 9px, `#4A90D9` at 0.4
    - 6 lines of clean natural language text, Inter, 10px, `#CBD5E1` at 0.5
    - Label: "300 tokens" — Inter, 8px, `#64748B` at 0.3
  - **Tests section:** middle portion, ~120px tall, `#D9944A` at 0.04 background
    - Header: "tests" — JetBrains Mono, 9px, `#D9944A` at 0.4
    - 12 lines of test assertions, JetBrains Mono, 9px, `#D9944A` at 0.3
    - Label: "2,000 tokens" — Inter, 8px, `#64748B` at 0.3
  - **Grounding section:** small portion, ~40px tall, `#5AAA6E` at 0.04 background
    - Header: "grounding" — JetBrains Mono, 9px, `#5AAA6E` at 0.4
    - 4 lines of example code, JetBrains Mono, 9px, `#5AAA6E` at 0.3
    - Label: "500 tokens" — Inter, 8px, `#64748B` at 0.3
  - **Remaining space:** abundant whitespace, `#1A1A2E`, labeled "room to think" in faint italic
- **Token counter:** "2,800 tokens" — JetBrains Mono, 11px, `#4A90D9`, below window
- **Signal meter:** thin bar, 120px wide, filled 100% with `#5AAA6E`
  - Label: "Effective signal: ~100%" — Inter, 10px, `#5AAA6E` at 0.5
- **Subtitle:** "all signal" — Inter, 11px, `#5AAA6E` at 0.4

#### Comparison Label
- Position: centered at y: 960
- Text: "Same context window. 20× more effective."
- Inter, 20px, semi-bold (600), `#E2E8F0`
- Background pill: `#1E293B` at 0.3, rounded 10px, padding 14px

### Animation Sequence
1. **Frame 0-30 (0-1s):** Split line draws. Panel headers appear.
2. **Frame 30-120 (1-4s):** Left panel: code lines flood in rapidly — line by line, filling the window. Dense, overwhelming. Token counter ticks up to "15,000."
3. **Frame 120-210 (4-7s):** Left panel: red highlights flash on — one by one, scattered through the code. Green highlight appears — tiny, almost lost. Signal meter fills to 5%.
4. **Frame 210-330 (7-11s):** Right panel: prompt section slides in from top — clean, readable. Tests section appears below — organized. Grounding section appears — small. "Room to think" whitespace is conspicuous. Token counter shows "2,800."
5. **Frame 330-390 (11-13s):** Right panel: signal meter fills to 100%. The contrast with the left panel's 5% is stark.
6. **Frame 390-480 (13-16s):** Both panels hold. The viewer's eye goes back and forth. The argument is visual.
7. **Frame 480-540 (16-18s):** Comparison label slides up from bottom: "Same context window. 20× more effective."
8. **Frame 540-600 (18-20s):** Hold.

### Typography
- Panel headers: Inter, 14px, semi-bold (600), respective colors, letter-spacing 2px
- Code text: JetBrains Mono, 9-10px, various syntax colors at low opacity
- Section headers: JetBrains Mono, 9px, respective PDD colors at 0.4
- Token counters: JetBrains Mono, 11px, respective colors
- Signal labels: Inter, 10px, respective colors
- Comparison text: Inter, 20px, semi-bold (600), `#E2E8F0`

### Easing
- Split line draw: `easeOut(cubic)` over 15 frames
- Code flood: `easeOut(quad)`, 1-frame stagger per line
- Red highlight flash: `easeOut(quad)` over 8 frames, 4-frame stagger per region
- Prompt section slide: `easeOut(cubic)` from y-20, 20 frames
- Signal meter fill: `easeOut(quad)` over 25 frames
- Comparison label slide: `easeOut(cubic)` from y+20, 25 frames

## Narration Sync
> "Regeneration doesn't have this problem. A prompt is a fifth to a tenth the size of the code it governs. So where raw code overwhelms the context window, the prompts for ten modules fit comfortably."
> "And the prompt defines its own context—the developer declares exactly what the model needs to see, instead of an agentic tool guessing at what's relevant. No retrieval. No search. No rot."
> "And there's something else. These models are trained on up to thirty times more natural language than code. Natural language is their deepest fluency."

Segment: `part1_007`

- **4:17** ("Regeneration doesn't have this problem"): Split screen appears
- **4:21** ("raw code overwhelms the context window"): Left panel fills with dense code
- **4:25** ("the prompts for ten modules fit comfortably"): Right panel shows clean prompt content
- **4:30** ("the developer declares exactly what the model needs"): Signal meters contrast visible
- **4:34** ("Natural language is their deepest fluency"): Comparison label appears

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Agentic patching */}
    <Panel x={0} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
        <PanelHeader text="AGENTIC PATCHING" color="#94A3B8"
          opacity={0.5} letterSpacing={2} y={40} />

        <ContextWindowMock position={[240, 340]} size={[420, 580]}>
          <Sequence from={30}>
            <CodeFlood lineCount={65}
              syntaxColors={{ keyword: '#569CD6', string: '#CE9178', variable: '#9CDCFE' }}
              lineDelay={1} opacity={0.3} />
          </Sequence>
          <Sequence from={120}>
            <RetrievalHighlights
              red={{ regions: 12, linesEach: [2,4], color: '#EF4444', opacity: 0.06 }}
              green={{ regions: 1, linesEach: [3], color: '#5AAA6E', opacity: 0.08 }}
              staggerDelay={4}
            />
          </Sequence>
        </ContextWindowMock>

        <TokenCounter value={15000} color="#94A3B8" y={680} />
        <SignalMeter fill={0.05} color="#5AAA6E" bgColor="#334155"
          label="Effective signal: ~5%" y={720} />
      </AbsoluteFill>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.25} drawDuration={15} />

    {/* Right panel — PDD regeneration */}
    <Panel x={962} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
        <PanelHeader text="PDD REGENERATION" color="#4A90D9"
          opacity={0.5} letterSpacing={2} y={40} />

        <Sequence from={210}>
          <ContextWindowMock position={[240, 340]} size={[420, 580]}>
            <PromptSection lines={6} tokens={300} color="#4A90D9" />
            <TestsSection lines={12} tokens={2000} color="#D9944A" />
            <GroundingSection lines={4} tokens={500} color="#5AAA6E" />
            <WhitespaceLabel text="room to think" />
          </ContextWindowMock>
        </Sequence>

        <Sequence from={330}>
          <TokenCounter value={2800} color="#4A90D9" y={680} />
          <SignalMeter fill={1.0} color="#5AAA6E"
            label="Effective signal: ~100%" y={720} />
        </Sequence>
      </AbsoluteFill>
    </Panel>

    {/* Comparison label */}
    <Sequence from={480}>
      <SlideUp distance={20} duration={25}>
        <PillLabel
          text="Same context window. 20× more effective."
          font="Inter" size={20} weight={600}
          color="#E2E8F0" bgColor="#1E293B"
          x={960} y={960}
        />
      </SlideUp>
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
    "label": "AGENTIC PATCHING",
    "tokenCount": 15000,
    "effectiveSignal": 0.05,
    "contentType": "raw_code",
    "irrelevantRegions": 12,
    "relevantRegions": 1,
    "background": "#0F172A"
  },
  "rightPanel": {
    "label": "PDD REGENERATION",
    "tokenCount": 2800,
    "effectiveSignal": 1.0,
    "contentSections": [
      { "type": "prompt", "tokens": 300, "color": "#4A90D9" },
      { "type": "tests", "tokens": 2000, "color": "#D9944A" },
      { "type": "grounding", "tokens": 500, "color": "#5AAA6E" }
    ],
    "background": "#0A0F1A"
  },
  "comparison": "Same context window. 20× more effective.",
  "backgroundColor": "#000000",
  "narrationSegments": ["part1_007"]
}
```

---
