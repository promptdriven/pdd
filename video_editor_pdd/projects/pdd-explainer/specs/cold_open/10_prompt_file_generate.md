[Remotion]

# Section 0.10: Prompt File and Code Generation

**Tool:** Remotion
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:33 - 0:39

## Visual Description

Clean terminal on a dark background. A file labeled `email_validator.prompt` appears — about 15 lines of natural language. The text is clear, readable, and obviously human-written: plain English describing what an email validator should do, what edge cases to handle, what the output format should be.

After the prompt file is visible and the viewer has a beat to read it, the terminal runs `pdd generate email_validator`. Code flows out on the right side (or below, split-pane style) — roughly 200 lines of clean, formatted, complete Python code. The generation is rapid and satisfying. The visual contrast is stark: 15 lines of intent → 200 lines of implementation.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (GitHub dark theme)
- Layout: Left pane (prompt file, 45% width) / Right pane (generated code, 55% width)
- Divider: `#30363D`, 1px, vertical

### Chart/Visual Elements

#### Left Pane — Prompt File
- File tab: `email_validator.prompt` with document icon, `#E2E8F0` on `#161B22`
- Content: 15 lines of natural language, Inter 15px, `#C9D1D9`
- Key lines highlighted with subtle left-border: `#4A90D9` at 0.3, 3px

#### Right Pane — Generated Code
- File tab: `email_validator.py` with Python icon, `#E2E8F0` on `#161B22`
- Content: Python code, JetBrains Mono 14px
- Keywords: `#C792EA`, Strings: `#C3E88D`, Functions: `#82AAFF`
- Line count indicator bottom-right: "200 lines" in `#4ADE80`

#### Terminal Bar (bottom)
- Height: 48px, background `#0D1117`
- Command: `$ pdd generate email_validator` → `✓ Generated 200 lines (0.8s)`
- Font: JetBrains Mono, 13px

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Left pane fades in with prompt file content. File tab appears.
2. **Frame 20-60 (0.67-2s):** Prompt content types in line by line — readable pace (3 frames per line). Highlighted lines get their blue left-border.
3. **Frame 60-80 (2-2.67s):** Terminal bar appears at bottom. Command types: `pdd generate email_validator`.
4. **Frame 80-90 (2.67-3s):** Right pane activates. Divider slides in. `email_validator.py` tab appears.
5. **Frame 90-150 (3-5s):** Generated code flows into right pane — rapid typewriter (0.3 frames per line). Scrolling effect as 200 lines stream in.
6. **Frame 150-180 (5-6s):** Hold. "200 lines" counter fades in at bottom-right of code pane. Terminal shows green checkmark.

### Typography
- Prompt text: Inter, 15px, regular (400), `#C9D1D9`
- Code: JetBrains Mono, 14px, regular (400)
- Terminal: JetBrains Mono, 13px, `#94A3B8`
- Line counter: JetBrains Mono, 13px, bold, `#4ADE80`

### Easing
- Pane fade-in: `easeOut(quad)` over 20 frames
- Prompt typewriter: linear, 3 frames per line
- Code flow: linear, 0.3 frames per line (rapid)
- Divider slide: `easeOut(cubic)` over 10 frames
- Counter fade-in: `easeOut(quad)` over 15 frames

## Narration Sync
> "15 lines of prompt, 200 lines of clean code."

Segment: `cold_open_008` (continued from spec 08/09)

- **32.88s** (seg 009 begins, but visual aligns with tail of 008): Prompt file appears
- **34.00s**: Prompt content visible, generation command runs
- **36.00s**: Code flowing into right pane
- **38.50s**: Generation complete, 200 lines visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Left pane: prompt file */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <Pane width="45%" side="left">
          <FileTab name="email_validator.prompt" icon="doc" />
          <TypewriterText
            lines={promptFileLines}
            font="Inter" size={15} color="#C9D1D9"
            lineDelay={3}
            highlightLines={[2, 5, 8, 11]}
            highlightBorder={{ color: "#4A90D9", opacity: 0.3, width: 3 }}
          />
        </Pane>
      </FadeIn>
    </Sequence>

    {/* Divider */}
    <Sequence from={80}>
      <SlideIn direction="left" duration={10}>
        <VerticalDivider color="#30363D" width={1} />
      </SlideIn>
    </Sequence>

    {/* Right pane: generated code */}
    <Sequence from={80}>
      <FadeIn duration={10}>
        <Pane width="55%" side="right">
          <FileTab name="email_validator.py" icon="python" />
          <Sequence from={10}>
            <RapidCodeFlow
              code={generatedCode}
              font="JetBrains Mono" size={14}
              lineDelay={0.3}
              scrollable
            />
          </Sequence>
        </Pane>
      </FadeIn>
    </Sequence>

    {/* Line counter */}
    <Sequence from={150}>
      <FadeIn duration={15}>
        <Badge text="200 lines" color="#4ADE80"
          position={{ x: 1860, y: 1020 }} align="right" />
      </FadeIn>
    </Sequence>

    {/* Terminal bar */}
    <Sequence from={60}>
      <TerminalBar
        command="pdd generate email_validator"
        result="✓ Generated 200 lines (0.8s)"
        resultColor="#4ADE80"
        typeDelay={2}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_generation_demo",
  "layout": "split_pane",
  "leftPane": {
    "file": "email_validator.prompt",
    "lineCount": 15,
    "contentType": "natural_language"
  },
  "rightPane": {
    "file": "email_validator.py",
    "lineCount": 200,
    "contentType": "python"
  },
  "ratio": "15:200",
  "terminal": {
    "command": "pdd generate email_validator",
    "result": "Generated 200 lines (0.8s)"
  },
  "narrationSegments": ["cold_open_008", "cold_open_009"]
}
```

---
