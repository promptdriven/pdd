[Remotion]

# Section 4.4: Detailed Prompt File — parser_v1.prompt

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 0:48 - 0:56

## Visual Description

A code-editor-style display showing a long, detailed prompt file. The file `parser_v1.prompt` is displayed in a dark editor window with syntax-like highlighting for natural language.

The file header shows the filename and a line count badge: "50 lines". The prompt text scrolls into view, dense with requirements — edge cases, error handling rules, format specifications, type constraints. Each requirement line has a faint amber indicator on its left gutter, emphasizing the sheer volume of specification.

The visual feeling is "heavy" — this prompt is doing all the precision work because there are no test walls to rely on. A subtle amber glow around the file border reinforces this is the "high effort" zone from the previous graph.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Editor Window
- Window frame: `#1E293B`, 1px border, rounded 8px corners
- Window position: centered, 1200×700px
- Title bar: `#151B28`, 36px tall, with traffic-light dots (decorative)
- Filename: "parser_v1.prompt" — JetBrains Mono, 13px, `#E2E8F0`
- Line count badge: "50 lines" — Inter, 11px, `#D9944A`, background `#D9944A` at 0.15, rounded pill

#### Prompt Content
- Font: JetBrains Mono, 13px, `#CBD5E1` at 0.9
- Line numbers: `#64748B` at 0.4, right-aligned in 40px gutter
- Gutter indicators: 3px amber bars (`#D9944A` at 0.5) on left edge of each requirement line
- Content structure (representative):
  - Lines 1-3: Module description header
  - Lines 4-12: Input format specification
  - Lines 13-22: Edge case handling (highlighted amber)
  - Lines 23-35: Error handling rules
  - Lines 36-45: Output format constraints
  - Lines 46-50: Performance requirements

#### Accent
- Window border glow: `#D9944A` at 0.08, 12px blur
- Label below window: "Without tests: prompt must specify everything" — Inter, 15px, `#D9944A` at 0.7

### Animation Sequence
1. **Frame 0-30 (0-1s):** Editor window fades in from dark. Title bar and filename appear.
2. **Frame 30-60 (1-2s):** Line count badge animates in with scale-up. Prompt content begins revealing top-down (like typing or scroll-reveal).
3. **Frame 60-150 (2-5s):** Content continues scrolling/revealing. Gutter indicators light up progressively — each line adds another amber bar. The density becomes apparent.
4. **Frame 150-180 (5-6s):** All 50 lines visible (scrolled or compressed). The amber gutter is a solid wall of requirement indicators.
5. **Frame 180-210 (6-7s):** Label appears below: "Without tests: prompt must specify everything."
6. **Frame 210-240 (7-8s):** Hold briefly, then begin fade for transition.

### Typography
- Filename: JetBrains Mono, 13px, regular (400), `#E2E8F0`
- Line count: Inter, 11px, semi-bold (600), `#D9944A`
- Prompt text: JetBrains Mono, 13px, regular (400), `#CBD5E1` at 0.9
- Line numbers: JetBrains Mono, 12px, regular (400), `#64748B` at 0.4
- Label: Inter, 15px, regular (400), `#D9944A` at 0.7

### Easing
- Window fade-in: `easeOut(quad)` over 30 frames
- Badge scale: `easeOut(back)` 0.8→1.0 over 15 frames
- Content reveal: `linear` scroll, 1.5 lines per frame
- Gutter indicators: `easeOut(quad)` over 4 frames each, staggered
- Label fade-in: `easeOut(quad)` over 20 frames
- Final fade: `easeIn(quad)` over 30 frames

## Narration Sync
> "This is why test accumulation matters. It's not just about catching bugs. It's about making prompts simpler and regeneration safer over time."

Segment: `part4_precision_tradeoff_003` (first half)

- **48.46s** (seg 003): Editor window appears — "This is why test accumulation matters"
- **52.00s**: Content revealing, density apparent — "not just about catching bugs"
- **55.00s**: Label appears — "making prompts simpler"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Editor window */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <EditorWindow
          position={{ x: 360, y: 160 }}
          width={1200} height={700}
          titleBarColor="#151B28"
          borderColor="#1E293B"
          glowColor="#D9944A" glowOpacity={0.08}
          cornerRadius={8}
        >
          <TitleBar>
            <TrafficLights />
            <Filename text="parser_v1.prompt"
              font="JetBrains Mono" size={13} color="#E2E8F0" />
            <Sequence from={30}>
              <ScaleIn from={0.8} duration={15}>
                <Badge text="50 lines" color="#D9944A"
                  bgOpacity={0.15} />
              </ScaleIn>
            </Sequence>
          </TitleBar>

          {/* Prompt content */}
          <Sequence from={30}>
            <ScrollReveal linesPerFrame={1.5}>
              <PromptContent
                lines={parserV1Lines}
                font="JetBrains Mono" size={13}
                textColor="#CBD5E1"
                lineNumberColor="#64748B"
                gutterIndicatorColor="#D9944A"
              />
            </ScrollReveal>
          </Sequence>
        </EditorWindow>
      </FadeIn>
    </Sequence>

    {/* Label */}
    <Sequence from={180}>
      <FadeIn duration={20}>
        <Text text="Without tests: prompt must specify everything"
          font="Inter" size={15} color="#D9944A" opacity={0.7}
          x={960} y={910} align="center" />
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
  "type": "code_editor",
  "chartId": "detailed_prompt_file",
  "file": {
    "name": "parser_v1.prompt",
    "lineCount": 50,
    "sections": [
      { "range": [1, 3], "label": "Module description", "type": "header" },
      { "range": [4, 12], "label": "Input format specification", "type": "spec" },
      { "range": [13, 22], "label": "Edge case handling", "type": "edge_case", "highlight": true },
      { "range": [23, 35], "label": "Error handling rules", "type": "error" },
      { "range": [36, 45], "label": "Output format constraints", "type": "format" },
      { "range": [46, 50], "label": "Performance requirements", "type": "perf" }
    ]
  },
  "accentColor": "#D9944A",
  "label": "Without tests: prompt must specify everything",
  "narrationSegments": ["part4_precision_tradeoff_003"]
}
```

---
