[split:]

# Section 3.15: Context Window Comparison — Code vs Prompts

**Tool:** Split
**Duration:** ~24s (720 frames @ 30fps)
**Timestamp:** 3:28 - 3:52

## Visual Description

Two context windows side by side, identical in physical size but dramatically different in content density and readability.

**LEFT — "Raw Code Context":** A context window filled with 15,000 tokens of dense code. Syntax-highlighted but overwhelming — tiny font, no natural language, pure implementation. Variables, brackets, function bodies. A label: "15,000 tokens of code" and below: "1 module's implementation." The text is cramped, hard to parse, visually noisy.

**RIGHT — "Prompt Context":** The same-sized window filled with prompts for ten modules. Clean natural language, clear intent statements, readable at a glance. Each prompt is separated by a divider. A label: "15,000 tokens of prompts" and below: "10 modules' specifications." The text is clean, spacious, immediately comprehensible.

A multiplier appears between them: "10×" — the right window represents ten times more system knowledge. Below: "Every token is author-curated. No retrieval guessing. No wasted space."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.15

### Chart/Visual Elements

#### Left Panel — Raw Code
- Header: "RAW CODE CONTEXT" — Inter, 16px, bold, `#94A3B8` at 0.5, y: 60
- Context window: 850×700px, bg `#1E1E2E`, border `#334155` at 0.3, rounded 6px
- Content: dense syntax-highlighted code, JetBrains Mono, 7px — intentionally hard to read
- Token count: "15,000 tokens" — Inter, 14px, bold, `#94A3B8` at 0.6, y: 820
- Scope: "1 module's implementation" — Inter, 12px, `#94A3B8` at 0.4, y: 845
- Overall mood: overwhelming, noisy

#### Right Panel — Prompt Space
- Header: "PROMPT CONTEXT" — Inter, 16px, bold, `#2DD4BF` at 0.7, y: 60
- Context window: 850×700px, bg `#0F1E1E`, border `#2DD4BF` at 0.3, rounded 6px
- Content: 10 prompt blocks, each 5-8 lines, separated by thin dividers
  - Each block starts with module name in bold, followed by natural language
  - Font: Inter, 11px, `#2DD4BF` at 0.5
  - Clean, readable, spacious line height
- Token count: "15,000 tokens" — Inter, 14px, bold, `#2DD4BF` at 0.6, y: 820
- Scope: "10 modules' specifications" — Inter, 12px, `#2DD4BF` at 0.5, y: 845
- Overall mood: clean, comprehensible, curated

#### Multiplier
- "10×" — Inter, 64px, bold, `#2DD4BF` at 0.7, centered at (960, 540)
- Appears between the panels on top of split line
- Glow: `#2DD4BF` at 0.1, 20px radius

#### Bottom Statement
- "Every token is author-curated. No retrieval guessing. No wasted space." — Inter, 14px, `#E2E8F0` at 0.6, centered at y: 920
- "The entire context window is devoted to your problem." — Inter, 14px, bold, `#2DD4BF` at 0.6, y: 950

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split line fades in.
2. **Frame 15-120 (0.5-4s):** Left panel: code context fills in rapidly. Dense, overwhelming. Header appears.
3. **Frame 120-240 (4-8s):** Right panel: prompt context fills in cleanly. Each prompt block appears. Header appears.
4. **Frame 240-360 (8-12s):** Token counts appear on both sides — same number. Scope labels appear — dramatically different.
5. **Frame 360-480 (12-16s):** "10×" multiplier appears at center with glow bloom. The implication lands.
6. **Frame 480-600 (16-20s):** Left panel dims to 0.3. Right panel brightens. The preference is clear.
7. **Frame 600-720 (20-24s):** Bottom statement appears. Hold.

### Typography
- Headers: Inter, 16px, bold (700), respective colors
- Code: JetBrains Mono, 7px, syntax-highlighted (intentionally small)
- Prompts: Inter, 11px, `#2DD4BF` at 0.5
- Token counts: Inter, 14px, bold (700)
- Multiplier: Inter, 64px, bold (700), `#2DD4BF`
- Bottom text: Inter, 14px, `#E2E8F0` / `#2DD4BF`

### Easing
- Split line: `easeOut(quad)` over 15 frames
- Code fill: linear rapid scroll, 0.5s to fill
- Prompt fill: `easeOut(quad)` per block, staggered 10 frames
- Token counts: `easeOut(quad)` over 15 frames
- "10×" bloom: `easeOut(back)` over 20 frames
- Panel dim/brighten: `easeOut(cubic)` over 30 frames
- Statement: `easeOut(quad)` over 20 frames

## Narration Sync
> "This is why the context window advantage we talked about is so powerful. You're not stuffing code into a window and hoping the model figures it out. You're giving it natural language — its strongest modality — in a window that's five to ten times more spacious. And every token is author-curated. No retrieval guessing. No wasted space. The entire context window is devoted to your problem."

Segment: `part3_mold_has_three_parts_022`

- **3:28** ("context window advantage"): Both panels begin filling
- **3:36** ("natural language"): Right panel prominent, left dimming
- **3:44** ("five to ten times"): "10×" multiplier appears
- **3:49** ("every token is author-curated"): Bottom statement

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={720}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Left panel — Raw Code */}
    <Panel x={0} width={958}>
      <FadeIn duration={15}>
        <Text text="RAW CODE CONTEXT" font="Inter" size={16}
          weight={700} color="#94A3B8" opacity={0.5}
          x={479} y={60} align="center" />
      </FadeIn>
      <Sequence from={15}>
        <ContextWindow x={55} y={90} width={850} height={700}
          bg="#1E1E2E" border="#334155"
          content="dense_code" font="JetBrains Mono" fontSize={7}
          fillSpeed="rapid" />
      </Sequence>
      <Sequence from={240}>
        <FadeIn duration={15}>
          <Text text="15,000 tokens" font="Inter" size={14}
            weight={700} color="#94A3B8" opacity={0.6}
            x={479} y={820} align="center" />
          <Text text="1 module's implementation" font="Inter" size={12}
            color="#94A3B8" opacity={0.4}
            x={479} y={845} align="center" />
        </FadeIn>
      </Sequence>
    </Panel>

    {/* Split divider */}
    <FadeIn duration={15}>
      <SplitLine x={960} color="#334155" opacity={0.15} width={2} />
    </FadeIn>

    {/* Right panel — Prompt Space */}
    <Panel x={962} width={958}>
      <FadeIn duration={15}>
        <Text text="PROMPT CONTEXT" font="Inter" size={16}
          weight={700} color="#2DD4BF" opacity={0.7}
          x={479} y={60} align="center" />
      </FadeIn>
      <Sequence from={120}>
        <ContextWindow x={55} y={90} width={850} height={700}
          bg="#0F1E1E" border="#2DD4BF"
          content="prompt_blocks" font="Inter" fontSize={11}
          textColor="#2DD4BF" blockCount={10}
          fillSpeed="staggered" stagger={10} />
      </Sequence>
      <Sequence from={240}>
        <FadeIn duration={15}>
          <Text text="15,000 tokens" font="Inter" size={14}
            weight={700} color="#2DD4BF" opacity={0.6}
            x={479} y={820} align="center" />
          <Text text="10 modules' specifications" font="Inter" size={12}
            color="#2DD4BF" opacity={0.5}
            x={479} y={845} align="center" />
        </FadeIn>
      </Sequence>
    </Panel>

    {/* 10× multiplier */}
    <Sequence from={360}>
      <GlowBloom duration={20}>
        <Text text="10×" font="Inter" size={64}
          weight={700} color="#2DD4BF" opacity={0.7}
          x={960} y={540} align="center" />
      </GlowBloom>
    </Sequence>

    {/* Bottom statement */}
    <Sequence from={600}>
      <FadeIn duration={20}>
        <Text text="Every token is author-curated. No retrieval guessing. No wasted space."
          font="Inter" size={14} color="#E2E8F0" opacity={0.6}
          x={960} y={920} align="center" />
        <Text text="The entire context window is devoted to your problem."
          font="Inter" size={14} weight={700} color="#2DD4BF" opacity={0.6}
          x={960} y={950} align="center" />
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
    "header": "RAW CODE CONTEXT",
    "headerColor": "#94A3B8",
    "content": "dense_code",
    "tokenCount": 15000,
    "scope": "1 module's implementation",
    "thematicRole": "overwhelming_code"
  },
  "rightPanel": {
    "header": "PROMPT CONTEXT",
    "headerColor": "#2DD4BF",
    "content": "prompt_blocks",
    "tokenCount": 15000,
    "scope": "10 modules' specifications",
    "thematicRole": "curated_prompts"
  },
  "multiplier": "10×",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_has_three_parts_022"]
}
```

---
