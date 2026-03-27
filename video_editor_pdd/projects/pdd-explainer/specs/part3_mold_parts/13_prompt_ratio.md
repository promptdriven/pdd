[Remotion]

# Section 3.13: Prompt Compression Ratio

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 4:15 - 4:33

## Visual Description

The prompt from the previous shot glows — it's small, maybe 10-15 lines of clean natural language. Below it (or beside it), a much larger block of generated code is visible — ~200 lines, dense, syntax-highlighted. A ratio label animates between them: "1:5 to 1:10".

The visual is a size comparison. The prompt is compact and readable. The code it governs is 5-10x larger. The prompt is like a header file; the code is the OBJ file.

This transitions into a context window comparison: two side-by-side context windows (rectangles representing token capacity). The LEFT window is filled with 15,000 tokens of raw code — dense, hard to parse, slightly red-tinted to suggest strain. The RIGHT window is filled with prompts for ten modules — clean natural language, clear intent, slightly green-tinted. Both windows are the same physical size, but a label shows the right one represents "10× more system knowledge."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Phase 1: Prompt vs. Code Size

##### Prompt Block
- Position: left third, (200, 300) to (500, 500)
- Background: `#1E1E2E`, border `#D9944A` at 0.3, rounded 8px
- Content: 12 lines of natural language text, JetBrains Mono, 11px, `#D9944A` at 0.7
- Label above: "Prompt" — Inter, 14px, semi-bold (600), `#D9944A`
- Line count badge: "~15 lines" — Inter, 11px, `#D9944A` at 0.5

##### Code Block
- Position: right two-thirds, (600, 180) to (1750, 780)
- Background: `#1E1E2E`, border `#334155`, rounded 8px
- Content: ~40 visible lines of syntax-highlighted code (representing 200 total), scrollable overflow indicated
- Label above: "Generated Code" — Inter, 14px, semi-bold (600), `#64748B`
- Line count badge: "~200 lines" — Inter, 11px, `#64748B`

##### Ratio Label
- "1:5 to 1:10" — Inter, 36px, bold (700), `#E2E8F0`
- Connector line from prompt to code, `#D9944A` at 0.2
- Position: centered between the two blocks

#### Phase 2: Context Window Comparison

##### Left Window — Raw Code
- Tall rectangle: 400px × 500px, `#1E1E2E` fill
- Border: `#EF4444` at 0.2 (red tint = strain)
- Filled with dense code text (8px, low opacity, representing 15,000 tokens)
- Label: "15,000 tokens of raw code" — Inter, 14px, `#F87171`
- Sublabel: "Dense. Hard to parse." — Inter, 12px, `#94A3B8`

##### Right Window — Prompts
- Same tall rectangle: 400px × 500px, `#1E1E2E` fill
- Border: `#4ADE80` at 0.2 (green tint = efficient)
- Filled with clean natural language blocks (10px, readable)
- Label: "Prompts for 10 modules" — Inter, 14px, `#4ADE80`
- Sublabel: "10× more system knowledge" — Inter, 14px, bold (700), `#4ADE80`

### Animation Sequence
1. **Frame 0-30 (0-1s):** Prompt block fades in on left.
2. **Frame 30-90 (1-3s):** Code block fades in on right. Much larger.
3. **Frame 90-150 (3-5s):** Ratio "1:5 to 1:10" animates in between them with connector line.
4. **Frame 150-210 (5-7s):** Hold on size comparison.
5. **Frame 210-270 (7-9s):** Crossfade transition. Prompt/code blocks morph into context windows.
6. **Frame 270-330 (9-11s):** Left window fills with dense code (red tint). Label: "15,000 tokens of raw code."
7. **Frame 330-390 (11-13s):** Right window fills with clean prompts (green tint). Label: "Prompts for 10 modules."
8. **Frame 390-450 (13-15s):** "10× more system knowledge" label appears on right window with emphasis glow.
9. **Frame 450-540 (15-18s):** Hold. The contrast is clear: same window, vastly different information density.

### Typography
- Block labels: Inter, 14px, semi-bold (600)
- Ratio: Inter, 36px, bold (700), `#E2E8F0`
- Window labels: Inter, 14px, semi-bold (600)
- Sublabels: Inter, 12px, regular (400), `#94A3B8`
- Emphasis: Inter, 14px, bold (700), `#4ADE80`
- Code: JetBrains Mono, 8-11px

### Easing
- Block fade-in: `easeOut(quad)` over 20 frames
- Ratio animate: `easeOut(back)` over 20 frames
- Crossfade: `easeInOut(cubic)` over 30 frames
- Window fill: `easeOut(quad)` over 30 frames
- Emphasis glow: `easeInOut(sine)` single pulse over 15 frames

## Narration Sync
> "A good prompt is a fifth to a tenth the size of the code it generates. Think of the prompt as your header file. The generated code is the OBJ file. You're specifying what and why, not how. And that compression matters."
> "This is why the context window advantage we talked about is so powerful. You're not stuffing code into a window and hoping the model figures it out. You're giving it natural language — its strongest modality — in a window that's five to ten times more spacious. And every token is author-curated. No retrieval guessing. No wasted space. The entire context window is devoted to your problem."

Segments: `part3_mold_parts_017`, `part3_mold_parts_018`

- **255.08s** (seg 017): Prompt block appears — "A good prompt is a fifth to a tenth"
- **260.0s**: Code block appears — "the code it generates"
- **264.0s**: Ratio appears — "1:5 to 1:10"
- **272.88s** (seg 017 ends / seg 018 starts): Transition to context windows — "context window advantage"
- **280.0s**: Left window fills — "stuffing code into a window"
- **286.0s**: Right window fills — "natural language — its strongest modality"
- **292.0s**: "10× more system knowledge" — emphasis
- **297.38s** (seg 018 ends): Hold on contrast

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Phase 1: Prompt vs Code size */}
    <Sequence from={0} durationInFrames={270}>
      {/* Prompt block */}
      <Sequence from={0}>
        <FadeIn duration={20}>
          <CodeBlock
            x={200} y={300} width={300} height={200}
            content={PROMPT_TEXT} borderColor="#D9944A"
            label="Prompt" badge="~15 lines"
          />
        </FadeIn>
      </Sequence>

      {/* Code block */}
      <Sequence from={30}>
        <FadeIn duration={20}>
          <CodeBlock
            x={600} y={180} width={1150} height={600}
            content={GENERATED_CODE} borderColor="#334155"
            label="Generated Code" badge="~200 lines"
            syntaxHighlight
          />
        </FadeIn>
      </Sequence>

      {/* Ratio */}
      <Sequence from={90}>
        <ScaleIn from={0.8} to={1.0} duration={20}>
          <Text text="1:5 to 1:10" font="Inter" size={36}
            weight={700} color="#E2E8F0"
            x={450} y={550} />
        </ScaleIn>
      </Sequence>
    </Sequence>

    {/* Phase 2: Context window comparison */}
    <Sequence from={210}>
      <CrossFade duration={30}>
        <ContextWindowComparison
          left={{
            label: "15,000 tokens of raw code",
            sublabel: "Dense. Hard to parse.",
            tint: "#EF4444",
            content: "code"
          }}
          right={{
            label: "Prompts for 10 modules",
            sublabel: "10× more system knowledge",
            tint: "#4ADE80",
            content: "prompts"
          }}
        />
      </CrossFade>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "compression_ratio",
  "promptLines": 15,
  "codeLines": 200,
  "ratio": "1:5 to 1:10",
  "contextComparison": {
    "left": { "tokens": 15000, "type": "raw_code", "modules": 1 },
    "right": { "tokens": 15000, "type": "prompts", "modules": 10 }
  },
  "narrationSegments": ["part3_mold_parts_017", "part3_mold_parts_018"],
  "durationSeconds": 18.0
}
```

---
