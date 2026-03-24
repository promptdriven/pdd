[Remotion]

# Section 3.14: Prompt Compression Ratio — 1:5 to 1:10

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 4:14 - 4:32

## Visual Description

A visual comparison of prompt size vs generated code size. On the left, a small glowing document (10-15 lines of natural language) — the prompt. On the right, a much larger code file (150-200 lines) — the generated code. The size ratio is immediately visible: the prompt is dramatically smaller.

A ratio label animates between them: "1:5 to 1:10" — the prompt is a fifth to a tenth the size of the code. Lines draw from the prompt to the code showing the expansion. The prompt glows brightly; the code is dimmer — the prompt is what matters.

Below: an analogy — "Prompt = header file. Code = OBJ file. You specify WHAT and WHY, not HOW."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Prompt Document (Left)
- Position: (250, 300), 250×200px
- Background: `#0F1E1E` (dark teal tint), rounded 8px, border `#2DD4BF` at 0.4
- Content: 12 lines of natural language text, Inter, 10px, `#2DD4BF` at 0.5
- Glow: `#2DD4BF` at 0.15, 30px radius
- Line count label: "~12 lines" — Inter, 12px, `#2DD4BF` at 0.6, below

#### Generated Code (Right)
- Position: (1200, 150), 400×700px
- Background: `#1E1E2E` (VS Code dark), rounded 8px, border `#334155` at 0.3
- Content: ~40 visible lines of syntax-highlighted code, JetBrains Mono, 8px
- Scroll indicator suggesting 200 total lines
- Opacity: 0.5 overall (dimmer than prompt)
- Line count label: "~200 lines" — Inter, 12px, `#94A3B8` at 0.5, below

#### Ratio Display
- Position: centered at (700, 500)
- "1:5 to 1:10" — Inter, 48px, bold, `#2DD4BF` at 0.8
- Expansion lines: 5 thin lines from prompt right edge to code left edge, `#2DD4BF` at 0.1

#### Analogy Bar
- Position: centered at (960, 920)
- "Prompt = header file. Code = OBJ file." — Inter, 14px, `#94A3B8` at 0.5
- "You specify WHAT and WHY, not HOW." — Inter, 14px, bold, `#2DD4BF` at 0.6

### Animation Sequence
1. **Frame 0-60 (0-2s):** Prompt document appears on left with glow. Lines of text visible.
2. **Frame 60-150 (2-5s):** Generated code appears on right, much larger. Scrolls briefly to show volume.
3. **Frame 150-240 (5-8s):** Expansion lines draw from prompt to code. Ratio "1:5 to 1:10" animates in at center.
4. **Frame 240-360 (8-12s):** Code dims further. Prompt glows brighter. The contrast in importance is visual.
5. **Frame 360-450 (12-15s):** Analogy text appears at bottom.
6. **Frame 450-540 (15-18s):** Hold. Prompt continues to pulse. Code is dimmed output.

### Typography
- Prompt text: Inter, 10px, `#2DD4BF` at 0.5
- Code text: JetBrains Mono, 8px, syntax-highlighted
- Ratio: Inter, 48px, bold (700), `#2DD4BF` at 0.8
- Line counts: Inter, 12px, respective colors
- Analogy: Inter, 14px, `#94A3B8` and `#2DD4BF`

### Easing
- Document appear: `easeOut(cubic)` over 30 frames
- Code appear: `easeOut(cubic)` over 40 frames
- Expansion lines: `easeInOut(quad)` over 30 frames, staggered
- Ratio number: `easeOut(back)` over 20 frames (slight scale spring)
- Code dim: `easeOut(quad)` over 30 frames
- Prompt glow: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "A good prompt is a fifth to a tenth the size of the code it generates. Think of the prompt as your header file. The generated code is the OBJ file. You're specifying what and why, not how."

Segment: `part3_mold_three_parts_023`

- **4:14** ("a fifth to a tenth"): Prompt and code documents appear, ratio shown
- **4:22** ("header file"): Prompt glows, code dims
- **4:28** ("specifying what and why"): Analogy text appears

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.03} />

    {/* Prompt document */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <DocumentPanel
          x={250} y={300} width={250} height={200}
          bg="#0F1E1E" border="#2DD4BF" borderOpacity={0.4}
          content={PROMPT_LINES} font="Inter" fontSize={10}
          textColor="#2DD4BF" textOpacity={0.5}
          glow="#2DD4BF" glowOpacity={0.15} glowRadius={30}
          label="~12 lines" labelColor="#2DD4BF" />
      </FadeIn>
    </Sequence>

    {/* Generated code */}
    <Sequence from={60}>
      <FadeIn duration={40}>
        <DocumentPanel
          x={1200} y={150} width={400} height={700}
          bg="#1E1E2E" border="#334155" borderOpacity={0.3}
          content={CODE_LINES} font="JetBrains Mono" fontSize={8}
          textColor="syntax" scrollIndicator={true}
          opacity={0.5}
          label="~200 lines" labelColor="#94A3B8" />
      </FadeIn>
    </Sequence>

    {/* Expansion lines and ratio */}
    <Sequence from={150}>
      <ExpansionLines from={[375, 400]} to={[1000, 500]}
        count={5} color="#2DD4BF" opacity={0.1}
        drawDuration={30} stagger={5} />
      <Sequence from={30}>
        <ScaleIn scale={0.8} duration={20}>
          <Text text="1:5 to 1:10" font="Inter" size={48}
            weight={700} color="#2DD4BF" opacity={0.8}
            x={700} y={500} align="center" />
        </ScaleIn>
      </Sequence>
    </Sequence>

    {/* Analogy */}
    <Sequence from={360}>
      <FadeIn duration={20}>
        <Text text="Prompt = header file. Code = OBJ file."
          font="Inter" size={14} color="#94A3B8" opacity={0.5}
          x={960} y={910} align="center" />
        <Text text="You specify WHAT and WHY, not HOW."
          font="Inter" size={14} weight={700}
          color="#2DD4BF" opacity={0.6}
          x={960} y={940} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "prompt_ratio",
  "promptSize": "~12 lines",
  "codeSize": "~200 lines",
  "ratio": "1:5 to 1:10",
  "analogy": { "prompt": "header file", "code": "OBJ file" },
  "promptColor": "#2DD4BF",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_three_parts_023"]
}
```

---
