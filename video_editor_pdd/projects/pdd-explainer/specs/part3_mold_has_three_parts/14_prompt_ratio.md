[Remotion]

# Section 3.14: Prompt-to-Code Ratio — Compression Matters

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 3:14 - 3:28

## Visual Description

A visual comparison showing the dramatic size difference between a prompt and the code it generates. On screen, a prompt file glows teal — it's small, maybe 10-15 lines of natural language. Next to it, the generated code file is much larger — 200 lines of dense syntax-highlighted code. Both are visible simultaneously.

A ratio counter animates between them: "1:5" → "1:10" — the prompt is a fifth to a tenth the size. The prompt is labeled "header file" and the code is labeled "OBJ file" to give technical listeners a familiar mental model.

Below: "You're specifying WHAT and WHY, not HOW."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Prompt File (Left)
- Position: x: 200, y: 150, width: 350, height: 350
- Background: `#0F1E1E`, border `#2DD4BF` at 0.3, rounded 6px
- Content: 12 lines of natural language, Inter, 11px, `#2DD4BF` at 0.5
- Glow: `#2DD4BF` at 0.1, 15px radius
- Label above: "user_parser.prompt" — JetBrains Mono, 12px, `#2DD4BF` at 0.6
- Label below: "~15 lines" — Inter, 14px, `#2DD4BF` at 0.5

#### Code File (Right)
- Position: x: 700, y: 80, width: 900, height: 700
- Background: `#1E1E2E`, border `#334155` at 0.2, rounded 6px
- Content: dense code, JetBrains Mono, 8px, syntax-highlighted, scrolling slowly
- Label above: "user_parser.py" — JetBrains Mono, 12px, `#94A3B8` at 0.5
- Label below: "~200 lines" — Inter, 14px, `#94A3B8` at 0.5
- No glow — it's output, not the source of truth

#### Ratio Display
- Position: centered between files, y: 540
- "1 : 5" → "1 : 10" — Inter, 48px, bold, `#2DD4BF` at 0.7
- Left number in teal, colon in neutral, right number animates

#### Analogy Labels
- Prompt: "≈ header file" — Inter, 12px, italic, `#2DD4BF` at 0.4
- Code: "≈ OBJ file" — Inter, 12px, italic, `#94A3B8` at 0.3

#### Bottom Statement
- "You're specifying WHAT and WHY, not HOW." — Inter, 16px, bold, `#E2E8F0` at 0.6, y: 920

### Animation Sequence
1. **Frame 0-60 (0-2s):** Prompt file appears with teal glow. Short, clean, readable.
2. **Frame 60-150 (2-5s):** Code file appears — much larger, dense, scrolling.
3. **Frame 150-240 (5-8s):** Ratio "1 : 5" appears between them. Then animates to "1 : 10".
4. **Frame 240-300 (8-10s):** Analogy labels appear: "header file" / "OBJ file".
5. **Frame 300-360 (10-12s):** Bottom statement fades in.
6. **Frame 360-420 (12-14s):** Hold. Prompt glows, code neutral.

### Typography
- File labels: JetBrains Mono, 12px, respective colors
- Prompt content: Inter, 11px, `#2DD4BF` at 0.5
- Code content: JetBrains Mono, 8px, syntax-highlighted
- Ratio: Inter, 48px, bold (700), `#2DD4BF`
- Line counts: Inter, 14px, respective colors
- Analogy: Inter, 12px, italic, respective colors
- Statement: Inter, 16px, bold (700), `#E2E8F0` at 0.6

### Easing
- Prompt appear: `easeOut(cubic)` over 30 frames
- Code appear: `easeOut(cubic)` over 40 frames
- Ratio appear: `easeOut(back)` over 20 frames
- Ratio animate (5→10): `easeInOut(cubic)` over 40 frames
- Statement fade-in: `easeOut(quad)` over 20 frames

## Narration Sync
> "A good prompt is a fifth to a tenth the size of the code it generates. Think of the prompt as your header file. The generated code is the OBJ file. You're specifying what and why, not how. And that compression matters."

Segment: `part3_mold_has_three_parts_021`

- **3:14** ("A good prompt"): Prompt file appears
- **3:18** ("fifth to a tenth"): Ratio appears and animates
- **3:23** ("header file"): Analogy labels
- **3:26** ("compression matters"): Bottom statement

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.03} />

    {/* Prompt file */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <GlowBox color="#2DD4BF" opacity={0.1} radius={15}>
          <CodeFile x={200} y={150} width={350} height={350}
            bg="#0F1E1E" border="#2DD4BF"
            content={PROMPT_CONTENT} font="Inter" fontSize={11}
            textColor="#2DD4BF" label="user_parser.prompt" />
        </GlowBox>
        <Text text="~15 lines" font="Inter" size={14}
          color="#2DD4BF" opacity={0.5} x={375} y={520} align="center" />
      </FadeIn>
    </Sequence>

    {/* Code file */}
    <Sequence from={60}>
      <FadeIn duration={40}>
        <CodeFile x={700} y={80} width={900} height={700}
          bg="#1E1E2E" border="#334155"
          content={CODE_CONTENT} font="JetBrains Mono" fontSize={8}
          scroll label="user_parser.py" />
        <Text text="~200 lines" font="Inter" size={14}
          color="#94A3B8" opacity={0.5} x={1150} y={800} align="center" />
      </FadeIn>
    </Sequence>

    {/* Ratio */}
    <Sequence from={150}>
      <AnimatedRatio from="1:5" to="1:10"
        font="Inter" size={48} weight={700}
        color="#2DD4BF" opacity={0.7}
        x={500} y={540}
        animateDelay={30} animateDuration={40} />
    </Sequence>

    {/* Bottom statement */}
    <Sequence from={300}>
      <FadeIn duration={20}>
        <Text text="You're specifying WHAT and WHY, not HOW."
          font="Inter" size={16} weight={700} color="#E2E8F0" opacity={0.6}
          x={960} y={920} align="center" />
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
  "promptFile": { "name": "user_parser.prompt", "lines": 15, "color": "#2DD4BF" },
  "codeFile": { "name": "user_parser.py", "lines": 200, "color": "#94A3B8" },
  "ratio": { "from": "1:5", "to": "1:10" },
  "analogy": { "prompt": "header file", "code": "OBJ file" },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_has_three_parts_021"]
}
```

---
