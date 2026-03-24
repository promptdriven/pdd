[Remotion]

# Section 4.4: Code Generation Comparison — Both Paths Produce Correct Output

**Tool:** Remotion
**Duration:** ~17s (511 frames @ 30fps)
**Timestamp:** 0:47 - 1:04

## Visual Description

A side-by-side animation showing that both approaches — verbose prompt with few tests, and minimal prompt with many tests — produce the same correct output. This reinforces the key insight that test accumulation simplifies prompts without sacrificing correctness.

**LEFT SCENARIO:** The dense 50-line prompt (`parser_v1.prompt`) flows downward through a narrow funnel into a code block. A small cluster of 5 test checkmarks appears beside it. The output code glows green — correct.

**RIGHT SCENARIO:** The minimal 10-line prompt (`parser_v2.prompt`) flows through a wider funnel. But the funnel is surrounded by 47 test wall segments that constrain the output. The same output code glows green — also correct.

Below, a comparison bar highlights: "50-line prompt → correct" vs "10-line prompt + 47 tests → correct". The right side pulses to indicate this is the preferred path.

Then the entire comparison fades to a centered callout text: **"More tests, less prompt. The walls do the precision work."** — the section's key takeaway.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Left Scenario — Heavy Prompt
- Position: centered at x: 350
- Prompt document: 180×120px, bg `#0F1E1E`, border `#2DD4BF` at 0.3, at y: 180
- Dense text lines: 10 visible lines, Inter, 7px, `#2DD4BF` at 0.3
- File label: "`parser_v1.prompt` — 50 lines" — JetBrains Mono, 10px, `#2DD4BF` at 0.5, below prompt
- Funnel: narrow tapered shape from prompt bottom to code top, `#2DD4BF` at 0.1, 2px stroke
- Test checkmarks: 5 small ✓ icons, 10px, `#4ADE80` at 0.4, clustered at x: 500, y: 500
- Output code block: 180×100px, bg `#1E1E2E`, border `#4ADE80` at 0.3, at y: 650
- Code text: 6 lines of syntax-highlighted pseudo-code, JetBrains Mono, 8px
- "CORRECT ✓" label: Inter, 12px, bold, `#4ADE80` at 0.7, below code block

#### Right Scenario — Heavy Tests
- Position: centered at x: 1200
- Prompt document: 120×50px, bg `#0F1E1E`, border `#2DD4BF` at 0.3, at y: 220
- Sparse text lines: 3 visible lines, Inter, 7px, `#2DD4BF` at 0.3
- File label: "`parser_v2.prompt` — 10 lines" — JetBrains Mono, 10px, `#2DD4BF` at 0.5, below prompt
- Funnel: wider tapered shape from prompt bottom to code top, `#2DD4BF` at 0.1, 2px stroke
- Test wall segments: 12 small wall icons (8×14px each), `#D9944A` at 0.5, flanking funnel on both sides
- Test count label: "47 tests" — Inter, 10px, `#D9944A` at 0.5
- Output code block: 180×100px, bg `#1E1E2E`, border `#4ADE80` at 0.3, at y: 650
- Code text: 6 lines of syntax-highlighted pseudo-code (same output), JetBrains Mono, 8px
- "CORRECT ✓" label: Inter, 12px, bold, `#4ADE80` at 0.7, below code block
- Subtle glow: `#4ADE80` at 0.08, 20px radius around right scenario (preferred path)

#### Comparison Bar
- Position: centered at (960, 880)
- Left: "50-line prompt → correct" — Inter, 13px, `#94A3B8` at 0.5
- Divider: "vs" — Inter, 13px, `#64748B` at 0.4
- Right: "10-line prompt + 47 tests → correct" — Inter, 13px, bold, `#2DD4BF` at 0.7

#### Takeaway Callout
- Position: centered at (960, 500)
- "More tests, less prompt." — Inter, 40px, bold, `#E2E8F0` at 0.9
- "The walls do the precision work." — Inter, 24px, `#D9944A` at 0.7, at y: 560
- Both lines have a subtle text shadow glow

### Animation Sequence
1. **Frame 0-60 (0-2s):** Both prompt documents appear simultaneously. File labels visible. Funnels begin drawing.
2. **Frame 60-150 (2-5s):** LEFT: Dense prompt flows through narrow funnel. 5 test checkmarks appear. RIGHT: Minimal prompt flows through wide funnel. Test wall segments appear flanking the funnel, staggered.
3. **Frame 150-240 (5-8s):** Both output code blocks appear simultaneously. Both show "CORRECT ✓". Right side gets subtle green glow.
4. **Frame 240-300 (8-10s):** Comparison bar appears at bottom. Right side text pulses to indicate preferred path.
5. **Frame 300-360 (10-12s):** Both scenarios fade out. Screen clears.
6. **Frame 360-450 (12-15s):** Takeaway callout text fades in — "More tests, less prompt." then "The walls do the precision work."
7. **Frame 450-511 (15-17s):** Hold on takeaway. Text pulses gently.

### Typography
- File labels: JetBrains Mono, 10px, `#2DD4BF` at 0.5
- Prompt content: Inter, 7px, `#2DD4BF` at 0.3
- Code content: JetBrains Mono, 8px, syntax-highlighted
- Correct labels: Inter, 12px, bold (700), `#4ADE80` at 0.7
- Comparison bar: Inter, 13px, mixed weights and colors
- Takeaway line 1: Inter, 40px, bold (700), `#E2E8F0` at 0.9
- Takeaway line 2: Inter, 24px, semi-bold (600), `#D9944A` at 0.7

### Easing
- Document appear: `easeOut(cubic)` over 20 frames
- Funnel draw: `easeInOut(quad)` over 40 frames
- Flow through funnel: `easeIn(quad)` over 30 frames
- Test walls stagger: `easeOut(cubic)` over 10 frames each, staggered 3 frames
- Code block appear: `easeOut(cubic)` over 20 frames
- Right glow: `easeOut(quad)` over 30 frames
- Comparison bar: `easeOut(quad)` over 20 frames
- Scenario fade-out: `easeIn(quad)` over 30 frames
- Takeaway fade-in: `easeOut(cubic)` over 30 frames
- Takeaway pulse: `easeInOut(sine)` on 50-frame cycle

## Narration Sync
> "On... This is why test accumulation matters. It's not just about catching bugs. It's about making prompts simpler and regeneration safer over time."
> "The more walls you have, the less you need to specify. The mold does the precision work."

Segments: `part4_precision_tradeoff_007`, `part4_precision_tradeoff_008`

- **0:47** ("This is why test accumulation"): Both scenarios begin building side by side
- **0:52** ("not just about catching bugs"): Both outputs appear — both correct
- **0:55** ("making prompts simpler"): Comparison bar appears, right side highlighted
- **0:58** ("The more walls you have"): Transition to takeaway callout
- **1:02** ("The mold does the precision work"): Takeaway text fully visible, pulsing

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={511}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.03} />

    {/* Left scenario — heavy prompt */}
    <Sequence from={0} durationInFrames={360}>
      <FadeOut startFrame={300} duration={30}>
        <GenerationScenario x={350}
          promptWidth={180} promptHeight={120} promptLines={10}
          fileLabel="parser_v1.prompt — 50 lines"
          funnelWidth="narrow" testCount={5}
          testStyle="checkmarks" testColor="#4ADE80"
          codeOutput={CODE_OUTPUT} />
      </FadeOut>
    </Sequence>

    {/* Right scenario — heavy tests */}
    <Sequence from={0} durationInFrames={360}>
      <FadeOut startFrame={300} duration={30}>
        <GenerationScenario x={1200}
          promptWidth={120} promptHeight={50} promptLines={3}
          fileLabel="parser_v2.prompt — 10 lines"
          funnelWidth="wide" testCount={47}
          testStyle="walls" testColor="#D9944A"
          codeOutput={CODE_OUTPUT} glow={true} />
      </FadeOut>
    </Sequence>

    {/* Comparison bar */}
    <Sequence from={240} durationInFrames={120}>
      <FadeIn duration={20}>
        <ComparisonBar
          left="50-line prompt → correct" leftColor="#94A3B8"
          right="10-line prompt + 47 tests → correct" rightColor="#2DD4BF"
          divider="vs" x={960} y={880} />
      </FadeIn>
    </Sequence>

    {/* Takeaway callout */}
    <Sequence from={360}>
      <FadeIn duration={30}>
        <Text text="More tests, less prompt." font="Inter" size={40}
          weight={700} color="#E2E8F0" opacity={0.9}
          x={960} y={500} align="center"
          textShadow="0 0 30px rgba(226,232,240,0.2)" />
      </FadeIn>
      <Sequence from={20}>
        <FadeIn duration={30}>
          <Text text="The walls do the precision work." font="Inter" size={24}
            weight={600} color="#D9944A" opacity={0.7}
            x={960} y={560} align="center"
            textShadow="0 0 20px rgba(217,148,74,0.15)" />
        </FadeIn>
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "code_generation_comparison",
  "scenarios": [
    {
      "side": "left",
      "promptFile": "parser_v1.prompt",
      "promptLines": 50,
      "testCount": 5,
      "result": "correct",
      "emphasis": "prompt_heavy"
    },
    {
      "side": "right",
      "promptFile": "parser_v2.prompt",
      "promptLines": 10,
      "testCount": 47,
      "result": "correct",
      "emphasis": "test_heavy",
      "preferred": true
    }
  ],
  "takeaway": {
    "line1": "More tests, less prompt.",
    "line2": "The walls do the precision work."
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_precision_tradeoff_007", "part4_precision_tradeoff_008"]
}
```

---
