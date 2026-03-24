[title:]

# Section 7.8: Final Title Card — Prompt-Driven Development

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 0:19 - 0:23

## Visual Description

The final frame of the entire video. Fades up from the beat's near-black. The title "Prompt-Driven Development" appears centered, large, clean — the definitive statement. Below it, a subtle URL. Below the URL, two monospaced lines providing the immediate next action:

```
uv tool install pdd-cli
pdd update your_module.py
```

The title glows with a gentle warm amber aura — echoing the mold glow. The install commands are practical, quiet, secondary. The composition is clean and confident: this is a real tool, ready to use.

The final narration line — "The mold is what matters" — lands as the title appears.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none

### Chart/Visual Elements

#### Title
- Text: "Prompt-Driven Development"
- Font: Inter, 52px, bold (700), `#E2E8F0`
- Position: centered at (960, 400)
- Letter-spacing: 2px
- Glow: `#D9944A` at 0.08, blur radius 60px

#### URL
- Text: "promptdrivendevelopment.com"
- Font: Inter, 16px, regular (400), `#94A3B8` at 0.6
- Position: centered at (960, 480)

#### Install Commands
- Line 1: `uv tool install pdd-cli`
- Line 2: `pdd update your_module.py`
- Font: JetBrains Mono, 16px, regular (400), `#64748B` at 0.5
- Position: centered block at (960, 580), 30px line height
- Left-aligned within centered block (monospace alignment)
- Faint left border: 2px `#D9944A` at 0.2, padding-left 16px

#### Subtle Triangle Echo
- The PDD triangle from Section 7.4, rendered at 0.03 opacity
- Same vertex positions but scaled to 0.4x, centered behind title
- Purely atmospheric — reinforces the three-component message subliminally

### Animation Sequence
1. **Frame 0-30 (0-1s):** Title text fades in from 0 to full opacity. Amber glow ramps up. `easeOut(cubic)`.
2. **Frame 30-45 (1-1.5s):** URL fades in below title. `easeOut(quad)`.
3. **Frame 45-75 (1.5-2.5s):** Install commands fade in. Line 1 first, line 2 follows 10 frames later. Left border draws in. `easeOut(quad)`.
4. **Frame 75-120 (2.5-4s):** Hold. All elements stable. Title glow pulses very gently (barely perceptible). This frame can hold indefinitely for video end card.

### Typography
- Title: Inter, 52px, bold (700), `#E2E8F0`, letter-spacing 2px
- URL: Inter, 16px, regular (400), `#94A3B8` at 0.6
- Commands: JetBrains Mono, 16px, regular (400), `#64748B` at 0.5

### Easing
- Title fade: `easeOut(cubic)` over 30 frames
- Glow ramp: `easeOut(quad)` over 30 frames
- URL fade: `easeOut(quad)` over 15 frames
- Command fade: `easeOut(quad)` over 15 frames each, staggered 10 frames
- Title glow pulse: `easeInOut(sine)`, very slow (120 frame period), amplitude 0.06-0.10

## Narration Sync
> "The mold is what matters."

Segment: `closing_005`

- **0:19** ("The mold"): Title begins fading in
- **0:20** ("is what matters"): Title fully visible, URL appearing
- **0:21** (post-narration): Install commands fade in
- **0:23** (end): All elements stable. End card hold.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Subtle triangle echo */}
    <TriangleFrame
      vertices={[[960, 320], [860, 450], [1060, 450]]}
      colors={["#60A5FA", "#4ADE80", "#D9944A"]}
      edgeColor="#334155"
      vertexOpacity={0.03}
      edgeOpacity={0.02}
      showLabels={false} />

    {/* Title */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <Text text="Prompt-Driven Development"
          font="Inter" size={52} weight={700}
          color="#E2E8F0" letterSpacing={2}
          x={960} y={400} align="center"
          glow={{ color: "#D9944A", opacity: 0.08, blur: 60 }} />
      </FadeIn>
    </Sequence>

    {/* URL */}
    <Sequence from={30}>
      <FadeIn duration={15}>
        <Text text="promptdrivendevelopment.com"
          font="Inter" size={16} weight={400}
          color="#94A3B8" opacity={0.6}
          x={960} y={480} align="center" />
      </FadeIn>
    </Sequence>

    {/* Install commands */}
    <Sequence from={45}>
      <FadeIn duration={15}>
        <CodeBlock
          x={760} y={560} leftBorder={{ width: 2, color: "#D9944A", opacity: 0.2 }}
          paddingLeft={16}>
          <Text text="uv tool install pdd-cli"
            font="JetBrains Mono" size={16} weight={400}
            color="#64748B" opacity={0.5} />
        </CodeBlock>
      </FadeIn>
    </Sequence>
    <Sequence from={55}>
      <FadeIn duration={15}>
        <CodeBlock x={760} y={590}>
          <Text text="pdd update your_module.py"
            font="JetBrains Mono" size={16} weight={400}
            color="#64748B" opacity={0.5} />
        </CodeBlock>
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "chartId": "final_title_card",
  "title": "Prompt-Driven Development",
  "titleFont": { "family": "Inter", "size": 52, "weight": 700, "color": "#E2E8F0" },
  "titleGlow": { "color": "#D9944A", "opacity": 0.08, "blur": 60 },
  "url": "promptdrivendevelopment.com",
  "commands": [
    "uv tool install pdd-cli",
    "pdd update your_module.py"
  ],
  "commandFont": { "family": "JetBrains Mono", "size": 16, "color": "#64748B" },
  "ghostElements": [
    { "source": "pdd_triangle", "opacity": 0.03, "scale": 0.4 }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["closing_005"]
}
```

---
