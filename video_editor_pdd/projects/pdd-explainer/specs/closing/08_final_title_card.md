[title:]

# Section 7.8: Final Title Card — Prompt-Driven Development

**Tool:** Title
**Duration:** ~6s
**Timestamp:** 0:21 - 0:27

## Visual Description
Fade from black to the final title card. "Prompt-Driven Development" appears in large, clean typography — the definitive statement of the video's thesis. Below the title, a URL appears in muted text. Further below, two lines of monospace code provide the immediate call-to-action:

```
uv tool install pdd-cli
pdd update your_module.py
```

The card is elegant, minimal, and unhurried. The title appears first, then the install commands fade in beneath — a bridge from concept to action. A subtle glow on "Prompt-Driven Development" echoes the mold glow from the previous spec — the specification is what matters, and here's how to start.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#050810` fading up to `#0A0F1A`
- No grid, no decoration

### Chart/Visual Elements

#### Title Text
- "Prompt-Driven Development"
- Font: Inter, 48px, bold (700), `#E2E8F0`
- Position: centered, `(960, 380)`
- Subtle outer glow: `#4A90D9` at `0.1`, `12px` blur

#### URL
- "promptdrivendevelopment.com"
- Font: Inter, 16px, regular (400), `#64748B`
- Position: centered, `(960, 450)`

#### Install Commands
- Line 1: `uv tool install pdd-cli`
- Line 2: `pdd update your_module.py`
- Font: JetBrains Mono, 18px, `#94A3B8`
- Position: centered, starting at `(960, 560)`
- Line spacing: `36px`
- Background pill: `#111827` with `1px` border `#1E293B`, radius `8px`, padding `24px 40px`
- Prompt `$` prefix: `#22C55E` (green)

### Animation Sequence
1. **Frame 0-30 (0-1s):** Background lifts from `#050810` to `#0A0F1A`. Silence continues from the beat.
2. **Frame 30-60 (1-2s):** "Prompt-Driven Development" fades in with subtle scale (`0.97→1.0`). Outer glow blooms.
3. **Frame 60-80 (2-2.7s):** URL fades in below title.
4. **Frame 80-110 (2.7-3.7s):** Command pill background fades in. Install commands appear line by line with a slight stagger.
5. **Frame 110-160 (3.7-5.3s):** Hold. All elements settled. Title glow pulses very gently.
6. **Frame 160-180 (5.3-6s):** All elements fade to black.

### Typography
- Title: Inter, 48px, bold (700), `#E2E8F0`
- URL: Inter, 16px, regular (400), `#64748B`
- Commands: JetBrains Mono, 18px, regular, `#94A3B8`
- Command prompt `$`: JetBrains Mono, 18px, `#22C55E`

### Easing
- Background lift: `easeOutQuad` over 30 frames
- Title fade + scale: `easeOutCubic` over 25 frames
- Title glow bloom: `easeOutQuad` over 20 frames
- URL fade-in: `easeOutQuad` over 20 frames
- Command pill: `easeOutQuad` over 15 frames
- Command lines: `easeOutQuad` over 15 frames, staggered 10 frames
- Title glow pulse: `easeInOutSine` on 90-frame cycle
- Final fade-out: `easeInCubic` over 20 frames

## Narration Sync
> (No narration — the final spoken line "The mold is what matters" completes during the beat. This card plays in post-narration silence.)

Post-segment: follows `closing_005` (20.66s onward)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <AbsoluteFill>
    {/* Background lift */}
    <AnimateColor from="#050810" to="#0A0F1A"
      durationInFrames={30} easing="easeOutQuad"
      property="backgroundColor" />

    {/* Title */}
    <Sequence from={30}>
      <ScaleAndFade fromScale={0.97} toScale={1.0}
        durationInFrames={25} easing="easeOutCubic">
        <GlowText
          text="Prompt-Driven Development"
          font="Inter" size={48} weight={700}
          color="#E2E8F0"
          glowColor="#4A90D9" glowOpacity={0.1}
          glowBlur={12}
          x={960} y={380} align="center"
        />
      </ScaleAndFade>
    </Sequence>

    {/* Title glow pulse */}
    <Sequence from={55}>
      <Loop durationInFrames={90}>
        <OpacityPulse target="title_glow"
          from={0.1} to={0.18}
          durationInFrames={90} easing="easeInOutSine" />
      </Loop>
    </Sequence>

    {/* URL */}
    <Sequence from={60}>
      <FadeIn durationInFrames={20} easing="easeOutQuad">
        <Text text="promptdrivendevelopment.com"
          font="Inter" size={16} weight={400}
          color="#64748B" x={960} y={450} align="center" />
      </FadeIn>
    </Sequence>

    {/* Command pill background */}
    <Sequence from={80}>
      <FadeIn durationInFrames={15} easing="easeOutQuad">
        <RoundedRect
          x={700} y={530} width={520} height={110}
          bg="#111827" border="#1E293B"
          borderWidth={1} radius={8}
        />
      </FadeIn>
    </Sequence>

    {/* Command line 1 */}
    <Sequence from={85}>
      <FadeIn durationInFrames={15} easing="easeOutQuad">
        <Text text="$ uv tool install pdd-cli"
          font="JetBrains Mono" size={18}
          color="#94A3B8" x={730} y={558}
          promptChar="$" promptColor="#22C55E" />
      </FadeIn>
    </Sequence>

    {/* Command line 2 */}
    <Sequence from={95}>
      <FadeIn durationInFrames={15} easing="easeOutQuad">
        <Text text="$ pdd update your_module.py"
          font="JetBrains Mono" size={18}
          color="#94A3B8" x={730} y={594}
          promptChar="$" promptColor="#22C55E" />
      </FadeIn>
    </Sequence>

    {/* Final fade to black */}
    <Sequence from={160}>
      <FadeOut durationInFrames={20} easing="easeInCubic" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "final_title_card",
  "title": "Prompt-Driven Development",
  "url": "promptdrivendevelopment.com",
  "commands": [
    "uv tool install pdd-cli",
    "pdd update your_module.py"
  ],
  "titleColor": "#E2E8F0",
  "titleGlow": "#4A90D9",
  "backgroundColor": "#0A0F1A",
  "commandBg": "#111827",
  "durationSeconds": 6,
  "narrationSegments": []
}
```
