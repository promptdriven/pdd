[title:]

# Section 5.1: Part 5 — Compound Returns Title Card

**Tool:** Title
**Duration:** ~8s
**Timestamp:** 0:00 - 0:08

## Visual Description
A clean section title card introducing Part 5. The words "Compound Returns" appear center-screen in large, bold white typography against a deep navy background. A subtle upward-curving line — hinting at exponential growth — traces beneath the title as an accent, glowing faintly in gold. The subtitle "Part 5" appears above in smaller, muted text.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid lines

### Chart/Visual Elements
- **Accent curve:** A thin (`1.5px`) golden line (`#D9944A` at `0.4`) traces an exponential arc from bottom-left to bottom-right beneath the title, rising gently from left to right
- **Subtle glow:** The curve has a soft `8px` glow at `#D9944A` opacity `0.1`

### Animation Sequence
1. **Frame 0-30 (0-1s):** Background fades in from black. "Part 5" label fades in above center.
2. **Frame 30-75 (1-2.5s):** "Compound Returns" scales up from `0.85` to `1.0` with opacity `0→1`. Slight vertical shift from `+20px` to `0px`.
3. **Frame 75-120 (2.5-4s):** The golden accent curve draws left-to-right beneath the title.
4. **Frame 120-210 (4-7s):** Hold. Gentle pulse on the accent glow (opacity `0.1→0.2→0.1`, 60-frame cycle).
5. **Frame 210-240 (7-8s):** All elements fade out to black over 30 frames.

### Typography
- Section label: Inter, 16px, regular (400), `#64748B`, uppercase, letter-spacing `3px`
- Title: Inter, 64px, bold (700), `#E2E8F0`
- All text centered horizontally and vertically

### Easing
- Title scale-up: `easeOutCubic`
- Title fade-in: `easeOutQuad`
- Curve draw: `easeInOutCubic`
- Glow pulse: `easeInOutSine`
- Fade-out: `easeInQuad`

## Narration Sync
> "Now let's zoom out. Because the numbers you just saw — individual patches, individual bugs — add up to something staggering."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Section label */}
    <Sequence from={0}>
      <FadeIn durationInFrames={30}>
        <Text text="PART 5" font="Inter" size={16}
          weight={400} color="#64748B"
          letterSpacing="3px" align="center"
          y={-60} />
      </FadeIn>
    </Sequence>

    {/* Main title */}
    <Sequence from={30}>
      <ScaleAndFade
        fromScale={0.85} toScale={1.0}
        fromY={20} toY={0}
        durationInFrames={45} easing="easeOutCubic">
        <Text text="Compound Returns" font="Inter" size={64}
          weight={700} color="#E2E8F0" align="center" />
      </ScaleAndFade>
    </Sequence>

    {/* Accent curve */}
    <Sequence from={75}>
      <AnimatedCurve
        points="exponential-arc" color="#D9944A"
        strokeWidth={1.5} opacity={0.4}
        glowRadius={8} glowOpacity={0.1}
        drawDuration={45} easing="easeInOutCubic" />
    </Sequence>

    {/* Fade out */}
    <Sequence from={210}>
      <FadeOut durationInFrames={30} easing="easeInQuad" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionLabel": "PART 5",
  "title": "Compound Returns",
  "accentStyle": "exponential_curve",
  "accentColor": "#D9944A",
  "backgroundColor": "#0A0F1A",
  "durationSeconds": 8,
  "narrationSegments": ["part5_compound_returns_001"]
}
```
