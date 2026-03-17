[title:]

# Section 1.1: Part 1 Title Card — The Economics of Darning

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 2:30 - 2:34

## Visual Description

A clean section title card announces Part 1. "THE ECONOMICS" appears first in large, bold weight, then "OF DARNING" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines. Behind the text, two abstract ghost shapes emerge at very low opacity — a price chart curve (left, amber) and a miniature sock silhouette (right, cool blue) — hinting at the sock-economics parallel that defines this section.

The background is deep navy-black with a subtle ledger-paper grid — faint horizontal lines with slightly brighter vertical accents at regular intervals, evoking accounting paper and economic charts.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Ledger grid: horizontal lines at 40px spacing, `#1E293B` at 0.04; vertical accents every 120px, `#1E293B` at 0.06

### Chart/Visual Elements

#### Title Text
- "THE ECONOMICS" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "OF DARNING" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 200px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 1" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Shapes (ghost elements)
- Price chart curve: rising-then-crossing S-curve at (700, 480), `#D9944A` at 0.04, 2px stroke
  - Two lines that cross, evoking the "threshold" moment
- Sock silhouette: simple sock outline at (1220, 480), `#4A90D9` at 0.04, 2px stroke
  - Classic tube-sock shape with ribbed cuff
- Both have 8px Gaussian blur glow at respective colors, 0.02 opacity

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Ledger grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 1" fades in. Two ghost shapes begin drawing themselves (stroke-dashoffset animation).
3. **Frame 40-60 (1.33-2s):** "THE ECONOMICS" types on character-by-character (3 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "OF DARNING" fades in with 10px upward slide.
6. **Frame 90-120 (3-4s):** Hold. Ghost shapes finish drawing. The two crossing lines pulse gently at the intersection point.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "OF DARNING" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost shape draw: `easeInOut(cubic)` over 60 frames
- Crossing-point pulse: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "This isn't nostalgia. It's economics."

Segment: `part1_001`

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <LedgerGrid hSpacing={40} vAccentEvery={120}
      color="#1E293B" hOpacity={0.04} vOpacity={0.06} />

    {/* Ghost shapes — economics + sock foreshadowed */}
    <Sequence from={15}>
      <StrokeDraw duration={60}>
        <CrossingCurves position={[700, 480]} color="#D9944A"
          opacity={0.04} strokeWidth={2}
          glow={{ blur: 8, opacity: 0.02 }} />
        <SockSilhouette position={[1220, 480]} color="#4A90D9"
          opacity={0.04} strokeWidth={2}
          glow={{ blur: 8, opacity: 0.02 }} />
      </StrokeDraw>
    </Sequence>

    {/* Section label */}
    <Sequence from={15}>
      <FadeIn duration={20}>
        <Text text="PART 1" font="Inter" size={14}
          weight={600} color="#64748B" opacity={0.5}
          letterSpacing={4} x={960} y={400} align="center" />
      </FadeIn>
    </Sequence>

    {/* Title: THE ECONOMICS */}
    <Sequence from={40}>
      <TypeWriter text="THE ECONOMICS" font="Inter" size={72}
        weight={700} color="#E2E8F0"
        charDelay={3} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[860, 505]} to={[1060, 505]}
        color="#334155" opacity={0.5} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Title: OF DARNING */}
    <Sequence from={70}>
      <SlideUp distance={10} duration={20}>
        <FadeIn duration={20}>
          <Text text="OF DARNING" font="Inter" size={72}
            weight={700} color="#E2E8F0"
            x={975} y={545} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": 1,
  "sectionLabel": "PART 1",
  "titleLine1": "THE ECONOMICS",
  "titleLine2": "OF DARNING",
  "backgroundColor": "#0A0F1A",
  "ghostElements": [
    { "shape": "crossing_curves", "color": "#D9944A", "component": "price_chart" },
    { "shape": "sock_silhouette", "color": "#4A90D9", "component": "sock_metaphor" }
  ],
  "narrationSegments": ["part1_001"]
}
```

---
