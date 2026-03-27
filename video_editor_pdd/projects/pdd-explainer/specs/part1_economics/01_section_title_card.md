[title:]

# Section 1.1: The Economics of Darning — Section Title Card

**Tool:** Title
**Duration:** ~24s (720 frames @ 30fps)
**Timestamp:** 0:00 - 0:24

## Visual Description

A section title card introducing Part 1. "THE ECONOMICS" appears in large bold weight, then "OF DARNING" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost silhouette of a line chart sits at very low opacity — two lines crossing, foreshadowing the cost-crossing-point thesis. Background is deep navy-black consistent with the overall visual language.

The title holds across three narration segments covering the 30-second demo recap ("Watch this. 15 lines of prompt..."), the test-and-fix cycle, and the "let me show you why this matters" transition. The card fades out as the narration pivots to "This isn't nostalgia. It's economics."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Title Text
- "THE ECONOMICS" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "OF DARNING" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 280px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 1" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Ghost (crossing lines)
- Two crossing lines: one descending (`#D9944A` at 0.04), one ascending (`#4A90D9` at 0.04), 1.5px stroke
- Crossing point: subtle radial glow at intersection, `#FFFFFF` at 0.02, 30px radius

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 1" label fades in. Ghost crossing lines draw with stroke-dashoffset.
3. **Frame 40-60 (1.33-2s):** "THE ECONOMICS" types on character-by-character (2 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "OF DARNING" fades in with 10px upward slide.
6. **Frame 90-660 (3-22s):** Hold. Ghost lines pulse subtly. Title stays visible through demo recap narration.
7. **Frame 660-720 (22-24s):** Title and elements fade out, transitioning to price chart.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "OF DARNING" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost lines draw: `easeInOut(cubic)` over 30 frames
- Lines pulse: `easeInOut(sine)` on 60-frame cycle
- Final fade-out: `easeIn(quad)` over 60 frames

## Narration Sync
> "Watch this. 15 lines of prompt. Two hundred lines of generated code."
> "Now a failing test. Regenerate. Bug gone. Not patched — gone. The test is a permanent wall. That bug can never come back."
> "Now, let me show you why this matters."

Segments: `part1_economics_001`, `part1_economics_002`, `part1_economics_003`

- **0.00s** (seg 001): Title card begins fade-in
- **6.70s** (seg 001 ends): "THE ECONOMICS" typing visible
- **7.54s** (seg 002): Title fully visible, hold during demo recap
- **20.60s** (seg 002 ends): Hold
- **20.80s** (seg 003): "Now let me show you why this matters"
- **23.34s** (seg 003 ends): Title begins fade-out

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={720}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost crossing lines */}
    <Sequence from={15}>
      <StrokeDraw duration={30}>
        <CrossingLines
          lineA={{ color: "#D9944A", opacity: 0.04 }}
          lineB={{ color: "#4A90D9", opacity: 0.04 }}
          strokeWidth={1.5}
        />
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
        charDelay={2} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[820, 505]} to={[1100, 505]}
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

    {/* Fade out */}
    <Sequence from={660}>
      <FadeOut duration={60} />
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
    { "shape": "crossing_lines", "colors": ["#D9944A", "#4A90D9"], "role": "cost_crossing_preview" }
  ],
  "narrationSegments": ["part1_economics_001", "part1_economics_002", "part1_economics_003"]
}
```

---
