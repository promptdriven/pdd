[title:]

# Section 1.1: The Economics of Code — Section Title Card

**Tool:** Title
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 0:00 - 0:16

## Visual Description

A section title card introducing the economics argument. "THE ECONOMICS" appears first in large bold weight, then "OF CODE" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost silhouette of two crossing lines (the sock/code cost analogy) sits at low opacity — a descending curve and an ascending curve that cross in the middle of the frame. The shape previews the economic crossover theme of the section. Background is deep navy-black.

The title holds for the opening beats: "Watch this." (a dramatic cold open), then "15 lines of prompt. 200 lines of code." and continues through the PDD demo setup, transitioning into the economics argument with "isn't nostalgia. It's economics."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Title Text
- "THE ECONOMICS" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "OF CODE" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 240px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 1" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Ghost (crossing lines)
- Descending curve: bezier from top-left (300, 300) to bottom-right (1600, 700), `#4A90D9` at 0.03, 2px stroke
- Ascending curve: bezier from bottom-left (300, 700) to top-right (1600, 300), `#D9944A` at 0.03, 2px stroke
- Intersection point: subtle glow at crossing (~960, 500), `#FFFFFF` at 0.02, 20px radius

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 1" label fades in. Ghost crossing lines draw with stroke-dashoffset.
3. **Frame 40-60 (1.33-2s):** "THE ECONOMICS" types on character-by-character (2 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "OF CODE" fades in with 10px upward slide.
6. **Frame 90-480 (3-16s):** Hold. Ghost lines pulse subtly. Title fades out at end.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "OF CODE" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost lines draw: `easeInOut(cubic)` over 30 frames
- Lines pulse: `easeInOut(sine)` on 60-frame cycle

## Narration Sync
> "Watch this."
> "15 lines of prompt. 200 lines of code."
> "Now a failing test. Regenerate."
> "Now, let me show you why what you just saw isn't nostalgia. It's economics."

Segments: `part1_economics_001`, `part1_economics_002`, `part1_economics_003`, `part1_economics_004`, `part1_economics_005`

- **0.00s** ("Watch this"): Title card begins fade-in
- **0.74s** ("15 lines of prompt"): "THE ECONOMICS" typing on screen
- **4.50s** ("Now a failing test"): Title fully visible, hold
- **16.16s** ("Now, let me show you"): Title begins transition to price chart
- **19.86s** ("isn't nostalgia. It's economics"): Title fading out

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost crossing lines */}
    <Sequence from={15}>
      <StrokeDraw duration={30}>
        <BezierCurve
          points={[[300, 300], [600, 500], [960, 500], [1600, 700]]}
          color="#4A90D9" opacity={0.03} strokeWidth={2} />
        <BezierCurve
          points={[[300, 700], [600, 500], [960, 500], [1600, 300]]}
          color="#D9944A" opacity={0.03} strokeWidth={2} />
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
      <DrawLine from={[840, 505]} to={[1080, 505]}
        color="#334155" opacity={0.5} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Title: OF CODE */}
    <Sequence from={70}>
      <SlideUp distance={10} duration={20}>
        <FadeIn duration={20}>
          <Text text="OF CODE" font="Inter" size={72}
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
  "titleLine2": "OF CODE",
  "backgroundColor": "#0A0F1A",
  "ghostElements": [
    { "shape": "bezier_curve", "color": "#4A90D9", "role": "descending_cost" },
    { "shape": "bezier_curve", "color": "#D9944A", "role": "ascending_cost" }
  ],
  "narrationSegments": ["part1_economics_001", "part1_economics_002", "part1_economics_003", "part1_economics_004", "part1_economics_005"]
}
```

---
