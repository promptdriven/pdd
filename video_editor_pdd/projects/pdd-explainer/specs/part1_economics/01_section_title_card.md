[title:]

# Section 1.0: Part 1 Section Title — The Economics of Darning

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 2:30 - 2:34

## Visual Description

A clean section title card marks the transition from the 30-second demo into the economics argument. The screen clears to the video's dark background, and "Part 1" appears as a small label above the main title "The Economics of Darning." Below, a thin horizontal rule and a faint subtitle: "Why patching was rational — and when it stopped."

The mood shifts from the punchy demo energy to grounded, explanatory authority. The title uses warm amber (`#D9944A`) — the "patching / traditional" color from the palette — because this section examines the cost of patching before revealing the alternative.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (dark IDE background, consistent with video)
- No code underlay — clean slate for the new section

### Chart/Visual Elements

#### Part Label
- "Part 1" — Inter, 14px, semi-bold (600), `#94A3B8` at 0.4, letter-spacing 4px, uppercase, centered at y: 420

#### Title Text
- "The Economics of Darning" — Inter, 52px, bold (700), `#D9944A` at 0.92, centered at y: 500

#### Horizontal Rule
- 120px wide, 2px, `#D9944A` at 0.2, centered at y: 555, draws from center outward

#### Subtitle
- "Why patching was rational — and when it stopped." — Inter, 16px, weight 300 (light), italic, `#94A3B8` at 0.4, centered at y: 585

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Fade up from previous shot. Background settles to `#0D1117`.
2. **Frame 15-35 (0.5-1.17s):** "Part 1" label fades in with 6px upward slide.
3. **Frame 35-60 (1.17-2s):** Title "The Economics of Darning" fades in with 10px upward slide.
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** Subtitle fades in.
6. **Frame 90-120 (3-4s):** Hold. Title sits with authority.

### Typography
- Part label: Inter, 14px, semi-bold (600), `#94A3B8` at 0.4, uppercase, letter-spacing 4px
- Title: Inter, 52px, bold (700), `#D9944A` at 0.92
- Subtitle: Inter, 16px, light (300), italic, `#94A3B8` at 0.4

### Easing
- Part label fade-in + slide: `easeOut(cubic)` over 15 frames
- Title fade-in + slide: `easeOut(cubic)` over 20 frames
- Rule draw: `easeOut(cubic)` over 10 frames
- Subtitle fade-in: `easeOut(quad)` over 15 frames

## Narration Sync
> "This isn't nostalgia. It's economics."

Segment: `part1_economics_001`

- **2:30** ("This isn't nostalgia"): Title card fully visible
- **2:33** ("It's economics"): Hold — title reinforces the word "economics"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Part label */}
    <Sequence from={15}>
      <SlideUp distance={6} duration={15}>
        <FadeIn duration={15}>
          <Text text="PART 1" font="Inter" size={14}
            weight={600} color="#94A3B8" opacity={0.4}
            letterSpacing={4}
            x={960} y={420} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Title */}
    <Sequence from={35}>
      <SlideUp distance={10} duration={20}>
        <FadeIn duration={20}>
          <Text text="The Economics of Darning" font="Inter" size={52}
            weight={700} color="#D9944A" opacity={0.92}
            x={960} y={500} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[900, 555]} to={[1020, 555]}
        color="#D9944A" opacity={0.2} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Subtitle */}
    <Sequence from={70}>
      <FadeIn duration={15}>
        <Text text="Why patching was rational — and when it stopped."
          font="Inter" size={16} weight={300}
          fontStyle="italic"
          color="#94A3B8" opacity={0.4}
          x={960} y={585} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": 1,
  "sectionLabel": "Part 1",
  "title": "The Economics of Darning",
  "titleColor": "#D9944A",
  "subtitle": "Why patching was rational — and when it stopped.",
  "subtitleColor": "#94A3B8",
  "backgroundColor": "#0D1117",
  "narrationSegments": ["part1_economics_001"]
}
```

---
