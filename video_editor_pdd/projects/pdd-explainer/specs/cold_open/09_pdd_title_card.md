[title:]

# Section 0.9: PDD Title Card — Prompt-Driven Development

**Tool:** Title
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:39 - 0:45

## Visual Description

The main title card for the video. From the dark void left by the fading question, a horizontal rule — thin, luminous — draws itself across the center of the screen. Then the title rises from behind the line: "Prompt-Driven Development" in large, confident typography. Below the line, a subtitle fades in: "Why You're Still Darning Socks". The title treatment is minimal and authoritative — no flashy 3D, no gradients, just clean type on a dark canvas with a single accent color. A subtle constellation of small dots (`·`) orbits slowly in the background, evoking a circuit board or neural network — barely visible, adding texture without competing with the title.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy, slightly richer than IDE black)
- Background dots: 40-60 small circles, 1-2px, `#4A90D9` at 0.06, positioned randomly, drifting at 0.3px/s

### Chart/Visual Elements

**Horizontal Rule**
- Position: y: 510, extending from x: 460 to x: 1460 (1000px wide, centered)
- Color: gradient from `#4A90D9` (center) to `transparent` (edges)
- Height: 1px
- Glow: `#4A90D9` at 0.12, 4px blur beneath the line

**Title Text**
- Text: "Prompt-Driven Development"
- Font: Inter Bold, 64px
- Color: `#E6EDF3` at 0.95
- Position: centered horizontally (x: 960), y: 460 (above the line)
- Letter-spacing: -1px

**Subtitle Text**
- Text: "Why You're Still Darning Socks"
- Font: Inter Regular, 24px
- Color: `#8B949E` at 0.7
- Position: centered horizontally (x: 960), y: 568 (below the line)
- Letter-spacing: 2px (spaced out for subtitle feel)
- Text-transform: uppercase

### Animation Sequence
1. **Frame 0-30 (0-1s):** Horizontal rule draws from center outward — starts as a single point at x: 960, expands to full 1000px width. The line glow appears simultaneously.
2. **Frame 30-60 (1-2s):** Title text rises upward from y: 510 → y: 460 (rises 50px from behind the line) while fading in from opacity 0 → 0.95. The motion is slow and deliberate.
3. **Frame 50-80 (1.67-2.67s):** Subtitle fades in beneath the line: opacity 0 → 0.7. No vertical motion — it simply materializes. Overlaps slightly with title animation finishing.
4. **Frame 80-150 (2.67-5s):** Hold on complete title card. Background dots drift slowly. The composition breathes.
5. **Frame 150-180 (5-6s):** Everything fades out together — title, subtitle, line, dots. Opacity → 0 over 30 frames. Transition to the 30-second demo.

### Typography
- Title: Inter Bold, 64px, `#E6EDF3` at 0.95, letter-spacing: -1px
- Subtitle: Inter Regular, 24px, `#8B949E` at 0.7, letter-spacing: 2px, uppercase

### Easing
- Rule draw: `easeInOut(cubic)` — accelerates from center, decelerates at edges
- Title rise: `easeOut(cubic)` — decelerating rise, confident stop
- Subtitle fade: `easeOut(quad)` — gentle appearance
- Background dots drift: `linear` — constant, imperceptible
- Final fade-out: `easeIn(quad)` — slow start, steady exit

## Narration Sync
> (No narration during title card. Music swell or ambient tone fills the beat.)

| Segment ID | Text | Sync Point |
|---|---|---|
| `cold_open_010` | (silence — title card beat) | Frame 60 — title fully visible, subtitle appearing |

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <AbsoluteFill style={{ backgroundColor: "#0A0F1A" }}>
    {/* Background constellation dots */}
    <DriftingDots
      count={50}
      size={[1, 2]}
      color="#4A90D9"
      opacity={0.06}
      speed={0.3}
    />

    {/* Horizontal rule — draws from center */}
    <Sequence from={0} durationInFrames={30}>
      <DrawLine
        y={510}
        fromX={960}
        toLeft={460}
        toRight={1460}
        color="#4A90D9"
        height={1}
        glow={{ color: "#4A90D9", opacity: 0.12, blur: 4 }}
      />
    </Sequence>

    {/* Title — rises from behind the line */}
    <Sequence from={30} durationInFrames={30}>
      <RiseIn fromY={510} toY={460}>
        <Text
          text="Prompt-Driven Development"
          font="Inter"
          weight={700}
          size={64}
          color="#E6EDF3"
          opacity={0.95}
          align="center"
          letterSpacing={-1}
        />
      </RiseIn>
    </Sequence>

    {/* Subtitle — fades in below the line */}
    <Sequence from={50} durationInFrames={30}>
      <FadeIn duration={30}>
        <Text
          text="WHY YOU'RE STILL DARNING SOCKS"
          font="Inter"
          weight={400}
          size={24}
          color="#8B949E"
          opacity={0.7}
          y={568}
          align="center"
          letterSpacing={2}
        />
      </FadeIn>
    </Sequence>

    {/* Final fade out */}
    <Sequence from={150} durationInFrames={30}>
      <FadeOut duration={30}>
        {/* All elements inherit this fade */}
      </FadeOut>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "title": {
    "text": "Prompt-Driven Development",
    "font": { "family": "Inter", "weight": 700, "size": 64 },
    "color": "#E6EDF3",
    "opacity": 0.95,
    "position": { "x": 960, "y": 460 },
    "letterSpacing": -1
  },
  "subtitle": {
    "text": "WHY YOU'RE STILL DARNING SOCKS",
    "font": { "family": "Inter", "weight": 400, "size": 24 },
    "color": "#8B949E",
    "opacity": 0.7,
    "position": { "x": 960, "y": 568 },
    "letterSpacing": 2
  },
  "rule": {
    "y": 510,
    "xRange": [460, 1460],
    "color": "#4A90D9",
    "glow": { "opacity": 0.12, "blur": 4 }
  },
  "background": {
    "color": "#0A0F1A",
    "dots": { "count": 50, "color": "#4A90D9", "opacity": 0.06, "speed": 0.3 }
  },
  "timing": {
    "ruleDrawFrames": [0, 30],
    "titleRiseFrames": [30, 60],
    "subtitleFadeFrames": [50, 80],
    "holdFrames": [80, 150],
    "fadeOutFrames": [150, 180]
  },
  "narrationSegments": ["cold_open_010"]
}
```
