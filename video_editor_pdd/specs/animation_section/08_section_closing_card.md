[title:]

# Section 1.8: Section Closing Card

**Tool:** Remotion
**Duration:** ~1.5s (45 frames)
**Timestamp:** 0:06 - 0:07

## Visual Description
A minimal closing card that bookends the Animation Section. The screen fades to the original navy-blue gradient from the title card. A centered tagline "Section Complete" appears in muted slate text, with a small checkmark icon above it that draws itself on (SVG path animation). A subtle horizontal rule expands below the text. The card provides visual closure before the next section begins.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Linear gradient 180deg from #0A1628 (top) to #1E3A8A (bottom) — mirrors the opening title card
- No grid lines

### Chart/Visual Elements
- **Checkmark icon:** SVG circle (64px diameter) with animated checkmark stroke inside, centered at (960, 440), stroke color #22C55E, stroke-width 3px
- **Tagline:** "Section Complete" centered at (960, 540), color #94A3B8
- **Horizontal rule:** 200px wide, 2px tall, centered at (960, 590), color #3B82F6, expands from center
- **Background particles (faint):** 20 particles from the title card system, reduced opacity (0.1-0.3), drifting slowly — visual continuity with the opening

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Background gradient fades in from black (opacity 0→1)
2. **Frame 5-25 (0.17-0.83s):** Checkmark circle draws (SVG stroke-dasharray animation), then checkmark path draws inside
3. **Frame 15-30 (0.5-1.0s):** "Section Complete" text fades in (opacity 0→1)
4. **Frame 25-40 (0.83-1.33s):** Horizontal rule expands from width 0 to 200px, centered
5. **Frame 35-45 (1.17-1.5s):** Entire card begins fading out (opacity 1→0.7) as section ends

### Typography
- Tagline: Inter, 36px, normal (400), #94A3B8, letter-spacing 2px, text-transform uppercase

### Easing
- Background fade: `easeOutQuad`
- Checkmark draw: `easeInOutCubic`
- Text fade-in: `easeOutQuad`
- Rule expand: `easeInOutQuad`
- Card fade-out: `easeInQuad`

## Narration Sync
> (No narration — this card plays after the spoken content ends)

The closing card occupies the tail of the section (6.0s-7.32s), after both narration segments have concluded. It provides a visual beat of silence before the next section's audio begins.

## Code Structure (Remotion)
```typescript
<Sequence from={180} durationInFrames={45}>
  <AbsoluteFill
    style={{
      background: 'linear-gradient(180deg, #0A1628, #1E3A8A)',
      opacity: backgroundOpacity,
    }}
  >
    {/* Faint background particles */}
    <ParticleSystem count={20} speed={1} color="#3B82F6" opacityRange={[0.1, 0.3]} />

    {/* Animated checkmark */}
    <Sequence from={5} durationInFrames={20}>
      <AnimatedCheckmark cx={960} cy={440} radius={32} strokeColor="#22C55E" />
    </Sequence>

    {/* Tagline */}
    <Sequence from={15} durationInFrames={15}>
      <FadeInText
        text="SECTION COMPLETE"
        x={960}
        y={540}
        fontSize={36}
        color="#94A3B8"
        letterSpacing="2px"
      />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={25} durationInFrames={15}>
      <ExpandingRule cx={960} cy={590} maxWidth={200} color="#3B82F6" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "tagline": "SECTION COMPLETE",
  "checkmark": {
    "cx": 960,
    "cy": 440,
    "radius": 32,
    "strokeColor": "#22C55E"
  },
  "rule": {
    "cx": 960,
    "cy": 590,
    "maxWidth": 200,
    "color": "#3B82F6"
  },
  "backgroundGradient": ["#0A1628", "#1E3A8A"]
}
```

---
