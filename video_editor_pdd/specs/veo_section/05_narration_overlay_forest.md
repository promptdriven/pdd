[Remotion]

# Section 2.5: Narration Text Overlay — Forest

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:05 - 0:08

## Visual Description
A lower-third narration overlay that appears over the aerial forest canopy footage. The text "It uses Veo-generated clips with narration overlay" slides in from the right as a frosted glass pill, positioned in the lower third of the frame. The text is white against a blurred semi-transparent dark backdrop, allowing the green forest footage to remain visible beneath. A thin emerald accent bar pulses once along the left edge of the pill to signal the new narration beat.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent (overlaid on Veo clip)
- Grid lines: none

### Chart/Visual Elements
- Pill container: 900px wide, 72px tall, centered horizontally at y=920, border-radius 36px
- Pill background: rgba(0, 0, 0, 0.55) with backdrop-filter blur(12px)
- Text content: "It uses Veo-generated clips with narration overlay."
- Accent bar: 4px wide, 48px tall, left edge of pill (x inset 16px), color #34D399 (emerald)
- Subtle border: 1px solid rgba(255, 255, 255, 0.12)

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Pill slides in from right (translateX +200px → 0px) while fading in (opacity 0→1).
2. **Frame 10-20 (0.33-0.67s):** Accent bar scales in vertically (scaleY 0→1) with a slight glow pulse.
3. **Frame 12-55 (0.4-1.83s):** Text reveals left-to-right via clip-path (inset right 100%→0%).
4. **Frame 55-75 (1.83-2.5s):** Hold. Full text visible.
5. **Frame 75-90 (2.5-3.0s):** Pill slides out to left (translateX 0 → -200px) with fade-out (opacity 1→0).

### Typography
- Subtitle text: Inter Medium, 28px, white (#FFFFFF), letter-spacing 0.3px
- Text shadow: 0 1px 6px rgba(0,0,0,0.4)

### Easing
- Pill slide-in: `easeOutCubic`
- Accent bar: `easeOutBack` (slight overshoot)
- Text reveal: `easeInOutQuad`
- Pill slide-out: `easeInCubic`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={150} durationInFrames={90}>
  <AbsoluteFill style={{ justifyContent: "flex-end", alignItems: "center" }}>
    <SlideIn direction="right" distance={200} duration={15}>
      <FrostedPill width={900} height={72} blur={12} opacity={0.55}>
        <Sequence from={10}>
          <AccentBar width={4} height={48} color="#34D399" />
        </Sequence>
        <Sequence from={12}>
          <ClipReveal direction="left-to-right" duration={43}>
            <NarrationText
              text="It uses Veo-generated clips with narration overlay."
              font="Inter Medium"
              size={28}
              color="#FFFFFF"
            />
          </ClipReveal>
        </Sequence>
      </FrostedPill>
    </SlideIn>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "narrationText": "It uses Veo-generated clips with narration overlay.",
  "pillWidth": 900,
  "pillHeight": 72,
  "accentColor": "#34D399",
  "blurRadius": 12,
  "textPositionY": 920
}
```

---
