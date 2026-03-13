[title:]

# Section 1.1: Animation Section Title Card

**Tool:** Remotion
**Duration:** ~1.1s (33 frames @ 30fps)
**Timestamp:** 0:00 – 0:01

## Visual Description
A dark cinematic title card introducing the Animation Section. The screen opens with a deep navy background featuring a soft radial glow at center. The title text "Animation Section" animates in letter-by-letter with a staggered reveal, centered on screen. A thin horizontal divider line expands outward beneath the title. The glow subtly pulses once the text is fully visible, then the composition holds with gentle floating motion.

## Technical Specifications

### Canvas
- Resolution: 1280x720 (16:9)
- Background: Dark navy gradient (#0B1120)
- Radial glow: centered, #2E4A7A, 400px radius, 0.4 opacity

### Chart/Visual Elements
- **Radial glow:** Centered elliptical gradient from #2E4A7A (center) to transparent, 400px initial radius expanding to 500px
- **Title text:** "Animation Section" — centered horizontally and vertically (offset -20px from center)
- **Divider line:** Horizontal, 2px height, white at 40% opacity, centered 40px below title, expands from 0px to 200px width

### Animation Sequence
1. **Frame 0–5 (0–0.17s):** Background fades in from black. Radial glow begins expanding from 300px to 400px radius.
2. **Frame 5–20 (0.17–0.67s):** Title text staggers in letter-by-letter (1.5 frames per character, 18 characters total). Each letter fades from 0→1 opacity and translates up 8px→0px.
3. **Frame 20–25 (0.67–0.83s):** Divider line expands from 0px to 200px width. Glow pulses to 500px radius and 0.5 opacity.
4. **Frame 25–33 (0.83–1.1s):** Hold composition with gentle floating — title drifts ±2px vertically on a sinusoidal cycle. Glow settles to resting 0.35 opacity.

### Typography
- Title: Inter, 56px, #FFFFFF, font-weight 700 (bold), letter-spacing 2px
- No additional labels

### Easing
- Letter stagger: `easeOutQuad` per character
- Divider expand: `easeInOutCubic`
- Glow pulse: `easeInOutSine`
- Float drift: `sinusoidal` (continuous)

## Narration Sync
> "This is the first section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={33}>
  <AbsoluteFill style={{ backgroundColor: "#0B1120" }}>
    <RadialGlow
      centerColor="#2E4A7A"
      radius={interpolate(frame, [0, 5, 22, 33], [300, 400, 500, 400])}
      opacity={interpolate(frame, [0, 5, 22, 33], [0, 0.4, 0.5, 0.35])}
    />
    <StaggeredTitle
      text="Animation Section"
      startFrame={5}
      framesPerChar={1.5}
      fontSize={56}
      color="#FFFFFF"
    />
    <Sequence from={20}>
      <ExpandingDivider
        width={interpolate(frame, [0, 5], [0, 200], { extrapolateRight: "clamp" })}
        color="rgba(255,255,255,0.4)"
        height={2}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "title": "Animation Section",
  "glowColor": "#2E4A7A",
  "backgroundColor": "#0B1120",
  "dividerWidth": 200,
  "letterCount": 18,
  "framesPerChar": 1.5
}
```

---
