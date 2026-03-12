[title:]

# Section 1.1: Animation Section Title Card

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:00 - 0:03

## Visual Description
A clean title card introducing the Animation Section. The text "Animation Section" fades in letter-by-letter against a dark navy background, with a thin horizontal rule expanding outward from center beneath it. A subtle gradient glow pulses once behind the title.

## Technical Specifications

### Canvas
- Resolution: 1280x720 (16:9)
- Background: Dark navy (#0B1120) with radial gradient center glow (#1A2744)

### Chart/Visual Elements
- Title text: "Animation Section" centered horizontally and vertically
- Horizontal divider line: 200px wide, 2px height, white (#FFFFFF) at 40% opacity, positioned 20px below title baseline
- Gradient glow: radial gradient circle, 300px radius, centered behind title, #2E4A7A at 30% opacity

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Radial glow begins expanding from 0 to 300px radius.
2. **Frame 15-45 (0.5-1.5s):** Title text appears letter-by-letter with stagger (50ms per character), fading from 0% to 100% opacity with 5px upward translate per letter.
3. **Frame 45-60 (1.5-2.0s):** Horizontal divider expands from 0px to 200px width, centered. Radial glow pulses brightness from 30% to 50% opacity and back.
4. **Frame 60-90 (2.0-3.0s):** All elements hold at full visibility. Subtle float animation on title (2px vertical oscillation).

### Typography
- Title: Inter Bold, 56px, white (#FFFFFF)
- Subtitle: none

### Easing
- Letter stagger: `easeOutQuad`
- Divider expansion: `easeInOutCubic`
- Glow pulse: `easeInOutSine`

## Narration Sync
> (No narration — title card plays before first narration segment)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <AbsoluteFill style={{ backgroundColor: '#0B1120' }}>
    <RadialGlow expandTo={300} pulseAt={45} />
    <Sequence from={15}>
      <StaggeredText text="Animation Section" staggerMs={50} />
    </Sequence>
    <Sequence from={45}>
      <ExpandingDivider width={200} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "title": "Animation Section",
  "bgColor": "#0B1120",
  "glowColor": "#2E4A7A",
  "dividerWidth": 200
}
```

---
