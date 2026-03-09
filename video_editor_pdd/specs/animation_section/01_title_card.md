[title:]

# Section 1.1: Animation Section Title Card

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:00 - 0:03

## Visual Description
A bold title card introducing the Animation Section. The text "ANIMATION SECTION" fades in from zero opacity at center screen, with a subtle horizontal rule expanding outward from the center beneath it. The background is a deep navy (#0B1120) with a faint radial gradient highlight behind the title.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep navy (#0B1120) with radial gradient center highlight (#1A2744 at 40% radius)

### Chart/Visual Elements
- Title text: "ANIMATION SECTION" — centered horizontally and vertically, white (#FFFFFF)
- Horizontal rule: 2px solid line, cyan accent (#38BDF8), starts at 0px width and expands to 400px, centered below the title with 16px gap
- Radial glow: Soft circular gradient behind text, 600px diameter, #1A2744 at center fading to transparent

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Radial glow appears at 0% opacity and ramps to 100%.
2. **Frame 15-45 (0.5-1.5s):** Title text fades in from 0% to 100% opacity with a slight upward drift (translateY from +20px to 0).
3. **Frame 45-65 (1.5-2.2s):** Horizontal rule expands from 0px to 400px width with easing.
4. **Frame 65-90 (2.2-3s):** Hold — all elements static at full opacity.

### Typography
- Title: Inter Bold, 72px, #FFFFFF, letter-spacing 6px, uppercase
- No additional labels

### Easing
- Title fade/drift: `easeOutCubic`
- Rule expansion: `easeInOutQuad`

## Narration Sync
> (No narration — title card plays before narrator begins)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <BackgroundGradient />
  <Sequence from={15}>
    <FadeInTitle text="ANIMATION SECTION" />
  </Sequence>
  <Sequence from={45}>
    <ExpandingRule width={400} color="#38BDF8" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": "ANIMATION SECTION",
  "accentColor": "#38BDF8",
  "backgroundColor": "#0B1120"
}
```

---
