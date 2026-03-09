[title:]

# Section 2.14: Section Outro

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:39 - 0:42

## Visual Description
A closing card that bookends the Veo section. The screen fades to a deep charcoal background. The text "END OF VEO SECTION" appears centered with a thin horizontal rule above it. A subtle amber line traces a complete rectangle border around the viewport edge, framing the closing message. The overall feel is clean and conclusive.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep charcoal (#0F0F0F) solid fill

### Chart/Visual Elements
- Border frame: 2px inset rectangle, 40px margin from each edge (positioned at 40, 40 to 1880, 1040)
  - Color: #F59E0B at 50% opacity
  - Draws clockwise from top-left corner
- Horizontal rule: 300px wide, 2px, #F59E0B at 60% opacity, centered at Y=480
- Section text: "END OF VEO SECTION" — centered at (960, 540)
- Small diamond ornament: 8x8px rotated square, #F59E0B, centered below text at Y=590

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from footage to solid #0F0F0F.
2. **Frame 10-40 (0.33-1.33s):** Border frame traces clockwise: top edge (10-17), right edge (17-24), bottom edge (24-31), left edge (31-40). Each segment draws with a glowing leading edge.
3. **Frame 25-45 (0.83-1.5s):** Horizontal rule expands from 0px to 300px width.
4. **Frame 35-55 (1.17-1.83s):** Section text fades in from 0% to 100% opacity, slight scale from 0.95 to 1.0.
5. **Frame 50-60 (1.67-2s):** Diamond ornament fades in and rotates 45 degrees into position.
6. **Frame 60-90 (2-3s):** Hold — all elements static. Then slow fade to black over final 10 frames.

### Typography
- Section text: Inter Bold, 48px, #FFFFFF at 90% opacity, letter-spacing 6px, uppercase
- No additional labels

### Easing
- Border trace: `linear` per segment
- Rule expansion: `easeInOutQuad`
- Text fade/scale: `easeOutCubic`
- Diamond rotation: `easeOutBack`
- Final fade to black: `easeInQuad`

## Narration Sync
> (No narration — closing card)

## Code Structure (Remotion)
```typescript
<Sequence from={1170} durationInFrames={90}>
  <SolidBackground color="#0F0F0F" />
  <Sequence from={10}>
    <BorderTrace
      margin={40}
      color="#F59E0B"
      opacity={0.5}
      drawDuration={30}
    />
  </Sequence>
  <Sequence from={25}>
    <ExpandingRule width={300} color="#F59E0B" y={480} />
  </Sequence>
  <Sequence from={35}>
    <FadeInTitle text="END OF VEO SECTION" fontSize={48} />
  </Sequence>
  <Sequence from={50}>
    <DiamondOrnament color="#F59E0B" y={590} />
  </Sequence>
  <Sequence from={80}>
    <FadeToBlack />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": "END OF VEO SECTION",
  "accentColor": "#F59E0B",
  "backgroundColor": "#0F0F0F",
  "borderMargin": 40
}
```

---
