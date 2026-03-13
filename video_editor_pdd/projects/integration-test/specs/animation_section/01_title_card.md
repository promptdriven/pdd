[title:]

# Section 1.1: Animation Section Title Card

**Tool:** Remotion
**Duration:** ~1.5s
**Timestamp:** 0:00 - 0:01.5

## Visual Description
A bold title card introduces the Animation Section. The background is a deep navy blue. The title text "Animation Section" fades in from zero opacity while scaling up slightly from 95% to 100%. A thin horizontal accent line (white, 2px) expands outward from the center beneath the title. A subtle subtitle "Integration Test" fades in 0.3s after the title.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep navy #0F172A
- Grid lines: None

### Chart/Visual Elements
- Title text: centered horizontally and vertically, offset 40px above center
- Accent line: centered, 200px wide expanding to 400px, 2px height, white (#FFFFFF) at 80% opacity
- Subtitle: centered, 24px below accent line

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Title text fades in from opacity 0 to 1, scales from 0.95 to 1.0
2. **Frame 9-24 (0.3-0.8s):** Accent line expands from 0px to 400px width
3. **Frame 15-30 (0.5-1.0s):** Subtitle fades in from opacity 0 to 1
4. **Frame 30-45 (1.0-1.5s):** Hold all elements at full visibility

### Typography
- Title: Inter Bold, 72px, white (#FFFFFF)
- Subtitle: Inter Regular, 28px, slate-300 (#CBD5E1)

### Easing
- Title fade/scale: `easeOutCubic`
- Line expansion: `easeInOutQuad`
- Subtitle fade: `easeOutQuad`

## Narration Sync
> "This is the first section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={45}>
  <TitleCard>
    <Sequence from={0}>
      <FadeScale text="Animation Section" />
    </Sequence>
    <Sequence from={9}>
      <ExpandingLine />
    </Sequence>
    <Sequence from={15}>
      <FadeIn text="Integration Test" />
    </Sequence>
  </TitleCard>
</Sequence>
```

## Data Points
```json
{
  "title": "Animation Section",
  "subtitle": "Integration Test"
}
```

---
