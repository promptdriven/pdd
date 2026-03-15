[title:]

# Section 1.1: The Economics of Darning — Title Card

**Tool:** Remotion
**Duration:** ~3s (90 frames @ 30fps)
**Timestamp:** 2:30 - 2:33

## Visual Description
A section title card introducing Part 1. The heading "The Economics of Darning" fades in and scales up from center, followed by a thin horizontal accent line expanding outward beneath it, then the subtitle "Part 1" drifts upward into view. A subtle darning-needle icon (thin line with a trailing thread curve) traces across the bottom third and fades out. All elements are centered on a deep navy background consistent with the project palette.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark slate `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Title Text:** "The Economics of Darning" — white `#FFFFFF`, centered at Y=420px
- **Accent Line:** Thin horizontal rule — `rgba(255, 255, 255, 0.7)`, centered at Y=490px, 400px wide x 2px tall
- **Subtitle Text:** "Part 1" — muted slate `#94A3B8`, centered at Y=540px
- **Needle Trace:** Thin curved path (2px stroke, `rgba(255,255,255,0.15)`) sweeping from X=300 to X=1620 at Y=750, with a slight sine-wave wobble (amplitude 8px, 2 periods)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Title text fades in (opacity 0→1) and scales up (0.85→1.0) from center
2. **Frame 15-35 (0.5-1.17s):** Accent line expands from 0px to 400px width, centered horizontally
3. **Frame 25-45 (0.83-1.5s):** Subtitle "Part 1" fades in (opacity 0→1) with a 12px upward drift
4. **Frame 30-70 (1.0-2.33s):** Needle trace draws left-to-right along its curved path (stroke-dashoffset reveal)
5. **Frame 70-90 (2.33-3.0s):** Hold all elements at final state, needle trace fades to 0.05 opacity

### Typography
- Title: Inter, 64px, bold (700), `#FFFFFF`
- Subtitle: Inter, 28px, regular (400), `#94A3B8`

### Easing
- Title fade/scale: `easeOut(quad)`
- Accent line expand: `easeOut(cubic)`
- Subtitle fade/drift: `easeOut(quad)`
- Needle trace draw: `easeInOut(cubic)`

## Narration Sync
> "This isn't nostalgia. It's economics."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <TitleText text="The Economics of Darning" fontSize={64} />
  <Sequence from={15}>
    <AccentLine targetWidth={400} color="rgba(255,255,255,0.7)" />
  </Sequence>
  <Sequence from={25}>
    <SubtitleText text="Part 1" />
  </Sequence>
  <Sequence from={30}>
    <NeedleTrace
      startX={300}
      endX={1620}
      y={750}
      amplitude={8}
      periods={2}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": "The Economics of Darning",
  "subtitle": "Part 1",
  "accentLineWidth": 400,
  "backgroundColor": "#0F172A",
  "titleColor": "#FFFFFF",
  "subtitleColor": "#94A3B8",
  "accentLineColor": "rgba(255, 255, 255, 0.7)",
  "needleTrace": {
    "strokeColor": "rgba(255, 255, 255, 0.15)",
    "strokeWidth": 2,
    "y": 750,
    "amplitude": 8,
    "periods": 2
  }
}
```

---
