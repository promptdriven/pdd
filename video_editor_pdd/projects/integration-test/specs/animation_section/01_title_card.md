[title:]

# Section 1.1: Title Card

**Tool:** Remotion
**Duration:** ~1.5s (45 frames @ 30fps)
**Timestamp:** 0:00 - 0:01

## Visual Description
A cinematic title card introducing the Animation Section. The title "Animation Section" fades in and scales up from center, followed by a thin horizontal accent line expanding outward beneath it, then the subtitle "Integration Test" drifts upward into view. All elements are centered on a deep navy background.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark slate `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Title Text:** "Animation Section" — white `#FFFFFF`, centered at Y=440px
- **Accent Line:** Thin horizontal rule — `rgba(255, 255, 255, 0.8)`, centered at Y=500px, 320px wide x 2px tall
- **Subtitle Text:** "Integration Test" — muted slate `#94A3B8`, centered at Y=560px

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Title text fades in (opacity 0→1) and scales up (0.85→1.0) from center
2. **Frame 12-30 (0.4-1.0s):** Accent line expands from 0px to 320px width, centered horizontally
3. **Frame 20-40 (0.67-1.33s):** Subtitle fades in (opacity 0→1) with a 10px upward drift
4. **Frame 40-45 (1.33-1.5s):** Hold — all elements at final state

### Typography
- Title: Inter, 72px, bold (700), `#FFFFFF`
- Subtitle: Inter, 28px, regular (400), `#94A3B8`

### Easing
- Title fade/scale: `easeOut(quad)`
- Accent line expand: `easeOut(cubic)`
- Subtitle fade/drift: `easeOut(quad)`

## Narration Sync
> "This is the first section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={45}>
  <TitleText text="Animation Section" />
  <Sequence from={12}>
    <AccentLine targetWidth={320} />
  </Sequence>
  <Sequence from={20}>
    <SubtitleText text="Integration Test" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": "Animation Section",
  "subtitle": "Integration Test",
  "accentLineWidth": 320,
  "backgroundColor": "#0F172A",
  "titleColor": "#FFFFFF",
  "subtitleColor": "#94A3B8",
  "accentLineColor": "rgba(255, 255, 255, 0.8)"
}
```

---
