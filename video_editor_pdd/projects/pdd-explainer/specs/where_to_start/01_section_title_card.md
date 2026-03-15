[title:]

# Section 6.1: Where to Start — Title Card

**Tool:** Remotion
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 22:20 - 22:24

## Visual Description
A clean section title card transitioning from theory to practice. The heading "Where to Start" fades in at center, accompanied by a stylized compass-needle icon that rotates from pointing upward (abstract/theory) to pointing right (forward/action). Below the title, a thin accent line expands and the subtitle "Part 6" drifts into view. The icon signals a tonal shift — the video is now giving the viewer a practical roadmap. Dark navy background consistent with the series.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Title Text:** "Where to Start" — white `#FFFFFF`, centered at Y=370px
- **Compass Icon:** Centered at Y=460px, 60px x 60px
  - Circle outline: `rgba(255,255,255,0.15)`, 2px stroke, 60px diameter
  - Needle: 28px long, `#4A90D9` at 0.7 opacity, 2px wide, pivots from center
  - Tip accent dot: `#4A90D9`, 4px radius, at needle tip
- **Accent Line:** Thin horizontal rule — `rgba(255,255,255,0.7)`, centered at Y=530px, 320px wide x 2px tall
- **Subtitle Text:** "Part 6" — muted slate `#94A3B8`, centered at Y=570px

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Title text fades in (opacity 0→1) and scales up (0.85→1.0) from center
2. **Frame 15-50 (0.50-1.67s):** Compass icon fades in — circle outline appears, needle rotates from 0° (pointing up) to 90° (pointing right) with a slight overshoot and settle
3. **Frame 45-70 (1.50-2.33s):** Accent line expands from 0px to 320px width, drawing outward from center
4. **Frame 60-85 (2.0-2.83s):** Subtitle "Part 6" fades in with 12px upward drift
5. **Frame 85-120 (2.83-4.0s):** Hold at final state

### Typography
- Title: Inter, 64px, bold (700), `#FFFFFF`
- Subtitle: Inter, 28px, regular (400), `#94A3B8`

### Easing
- Title fade/scale: `easeOut(quad)`
- Compass circle fade: `easeOut(quad)`
- Needle rotation: `easeOut(back(1.4))`
- Accent line expand: `easeOut(cubic)`
- Subtitle fade/drift: `easeOut(quad)`

## Narration Sync
> "So — you're convinced. Or at least curious. Where do you actually begin?"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <TitleText text="Where to Start" fontSize={64} />
  <Sequence from={15}>
    <CompassIcon size={60} y={460}>
      <CircleOutline color="rgba(255,255,255,0.15)" strokeWidth={2} />
      <RotatingNeedle
        fromAngle={0}
        toAngle={90}
        color="#4A90D9"
        length={28}
      />
    </CompassIcon>
  </Sequence>
  <Sequence from={45}>
    <AccentLine targetWidth={320} color="rgba(255,255,255,0.7)" />
  </Sequence>
  <Sequence from={60}>
    <SubtitleText text="Part 6" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": "Where to Start",
  "subtitle": "Part 6",
  "accentLineWidth": 320,
  "backgroundColor": "#0F172A",
  "titleColor": "#FFFFFF",
  "subtitleColor": "#94A3B8",
  "icon": {
    "type": "compass",
    "size": 60,
    "needleColor": "#4A90D9",
    "outlineColor": "rgba(255,255,255,0.15)",
    "rotationFrom": 0,
    "rotationTo": 90
  }
}
```

---
