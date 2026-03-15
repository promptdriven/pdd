[title:]

# Section 2.1: The Paradigm Shift — Title Card

**Tool:** Remotion
**Duration:** ~3s (90 frames @ 30fps)
**Timestamp:** 8:30 - 8:33

## Visual Description
A section title card introducing Part 2. The heading "The Paradigm Shift" fades in with a subtle scale-up from center. Beneath it, a thin horizontal accent line expands outward, followed by the subtitle "Part 2" drifting upward into position. A geometric motif — an abstract injection mold cross-section outline (two converging trapezoidal walls with a cavity between them) — traces itself in the lower third, drawn with a single continuous stroke, then fades to a subtle ghost. The palette shifts slightly warmer than Part 1, hinting at the industrial theme ahead.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Title Text:** "The Paradigm Shift" — white `#FFFFFF`, centered at Y=420px
- **Accent Line:** Thin horizontal rule — `rgba(255, 255, 255, 0.7)`, centered at Y=490px, 400px wide x 2px tall
- **Subtitle Text:** "Part 2" — muted slate `#94A3B8`, centered at Y=540px
- **Mold Outline Motif:** Single-stroke outline of a simplified injection mold cross-section, 2px stroke `rgba(42, 161, 152, 0.25)` (teal ghost), centered horizontally at Y=740, 360px wide x 80px tall. Two angled walls converging to a cavity shape

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Title text fades in (opacity 0→1) and scales up (0.85→1.0) from center
2. **Frame 15-35 (0.5-1.17s):** Accent line expands from 0px to 400px width, centered horizontally
3. **Frame 25-45 (0.83-1.5s):** Subtitle "Part 2" fades in (opacity 0→1) with a 12px upward drift
4. **Frame 30-70 (1.0-2.33s):** Mold outline motif draws as a continuous stroke (stroke-dashoffset reveal), left wall → cavity bottom → right wall
5. **Frame 70-90 (2.33-3.0s):** Hold all elements. Mold outline fades to 0.08 opacity

### Typography
- Title: Inter, 64px, bold (700), `#FFFFFF`
- Subtitle: Inter, 28px, regular (400), `#94A3B8`

### Easing
- Title fade/scale: `easeOut(quad)`
- Accent line expand: `easeOut(cubic)`
- Subtitle fade/drift: `easeOut(quad)`
- Mold outline draw: `easeInOut(cubic)`

## Narration Sync
> "There's a pattern here that shows up across industries. Not just cheaper materials — a deeper shift in how things are made."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <TitleText text="The Paradigm Shift" fontSize={64} />
  <Sequence from={15}>
    <AccentLine targetWidth={400} color="rgba(255,255,255,0.7)" />
  </Sequence>
  <Sequence from={25}>
    <SubtitleText text="Part 2" />
  </Sequence>
  <Sequence from={30}>
    <MoldOutlineMotif
      width={360}
      height={80}
      y={740}
      strokeColor="rgba(42, 161, 152, 0.25)"
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": "The Paradigm Shift",
  "subtitle": "Part 2",
  "accentLineWidth": 400,
  "backgroundColor": "#0F172A",
  "titleColor": "#FFFFFF",
  "subtitleColor": "#94A3B8",
  "accentLineColor": "rgba(255, 255, 255, 0.7)",
  "moldMotif": {
    "strokeColor": "rgba(42, 161, 152, 0.25)",
    "strokeWidth": 2,
    "width": 360,
    "height": 80,
    "y": 740
  }
}
```

---
