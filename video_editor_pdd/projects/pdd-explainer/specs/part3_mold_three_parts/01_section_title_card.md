[title:]

# Section 3.1: The Mold Has Three Parts — Title Card

**Tool:** Remotion
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 13:00 - 13:04

## Visual Description
A section title card introducing Part 3. The heading "The Mold Has Three Parts" fades in at center, accompanied by a stylized mold cross-section icon that draws itself beneath the text — three distinct regions pulse one by one in blue, amber, and green (corresponding to prompt, tests, and grounding). The subtitle "Part 3" drifts upward below. All on the standard dark navy background.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark slate `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Title Text:** "The Mold Has Three Parts" — white `#FFFFFF`, centered at Y=380px
- **Mold Icon:** Simplified cross-section outline (trapezoidal mold shape, 200px wide x 80px tall) centered at Y=470px, stroke `rgba(255,255,255,0.5)`, 2px
  - Left wall region: `#D9944A` (amber) fill at 0.3 opacity
  - Center nozzle region: `#4A90D9` (blue) fill at 0.3 opacity
  - Right material region: `#5AAA6E` (green) fill at 0.3 opacity
- **Accent Line:** Thin horizontal rule — `rgba(255,255,255,0.7)`, centered at Y=530px, 400px wide x 2px tall
- **Subtitle Text:** "Part 3" — muted slate `#94A3B8`, centered at Y=570px

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Title text fades in (opacity 0→1) and scales up (0.85→1.0) from center
2. **Frame 20-50 (0.67-1.67s):** Mold icon outline draws in (stroke-dashoffset reveal)
3. **Frame 45-60 (1.5-2.0s):** Amber wall region pulses to 0.5 opacity, then settles at 0.3
4. **Frame 55-70 (1.83-2.33s):** Blue nozzle region pulses to 0.5 opacity, then settles at 0.3
5. **Frame 65-80 (2.17-2.67s):** Green material region pulses to 0.5 opacity, then settles at 0.3
6. **Frame 40-65 (1.33-2.17s):** Accent line expands from 0px to 400px width
7. **Frame 60-85 (2.0-2.83s):** Subtitle "Part 3" fades in with 12px upward drift
8. **Frame 85-120 (2.83-4.0s):** Hold at final state

### Typography
- Title: Inter, 64px, bold (700), `#FFFFFF`
- Subtitle: Inter, 28px, regular (400), `#94A3B8`

### Easing
- Title fade/scale: `easeOut(quad)`
- Mold icon draw: `easeInOut(cubic)`
- Region pulses: `easeInOut(sine)`
- Accent line expand: `easeOut(cubic)`
- Subtitle fade/drift: `easeOut(quad)`

## Narration Sync
> "Now let's get precise. Because 'prompt is the mold' is a nice metaphor, but it's incomplete."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <TitleText text="The Mold Has Three Parts" fontSize={64} />
  <Sequence from={20}>
    <MoldIcon width={200} height={80} y={470} />
  </Sequence>
  <Sequence from={45}>
    <RegionPulse region="walls" color="#D9944A" />
  </Sequence>
  <Sequence from={55}>
    <RegionPulse region="nozzle" color="#4A90D9" />
  </Sequence>
  <Sequence from={65}>
    <RegionPulse region="material" color="#5AAA6E" />
  </Sequence>
  <Sequence from={40}>
    <AccentLine targetWidth={400} color="rgba(255,255,255,0.7)" />
  </Sequence>
  <Sequence from={60}>
    <SubtitleText text="Part 3" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": "The Mold Has Three Parts",
  "subtitle": "Part 3",
  "accentLineWidth": 400,
  "backgroundColor": "#0F172A",
  "titleColor": "#FFFFFF",
  "subtitleColor": "#94A3B8",
  "moldIcon": {
    "width": 200,
    "height": 80,
    "strokeColor": "rgba(255,255,255,0.5)",
    "regions": [
      { "id": "walls", "color": "#D9944A", "label": "Tests" },
      { "id": "nozzle", "color": "#4A90D9", "label": "Prompt" },
      { "id": "material", "color": "#5AAA6E", "label": "Grounding" }
    ]
  }
}
```

---
