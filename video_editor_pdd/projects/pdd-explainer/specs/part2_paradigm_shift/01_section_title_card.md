[title:]

# Section 2.1: The Paradigm Shift — Title Card

**Tool:** Remotion
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 8:30 - 8:34

## Visual Description
A section title card introducing Part 2. The heading "The Paradigm Shift" fades in at center with a subtle upward drift. Below the title, an animated icon pair appears: a small handcrafted object (simple wireframe chair) on the left morphs into a geometric mold cavity on the right, connected by a sweeping arrow — representing the shift from crafting to specification. The subtitle "Part 2" drifts upward below an expanding accent line. Dark navy background consistent with the series palette.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Title Text:** "The Paradigm Shift" — white `#FFFFFF`, centered at Y=370px
- **Shift Icon:** Centered at Y=460px, 300px wide x 60px tall
  - Left: Wireframe chair outline (4 strokes), `#4A90D9` at 0.5 opacity, 2px stroke
  - Arrow: Curved sweep from left to right, `rgba(255,255,255,0.4)`, 1.5px, with small arrowhead
  - Right: Rectangular mold cavity outline, `#D9944A` at 0.5 opacity, 2px stroke
- **Accent Line:** Thin horizontal rule — `rgba(255,255,255,0.7)`, centered at Y=520px, 400px wide x 2px tall
- **Subtitle Text:** "Part 2" — muted slate `#94A3B8`, centered at Y=560px

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Title text fades in (opacity 0→1) and scales up (0.85→1.0) from center with 8px upward drift
2. **Frame 20-55 (0.67-1.83s):** Shift icon draws in — wireframe chair strokes first, then arrow sweeps left-to-right, then mold cavity draws
3. **Frame 45-65 (1.5-2.17s):** Accent line expands from 0px to 400px width
4. **Frame 55-80 (1.83-2.67s):** Subtitle "Part 2" fades in with 12px upward drift
5. **Frame 80-120 (2.67-4.0s):** Hold at final state

### Typography
- Title: Inter, 64px, bold (700), `#FFFFFF`
- Subtitle: Inter, 28px, regular (400), `#94A3B8`

### Easing
- Title fade/scale: `easeOut(quad)`
- Chair wireframe draw: `easeOut(cubic)`
- Arrow sweep: `easeInOut(cubic)`
- Mold cavity draw: `easeOut(cubic)`
- Accent line expand: `easeOut(cubic)`
- Subtitle fade/drift: `easeOut(quad)`

## Narration Sync
> "So let me put together what I just showed you."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <TitleText text="The Paradigm Shift" fontSize={64} />
  <Sequence from={20}>
    <ShiftIcon width={300} height={60} y={460}>
      <WireframeChair color="#4A90D9" side="left" />
      <SweepArrow color="rgba(255,255,255,0.4)" />
      <MoldCavity color="#D9944A" side="right" />
    </ShiftIcon>
  </Sequence>
  <Sequence from={45}>
    <AccentLine targetWidth={400} color="rgba(255,255,255,0.7)" />
  </Sequence>
  <Sequence from={55}>
    <SubtitleText text="Part 2" />
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
  "icon": {
    "width": 300,
    "height": 60,
    "leftColor": "#4A90D9",
    "rightColor": "#D9944A",
    "arrowColor": "rgba(255,255,255,0.4)"
  }
}
```

---
