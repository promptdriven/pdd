[title:]

# Section 4.1: The Precision Tradeoff — Title Card

**Tool:** Remotion
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 18:30 - 18:34

## Visual Description
A section title card introducing Part 4. The heading "The Precision Tradeoff" fades in at center. Below the title, a stylized icon animates: a horizontal line with a precise, angular mold shape on the left and a loose, freeform squiggle on the right — representing the tension between specification precision and constraint-driven shaping. The subtitle "Part 4" drifts upward below an accent line. Dark navy background consistent with the series.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Title Text:** "The Precision Tradeoff" — white `#FFFFFF`, centered at Y=370px
- **Precision Icon:** Centered at Y=460px, 260px wide x 60px tall
  - Left side: Angular geometric shape (precise grid points connected by straight lines), stroke `#4A90D9` at 0.5 opacity, 2px
  - Right side: Smooth organic curve (flowing liquid constrained by two wall lines), stroke `#D9944A` at 0.5 opacity, 2px
  - Divider: Thin vertical mark at center, `rgba(255,255,255,0.3)`, 1px
- **Accent Line:** Thin horizontal rule — `rgba(255,255,255,0.7)`, centered at Y=520px, 400px wide x 2px tall
- **Subtitle Text:** "Part 4" — muted slate `#94A3B8`, centered at Y=560px

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Title text fades in (opacity 0→1) and scales up (0.85→1.0) from center
2. **Frame 20-50 (0.67-1.67s):** Precision icon draws in — left angular grid strokes first, then right flowing curve, meeting at the center divider
3. **Frame 40-65 (1.33-2.17s):** Accent line expands from 0px to 400px width
4. **Frame 55-80 (1.83-2.67s):** Subtitle "Part 4" fades in with 12px upward drift
5. **Frame 80-120 (2.67-4.0s):** Hold at final state

### Typography
- Title: Inter, 64px, bold (700), `#FFFFFF`
- Subtitle: Inter, 28px, regular (400), `#94A3B8`

### Easing
- Title fade/scale: `easeOut(quad)`
- Icon draw (left angular): `easeOut(cubic)`
- Icon draw (right curve): `easeInOut(cubic)`
- Accent line expand: `easeOut(cubic)`
- Subtitle fade/drift: `easeOut(quad)`

## Narration Sync
> "Let's talk about precision. Because there's a subtle tradeoff that changes how you think about prompts."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <TitleText text="The Precision Tradeoff" fontSize={64} />
  <Sequence from={20}>
    <PrecisionIcon width={260} height={60} y={460}>
      <AngularGrid color="#4A90D9" side="left" />
      <FlowingCurve color="#D9944A" side="right" />
    </PrecisionIcon>
  </Sequence>
  <Sequence from={40}>
    <AccentLine targetWidth={400} color="rgba(255,255,255,0.7)" />
  </Sequence>
  <Sequence from={55}>
    <SubtitleText text="Part 4" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": "The Precision Tradeoff",
  "subtitle": "Part 4",
  "accentLineWidth": 400,
  "backgroundColor": "#0F172A",
  "titleColor": "#FFFFFF",
  "subtitleColor": "#94A3B8",
  "icon": {
    "width": 260,
    "height": 60,
    "leftColor": "#4A90D9",
    "rightColor": "#D9944A",
    "dividerColor": "rgba(255,255,255,0.3)"
  }
}
```

---
