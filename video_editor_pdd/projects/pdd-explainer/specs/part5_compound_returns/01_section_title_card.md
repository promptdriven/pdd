[title:]

# Section 5.1: Compound Returns — Title Card

**Tool:** Remotion
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 21:00 - 21:04

## Visual Description
A section title card introducing Part 5. The heading "Compound Returns" fades in at center. Below the title, a stylized icon animates: two curves diverge from a shared origin — one curving exponentially upward (amber, representing compounding debt/cost) and one staying flat then gently declining (blue, representing PDD's compounding value). A small dollar sign marks the end of the upper curve; a small checkmark marks the end of the lower curve. The subtitle "Part 5" drifts upward below an accent line. Dark navy background consistent with the series.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Title Text:** "Compound Returns" — white `#FFFFFF`, centered at Y=370px
- **Divergence Icon:** Centered at Y=460px, 280px wide x 70px tall
  - Shared origin dot at left-center: `#FFFFFF` at 0.6 opacity, 4px radius
  - Upper curve: Exponential upward arc, stroke `#D9944A` at 0.5 opacity, 2px (debt/cost)
  - Lower curve: Flat then gentle decline, stroke `#4A90D9` at 0.5 opacity, 2px (PDD cost)
  - Small dollar sign at end of upper curve: `#D9944A` at 0.3 opacity, 12px
  - Small checkmark at end of lower curve: `#4A90D9` at 0.3 opacity, 12px
- **Accent Line:** Thin horizontal rule — `rgba(255,255,255,0.7)`, centered at Y=550px, 400px wide x 2px tall
- **Subtitle Text:** "Part 5" — muted slate `#94A3B8`, centered at Y=590px

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Title text fades in (opacity 0→1) and scales up (0.85→1.0) from center
2. **Frame 20-55 (0.67-1.83s):** Divergence icon draws in — origin dot appears, then both curves draw outward simultaneously from the shared origin, diverging. Dollar sign and checkmark fade in at endpoints
3. **Frame 45-70 (1.50-2.33s):** Accent line expands from 0px to 400px width
4. **Frame 60-85 (2.0-2.83s):** Subtitle "Part 5" fades in with 12px upward drift
5. **Frame 85-120 (2.83-4.0s):** Hold at final state

### Typography
- Title: Inter, 64px, bold (700), `#FFFFFF`
- Subtitle: Inter, 28px, regular (400), `#94A3B8`

### Easing
- Title fade/scale: `easeOut(quad)`
- Origin dot appear: `easeOut(cubic)`
- Curve draws: `easeInOut(cubic)`
- Accent line expand: `easeOut(cubic)`
- Subtitle fade/drift: `easeOut(quad)`

## Narration Sync
> "Now let's zoom out. Because the numbers you just saw — individual patches, individual bugs — add up to something staggering."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <TitleText text="Compound Returns" fontSize={64} />
  <Sequence from={20}>
    <DivergenceIcon width={280} height={70} y={460}>
      <OriginDot color="#FFFFFF" opacity={0.6} radius={4} />
      <ExponentialCurve color="#D9944A" opacity={0.5} direction="up" />
      <FlatCurve color="#4A90D9" opacity={0.5} direction="flat" />
    </DivergenceIcon>
  </Sequence>
  <Sequence from={45}>
    <AccentLine targetWidth={400} color="rgba(255,255,255,0.7)" />
  </Sequence>
  <Sequence from={60}>
    <SubtitleText text="Part 5" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": "Compound Returns",
  "subtitle": "Part 5",
  "accentLineWidth": 400,
  "backgroundColor": "#0F172A",
  "titleColor": "#FFFFFF",
  "subtitleColor": "#94A3B8",
  "icon": {
    "width": 280,
    "height": 70,
    "upperCurveColor": "#D9944A",
    "lowerCurveColor": "#4A90D9",
    "originDotColor": "#FFFFFF",
    "originDotOpacity": 0.6
  }
}
```

---
