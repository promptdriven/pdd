[title:]

# Section 6.1: Where to Start — Title Card

**Tool:** Remotion
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 22:20 - 22:24

## Visual Description
A section title card introducing the practical coda. The heading "Where to Start" fades in at center with a subtle upward drift. Below the title, an animated icon: a single module block (rounded rectangle) with a small play-button triangle inside, suggesting "begin here." The block pulses once with a gentle glow. The subtitle "Part 6" drifts upward below an expanding accent line. Dark navy background consistent with the series palette. This card signals the shift from theory to action.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Title Text:** "Where to Start" — white `#FFFFFF`, centered at Y=370px
- **Module Icon:** Centered at Y=460px, 80px wide x 50px tall
  - Rounded rectangle outline: `#4A90D9` at 0.5 opacity, 2px stroke, 6px border-radius
  - Play triangle inside: `#5AAA6E` at 0.5 opacity, 16px wide, centered within the rectangle
  - Glow pulse: `rgba(74,144,217,0.15)` expanding ring, peaks at 120px radius then fades
- **Accent Line:** Thin horizontal rule — `rgba(255,255,255,0.7)`, centered at Y=530px, 400px wide x 2px tall
- **Subtitle Text:** "Part 6" — muted slate `#94A3B8`, centered at Y=570px

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Title text fades in (opacity 0→1) and scales up (0.85→1.0) from center with 8px upward drift
2. **Frame 20-50 (0.67-1.67s):** Module icon draws in — rectangle outline first, then play triangle fades in inside it
3. **Frame 50-75 (1.67-2.5s):** Glow pulse expands from module icon (0→120px radius) then fades (opacity 0.15→0). Accent line expands from 0px to 400px width simultaneously
4. **Frame 65-85 (2.17-2.83s):** Subtitle "Part 6" fades in with 12px upward drift
5. **Frame 85-120 (2.83-4.0s):** Hold at final state

### Typography
- Title: Inter, 64px, bold (700), `#FFFFFF`
- Subtitle: Inter, 28px, regular (400), `#94A3B8`

### Easing
- Title fade/scale: `easeOut(quad)`
- Rectangle draw: `easeOut(cubic)`
- Play triangle fade: `easeOut(quad)`
- Glow pulse: `easeOut(cubic)`
- Accent line expand: `easeOut(cubic)`
- Subtitle fade/drift: `easeOut(quad)`

## Narration Sync
> "PDD can create prompts from existing code."

Segment: `where_to_start_001` (0.0s – ~2.72s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <TitleText text="Where to Start" fontSize={64} />
  <Sequence from={20}>
    <ModuleIcon width={80} height={50} y={460}>
      <RoundedRect color="#4A90D9" opacity={0.5} radius={6} />
      <PlayTriangle color="#5AAA6E" opacity={0.5} size={16} />
    </ModuleIcon>
  </Sequence>
  <Sequence from={50}>
    <GlowPulse color="rgba(74,144,217,0.15)" maxRadius={120} />
    <AccentLine targetWidth={400} color="rgba(255,255,255,0.7)" />
  </Sequence>
  <Sequence from={65}>
    <SubtitleText text="Part 6" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": "Where to Start",
  "subtitle": "Part 6",
  "accentLineWidth": 400,
  "backgroundColor": "#0F172A",
  "titleColor": "#FFFFFF",
  "subtitleColor": "#94A3B8",
  "icon": {
    "width": 80,
    "height": 50,
    "rectColor": "#4A90D9",
    "playColor": "#5AAA6E",
    "glowColor": "rgba(74,144,217,0.15)",
    "glowMaxRadius": 120
  }
}
```

---
