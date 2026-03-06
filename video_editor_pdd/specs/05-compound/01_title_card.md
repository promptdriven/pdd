[title:Part 5 — Compound Returns]

# Section 5.0: Title Card — "Compound Returns"

**Tool:** Remotion
**Duration:** ~5s
**Timestamp:** 0:00 - 0:05

## Visual Description
A bold section title card that fades in from black. "Part 5" appears first as a small eyebrow label in vibrant blue, followed by the main title "Compound Returns" scaling up into position. A thin horizontal rule animates outward from center beneath the title in test green. The card sits on a deep navy background with a cool blue-green radial glow behind the text — evoking exponential growth and compounding momentum. After holding for 3 seconds, the entire card cross-dissolves into the Veo maintenance pie chart background.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: solid #0F172A (dark navy) with radial glow at center
- Radial glow: #0A2A1A → transparent, radius 800px, centered at (960, 480)

### Chart/Visual Elements
- Eyebrow label: "PART 5" centered at (960, 360)
- Title text: "Compound Returns" centered at (960, 460)
- Horizontal rule: 2px line, centered, expanding from 0px to 360px width at y=520
- Radial glow: cool blue-green ambient background glow behind text cluster

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Fade in from black — background opacity 0→1.
2. **Frame 15-35 (0.5-1.17s):** Eyebrow "PART 5" fades in — opacity 0→1, translateY 20→0.
3. **Frame 25-50 (0.83-1.67s):** Main title fades in — opacity 0→1, scale 0.9→1.0.
4. **Frame 40-60 (1.33-2s):** Horizontal rule expands from center — width 0→360px.
5. **Frame 60-120 (2-4s):** Hold at full opacity.
6. **Frame 120-150 (4-5s):** Entire card cross-dissolves — opacity 1→0.

### Typography
- Eyebrow: Inter Medium, 24px, #3B82F6 (vibrant blue), letter-spacing 0.2em, uppercase
- Title: Inter Bold, 64px, #FFFFFF, letter-spacing -0.02em
- Text shadow: 0 4px 24px rgba(34, 197, 94, 0.3)
- Horizontal rule: #22C55E at 60% opacity

### Easing
- Eyebrow fade/slide: `easeOutCubic`
- Title scale: `easeOutQuart`
- Rule expansion: `easeInOutCubic`
- Card fade out: `easeInCubic`

## Narration Sync
> "Eighty to ninety percent of software cost is maintenance."

Title card appears at the start of Part 5 and cross-dissolves as the narration transitions into the maintenance burden framing.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  {/* Background with green radial glow */}
  <AbsoluteFill style={{
    backgroundColor: '#0F172A',
    opacity: interpolate(frame, [0, 20, 120, 150], [0, 1, 1, 0]),
  }}>
    <RadialGlow center={[960, 480]} radius={800} color="#0A2A1A" opacity={0.6} />
  </AbsoluteFill>

  {/* Eyebrow label */}
  <Text style={{
    opacity: interpolate(frame, [15, 35, 120, 150], [0, 1, 1, 0], { extrapolateLeft: 'clamp' }),
    transform: `translateY(${interpolate(frame, [15, 35], [20, 0], { extrapolateRight: 'clamp' })}px)`,
    color: '#3B82F6',
    fontSize: 24,
    letterSpacing: '0.2em',
    textTransform: 'uppercase',
  }}>
    PART 5
  </Text>

  {/* Main title */}
  <Text style={{
    opacity: interpolate(frame, [25, 50, 120, 150], [0, 1, 1, 0], { extrapolateLeft: 'clamp' }),
    transform: `scale(${interpolate(frame, [25, 50], [0.9, 1.0], { extrapolateRight: 'clamp' })})`,
    color: '#FFFFFF',
    fontSize: 64,
    fontWeight: 'bold',
  }}>
    Compound Returns
  </Text>

  {/* Horizontal rule */}
  <HorizontalRule
    width={interpolate(frame, [40, 60, 120, 150], [0, 360, 360, 0], { extrapolateLeft: 'clamp' })}
    color="#22C55E"
    opacity={0.6}
  />
</Sequence>
```

## Data Points
```json
{
  "eyebrow": "PART 5",
  "title": "Compound Returns",
  "accentColor": "#22C55E",
  "glowColor": "#0A2A1A",
  "eyebrowColor": "#3B82F6",
  "fadeInFrames": 50,
  "holdFrames": 70,
  "fadeOutFrames": 30,
  "totalFrames": 150,
  "fps": 30
}
```

---
