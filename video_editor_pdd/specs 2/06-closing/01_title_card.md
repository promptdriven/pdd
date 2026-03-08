[title:Part 6 — The Future of Code]

# Section 6.0: Title Card — "The Future of Code"

**Tool:** Remotion
**Duration:** ~4s
**Timestamp:** 0:00 - 0:04

## Visual Description
A cinematic closing title card that emerges from darkness. "Part 6" appears as a small eyebrow label in vibrant blue, followed by the main title "The Future of Code" which scales up with conviction. A thin horizontal rule animates outward from center beneath the title in amber (#F59E0B) — signaling a shift from analysis to action. The background is deep navy with a warm amber-blue dual-tone radial glow, evoking resolution and forward momentum. The card cross-dissolves quickly into the Veo economics flip background, establishing the closing argument.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: solid #0F172A (dark navy) with dual radial glow
- Radial glow 1: #1E3A5F → transparent, radius 700px, centered at (960, 400)
- Radial glow 2: #3D2E0A → transparent, radius 500px, centered at (960, 550)

### Chart/Visual Elements
- Eyebrow label: "PART 6" centered at (960, 370)
- Title text: "The Future of Code" centered at (960, 470)
- Horizontal rule: 2px line, centered, expanding from 0px to 400px width at y=530
- Dual radial glow: warm amber-blue ambient blend behind text cluster

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Fade in from black — background opacity 0→1.
2. **Frame 10-28 (0.33-0.93s):** Eyebrow "PART 6" fades in — opacity 0→1, translateY 18→0.
3. **Frame 20-42 (0.67-1.4s):** Main title fades in — opacity 0→1, scale 0.88→1.0.
4. **Frame 35-52 (1.17-1.73s):** Horizontal rule expands from center — width 0→400px.
5. **Frame 52-90 (1.73-3s):** Hold at full opacity.
6. **Frame 90-120 (3-4s):** Entire card cross-dissolves — opacity 1→0.

### Typography
- Eyebrow: Inter Medium, 24px, #3B82F6 (vibrant blue), letter-spacing 0.2em, uppercase
- Title: Inter Bold, 64px, #FFFFFF, letter-spacing -0.02em
- Text shadow: 0 4px 24px rgba(245, 158, 11, 0.3)
- Horizontal rule: #F59E0B at 70% opacity

### Easing
- Eyebrow fade/slide: `easeOutCubic`
- Title scale: `easeOutQuart`
- Rule expansion: `easeInOutCubic`
- Card fade out: `easeInCubic`

## Narration Sync
> "The economics have flipped."

Title card appears at the very start of the closing section and cross-dissolves as the narration launches into the closing argument about economics flipping.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  {/* Background with dual radial glow */}
  <AbsoluteFill style={{
    backgroundColor: '#0F172A',
    opacity: interpolate(frame, [0, 15, 90, 120], [0, 1, 1, 0]),
  }}>
    <RadialGlow center={[960, 400]} radius={700} color="#1E3A5F" opacity={0.5} />
    <RadialGlow center={[960, 550]} radius={500} color="#3D2E0A" opacity={0.4} />
  </AbsoluteFill>

  {/* Eyebrow label */}
  <Text style={{
    opacity: interpolate(frame, [10, 28, 90, 120], [0, 1, 1, 0], { extrapolateLeft: 'clamp' }),
    transform: `translateY(${interpolate(frame, [10, 28], [18, 0], { extrapolateRight: 'clamp' })}px)`,
    color: '#3B82F6',
    fontSize: 24,
    letterSpacing: '0.2em',
    textTransform: 'uppercase',
  }}>
    PART 6
  </Text>

  {/* Main title */}
  <Text style={{
    opacity: interpolate(frame, [20, 42, 90, 120], [0, 1, 1, 0], { extrapolateLeft: 'clamp' }),
    transform: `scale(${interpolate(frame, [20, 42], [0.88, 1.0], { extrapolateRight: 'clamp' })})`,
    color: '#FFFFFF',
    fontSize: 64,
    fontWeight: 'bold',
  }}>
    The Future of Code
  </Text>

  {/* Horizontal rule */}
  <HorizontalRule
    width={interpolate(frame, [35, 52, 90, 120], [0, 400, 400, 0], { extrapolateLeft: 'clamp' })}
    color="#F59E0B"
    opacity={0.7}
  />
</Sequence>
```

## Data Points
```json
{
  "eyebrow": "PART 6",
  "title": "The Future of Code",
  "accentColor": "#F59E0B",
  "glowColors": ["#1E3A5F", "#3D2E0A"],
  "eyebrowColor": "#3B82F6",
  "fadeInFrames": 42,
  "holdFrames": 48,
  "fadeOutFrames": 30,
  "totalFrames": 120,
  "fps": 30
}
```

---
