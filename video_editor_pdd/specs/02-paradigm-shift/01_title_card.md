[title:Part 2 — The Paradigm Shift]

# Section 2.0: Title Card — "The Paradigm Shift"

**Tool:** Remotion
**Duration:** ~5s
**Timestamp:** 0:00 - 0:05

## Visual Description
A bold section title card that fades in from black. "Part 2" appears first as a small eyebrow label in molten orange, followed by the main title "The Paradigm Shift" scaling up into position with a subtle rotational entrance. A thin horizontal rule animates outward from center beneath the title, transitioning from orange to blue as it expands. The card sits on a deep navy background with a warm radial glow behind the text — more amber-toned than Part 1's blue, signaling a shift in narrative energy. After holding for 3 seconds, the entire card fades out to reveal the injection molding Veo footage underneath.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: solid #0F172A (dark navy) with radial glow at center
- Radial glow: #3D1F00 → transparent, radius 900px, centered at (960, 480)

### Chart/Visual Elements
- Eyebrow label: "PART 2" centered at (960, 360)
- Title text: "The Paradigm Shift" centered at (960, 460)
- Horizontal rule: 2px line, centered, expanding from 0px to 480px width at y=520
- Rule gradient: #F97316 (left edge) → #3B82F6 (right edge)
- Radial glow: warm ambient background glow behind text cluster

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Fade in from black — background opacity 0→1.
2. **Frame 15-35 (0.5-1.17s):** Eyebrow "PART 2" fades in — opacity 0→1, translateY 20→0.
3. **Frame 25-50 (0.83-1.67s):** Main title fades in — opacity 0→1, scale 0.92→1.0, rotateX 3°→0°.
4. **Frame 40-60 (1.33-2s):** Horizontal rule expands from center — width 0→480px.
5. **Frame 60-120 (2-4s):** Hold at full opacity.
6. **Frame 120-150 (4-5s):** Entire card fades out — opacity 1→0.

### Typography
- Eyebrow: Inter Medium, 24px, #F97316 (molten orange), letter-spacing 0.2em, uppercase
- Title: Inter Bold, 68px, #FFFFFF, letter-spacing -0.02em
- Text shadow: 0 4px 24px rgba(249, 115, 22, 0.3)
- Horizontal rule: gradient #F97316 → #3B82F6 at 70% opacity

### Easing
- Eyebrow fade/slide: `easeOutCubic`
- Title scale + rotation: `easeOutQuart`
- Rule expansion: `easeInOutCubic`
- Card fade out: `easeInCubic`

## Narration Sync
> "Not cheaper materials — a shift in how things are made."

Title appears at the start of Part 2 and fades out before the narration transitions into the industry pattern discussion.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  {/* Background with warm radial glow */}
  <AbsoluteFill style={{
    backgroundColor: '#0F172A',
    opacity: interpolate(frame, [0, 20, 120, 150], [0, 1, 1, 0]),
  }}>
    <RadialGlow center={[960, 480]} radius={900} color="#3D1F00" opacity={0.6} />
  </AbsoluteFill>

  {/* Eyebrow label */}
  <Text style={{
    fontFamily: 'Inter', fontWeight: 500, fontSize: 24,
    color: '#F97316', letterSpacing: '0.2em', textTransform: 'uppercase',
    opacity: interpolate(frame, [15, 35, 120, 150], [0, 1, 1, 0], { extrapolateLeft: 'clamp' }),
    transform: `translateY(${interpolate(frame, [15, 35], [20, 0], { extrapolateRight: 'clamp' })}px)`,
  }}>
    PART 2
  </Text>

  {/* Main title */}
  <Text style={{
    fontFamily: 'Inter', fontWeight: 700, fontSize: 68,
    color: '#FFFFFF', letterSpacing: '-0.02em',
    opacity: interpolate(frame, [25, 50, 120, 150], [0, 1, 1, 0], { extrapolateLeft: 'clamp' }),
    transform: `scale(${interpolate(frame, [25, 50], [0.92, 1.0], { extrapolateRight: 'clamp' })}) rotateX(${interpolate(frame, [25, 50], [3, 0], { extrapolateRight: 'clamp' })}deg)`,
  }}>
    The Paradigm Shift
  </Text>

  {/* Horizontal rule with gradient */}
  <HorizontalRule
    width={interpolate(frame, [40, 60, 120, 150], [0, 480, 480, 0], { extrapolateLeft: 'clamp' })}
    gradient={['#F97316', '#3B82F6']}
    opacity={0.7}
  />
</Sequence>
```

## Data Points
```json
{
  "eyebrow": "PART 2",
  "title": "The Paradigm Shift",
  "fadeInFrames": 50,
  "holdFrames": 70,
  "fadeOutFrames": 30,
  "totalFrames": 150,
  "fps": 30,
  "glowColor": "#3D1F00",
  "accentColor": "#F97316"
}
```

---
