[title:Part 1 — The Economics of Code Generation]

# Section 1.0: Title Card — "The Economics of Code Generation"

**Tool:** Remotion
**Duration:** ~5s
**Timestamp:** 0:00 - 0:05

## Visual Description
A bold section title card that fades in from black. "Part 1" appears first as a small eyebrow label, followed by the main title "The Economics of Code Generation" scaling up into position. A thin horizontal rule animates outward from center beneath the title. The card sits on a deep navy background with a subtle radial glow behind the text. After holding for 3 seconds, the entire card fades out to reveal the Veo cost graph background underneath.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: solid #0F172A (dark navy) with radial glow at center
- Radial glow: #1E3A5F → transparent, radius 800px, centered at (960, 480)

### Chart/Visual Elements
- Eyebrow label: "PART 1" centered at (960, 360)
- Title text: "The Economics of Code Generation" centered at (960, 460)
- Horizontal rule: 2px line, centered, expanding from 0px to 400px width at y=520
- Radial glow: soft ambient background glow behind text cluster

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Fade in from black — background opacity 0→1.
2. **Frame 15-35 (0.5-1.17s):** Eyebrow "PART 1" fades in — opacity 0→1, translateY 20→0.
3. **Frame 25-50 (0.83-1.67s):** Main title fades in — opacity 0→1, scale 0.9→1.0.
4. **Frame 40-60 (1.33-2s):** Horizontal rule expands from center — width 0→400px.
5. **Frame 60-120 (2-4s):** Hold at full opacity.
6. **Frame 120-150 (4-5s):** Entire card fades out — opacity 1→0.

### Typography
- Eyebrow: Inter Medium, 24px, #3B82F6 (vibrant blue), letter-spacing 0.2em, uppercase
- Title: Inter Bold, 64px, #FFFFFF, letter-spacing -0.02em
- Text shadow: 0 4px 24px rgba(59, 130, 246, 0.3)
- Horizontal rule: #3B82F6 at 60% opacity

### Easing
- Eyebrow fade/slide: `easeOutCubic`
- Title scale: `easeOutQuart`
- Rule expansion: `easeInOutCubic`
- Card fade out: `easeInCubic`

## Narration Sync
> "If you use Cursor, Claude Code, or Copilot — you're getting really good at this."

Title appears at the start of Part 1 and fades out before the narration transitions into the economics metaphor.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  {/* Background with radial glow */}
  <AbsoluteFill style={{
    backgroundColor: '#0F172A',
    opacity: interpolate(frame, [0, 20, 120, 150], [0, 1, 1, 0]),
  }}>
    <RadialGlow center={[960, 480]} radius={800} color="#1E3A5F" opacity={0.6} />
  </AbsoluteFill>

  {/* Eyebrow label */}
  <Text style={{
    opacity: interpolate(frame, [15, 35, 120, 150], [0, 1, 1, 0], { extrapolateLeft: 'clamp' }),
    transform: `translateY(${interpolate(frame, [15, 35], [20, 0], { extrapolateRight: 'clamp' })}px)`,
  }}>
    PART 1
  </Text>

  {/* Main title */}
  <Text style={{
    opacity: interpolate(frame, [25, 50, 120, 150], [0, 1, 1, 0], { extrapolateLeft: 'clamp' }),
    transform: `scale(${interpolate(frame, [25, 50], [0.9, 1.0], { extrapolateRight: 'clamp' })})`,
  }}>
    The Economics of Code Generation
  </Text>

  {/* Horizontal rule */}
  <HorizontalRule
    width={interpolate(frame, [40, 60, 120, 150], [0, 400, 400, 0], { extrapolateLeft: 'clamp' })}
    color="#3B82F6"
    opacity={0.6}
  />
</Sequence>
```

## Data Points
```json
{
  "eyebrow": "PART 1",
  "title": "The Economics of Code Generation",
  "fadeInFrames": 50,
  "holdFrames": 70,
  "fadeOutFrames": 30,
  "totalFrames": 150,
  "fps": 30
}
```

---
