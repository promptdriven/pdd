[title:Part 3 — The Mold Has Three Parts]

# Section 3.0: Title Card — "The Mold Has Three Parts"

**Tool:** Remotion
**Duration:** ~5s
**Timestamp:** 0:00 - 0:05

## Visual Description
A bold section title card fades in over the Veo test-walls background. "Part 3" appears as a small eyebrow label, followed by the main title "The Mold Has Three Parts" scaling up into position. Beneath the title, a tricolor accent bar animates outward from center — three segments in test green, prompt gold, and grounding purple, visually previewing the three components of the mold. After holding for 3 seconds, the title fades out to reveal the Veo background underneath.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: semi-transparent overlay on Veo background — rgba(15, 23, 42, 0.7)
- Radial glow: subtle tricolor glow at center (green/gold/purple blend), radius 600px

### Chart/Visual Elements
- Eyebrow label: "PART 3" centered at (960, 350)
- Title text: "The Mold Has Three Parts" centered at (960, 450)
- Tricolor accent bar: three adjacent segments at y=520, expanding from center
  - Left segment: #22C55E (test green), 133px wide
  - Center segment: #F59E0B (prompt gold), 134px wide
  - Right segment: #A855F7 (grounding purple), 133px wide
  - Total width: 400px, height: 3px
- Background scrim: full-frame semi-transparent dark overlay

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Scrim fades in — opacity 0→0.7.
2. **Frame 15-35 (0.5-1.17s):** Eyebrow "PART 3" fades in — opacity 0→1, translateY 20→0.
3. **Frame 25-50 (0.83-1.67s):** Main title fades in — opacity 0→1, scale 0.9→1.0.
4. **Frame 40-65 (1.33-2.17s):** Tricolor bar expands from center — width 0→400px, each segment animates sequentially (green first, gold second, purple third, 5-frame stagger).
5. **Frame 65-120 (2.17-4s):** Hold at full opacity.
6. **Frame 120-150 (4-5s):** Entire card fades out — opacity 1→0.

### Typography
- Eyebrow: Inter Medium, 24px, #A855F7 (grounding purple), letter-spacing 0.2em, uppercase
- Title: Inter Bold, 64px, #FFFFFF, letter-spacing -0.02em
- Text shadow: 0 4px 24px rgba(168, 85, 247, 0.3)

### Easing
- Eyebrow fade/slide: `easeOutCubic`
- Title scale: `easeOutQuart`
- Bar expansion: `easeInOutCubic`
- Card fade out: `easeInCubic`

## Narration Sync
> "Each one is a different type of capital."

Title card appears at the start of Part 3 and fades out as the narration transitions into describing test capital.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  {/* Background scrim */}
  <AbsoluteFill style={{
    backgroundColor: `rgba(15, 23, 42, ${interpolate(frame, [0, 20, 120, 150], [0, 0.7, 0.7, 0])})`,
  }}>
    <TricolorGlow center={[960, 450]} radius={600} opacity={0.4} />
  </AbsoluteFill>

  {/* Eyebrow label */}
  <Text style={{
    opacity: interpolate(frame, [15, 35, 120, 150], [0, 1, 1, 0]),
    transform: `translateY(${interpolate(frame, [15, 35], [20, 0], { extrapolateRight: 'clamp' })}px)`,
    color: '#A855F7',
  }}>
    PART 3
  </Text>

  {/* Main title */}
  <Text style={{
    opacity: interpolate(frame, [25, 50, 120, 150], [0, 1, 1, 0]),
    transform: `scale(${interpolate(frame, [25, 50], [0.9, 1.0], { extrapolateRight: 'clamp' })})`,
  }}>
    The Mold Has Three Parts
  </Text>

  {/* Tricolor accent bar */}
  <TricolorBar
    segments={[
      { color: '#22C55E', startFrame: 40 },
      { color: '#F59E0B', startFrame: 45 },
      { color: '#A855F7', startFrame: 50 },
    ]}
    totalWidth={interpolate(frame, [40, 65, 120, 150], [0, 400, 400, 0])}
    y={520}
  />
</Sequence>
```

## Data Points
```json
{
  "title": "The Mold Has Three Parts",
  "eyebrow": "PART 3",
  "accent_colors": ["#22C55E", "#F59E0B", "#A855F7"],
  "accent_labels": ["Tests", "Prompt", "Grounding"],
  "totalFrames": 150,
  "fps": 30
}
```

---
