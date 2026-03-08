[Remotion] CodeRabbit Stat Callout — AI Code 1.7x More Issues

# Section 3.2: Stat Callout — CodeRabbit AI Code Quality Study

**Tool:** Remotion
**Duration:** ~10s
**Timestamp:** 0:25 - 0:35

## Visual Description
A data callout card that slides in from the right side of the frame. The card features the headline stat "1.7x" in large bold text with a subheading "more issues in AI-generated code" and a source attribution "CodeRabbit, 2024". Below the main stat, two qualifying details appear sequentially: "75% logic errors" in red and "8x perf problems" in amber. The card has a frosted glass background with a red left-edge accent bar, signaling a warning/problem stat. After holding for 6 seconds, it slides back out to the right.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay
- Card position: right-aligned, vertically centered — card at (1060, 300) to (1860, 720)
- Card size: 800px x 420px

### Chart/Visual Elements
- Card background: rgba(15, 23, 42, 0.88) with backdrop-filter blur(12px) — frosted glass
- Card border: 1px solid rgba(239, 68, 68, 0.3)
- Card border-radius: 16px
- Left accent bar: 4px x full height, #EF4444 (red)
- Stat number: "1.7x" — large, positioned at top-left of card content
- Stat descriptor: "more issues in AI-generated code" — below stat number
- Detail row 1: "75% logic errors" — red text with error icon
- Detail row 2: "8x perf problems" — amber text with warning icon
- Source: "CodeRabbit, 2024" — small text, bottom of card
- Subtle glow: box-shadow 0 8px 32px rgba(239, 68, 68, 0.15)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Card slides in from right — translateX(200)→translateX(0), opacity 0→1.
2. **Frame 15-35 (0.5-1.17s):** Stat "1.7x" animates — scale 0.8→1.0, opacity 0→1.
3. **Frame 30-45 (1-1.5s):** Descriptor text fades in — opacity 0→1.
4. **Frame 40-60 (1.33-2s):** Detail "75% logic errors" slides in from left within card — translateX(-20)→0, opacity 0→1.
5. **Frame 55-75 (1.83-2.5s):** Detail "8x perf problems" slides in — same animation, staggered.
6. **Frame 70-85 (2.33-2.83s):** Source attribution fades in — opacity 0→0.7.
7. **Frame 85-250 (2.83-8.33s):** Hold. Card fully visible.
8. **Frame 250-300 (8.33-10s):** Card slides out to right — translateX(0)→translateX(200), opacity 1→0.

### Typography
- Stat number: Inter Black, 88px, #FFFFFF
- Stat descriptor: Inter Medium, 26px, #CBD5E1
- Detail row 1: Inter SemiBold, 22px, #EF4444 (red)
- Detail row 2: Inter SemiBold, 22px, #F59E0B (amber)
- Icons: 18px inline, matching text color
- Source: Inter Regular, 16px, #64748B (muted)

### Easing
- Card slide in: `spring({ damping: 15, stiffness: 180 })`
- Stat scale: `easeOutCubic`
- Detail slides: `easeOutQuad`
- Text fades: `easeOutQuad`
- Card slide out: `easeInCubic`

## Narration Sync
> "CodeRabbit analyzed thousands of pull requests and found AI-generated code has 1.7 times more issues — 75 percent are logic errors, with 8 times as many performance problems."

The "1.7x" stat animates in as "1.7 times more issues" is spoken. "75% logic errors" appears on "75 percent are logic errors." "8x perf problems" appears on "8 times as many performance problems."

## Code Structure (Remotion)
```typescript
<Sequence from={CODERABBIT_STAT_START} durationInFrames={300}>
  <StatCalloutCard
    style={{
      transform: `translateX(${interpolate(frame, [0, 20, 250, 300], [200, 0, 0, 200])}px)`,
      opacity: interpolate(frame, [0, 20, 250, 300], [0, 1, 1, 0]),
    }}
  >
    <CardBackground blur={12} bgColor="rgba(15, 23, 42, 0.88)" />
    <AccentBar color="#EF4444" />

    {/* Main stat */}
    <StatNumber
      text="1.7x"
      style={{
        transform: `scale(${interpolate(frame, [15, 35], [0.8, 1.0], { extrapolateRight: 'clamp' })})`,
        opacity: interpolate(frame, [15, 35], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
      }}
    />

    <StatDescriptor
      text="more issues in AI-generated code"
      opacity={interpolate(frame, [30, 45], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />

    {/* Detail rows */}
    <DetailRow
      icon="error"
      text="75% logic errors"
      color="#EF4444"
      style={{
        opacity: interpolate(frame, [40, 60], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
        transform: `translateX(${interpolate(frame, [40, 60], [-20, 0], { extrapolateRight: 'clamp' })}px)`,
      }}
    />
    <DetailRow
      icon="warning"
      text="8x perf problems"
      color="#F59E0B"
      style={{
        opacity: interpolate(frame, [55, 75], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
        transform: `translateX(${interpolate(frame, [55, 75], [-20, 0], { extrapolateRight: 'clamp' })}px)`,
      }}
    />

    <SourceAttribution
      text="CodeRabbit, 2024"
      opacity={interpolate(frame, [70, 85], [0, 0.7], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />
  </StatCalloutCard>
</Sequence>
```

## Data Points
```json
{
  "stat": "1.7x",
  "descriptor": "more issues in AI-generated code",
  "details": [
    {"text": "75% logic errors", "color": "#EF4444", "icon": "error"},
    {"text": "8x perf problems", "color": "#F59E0B", "icon": "warning"}
  ],
  "source": "CodeRabbit, 2024",
  "card_position": {"x": 1060, "y": 300, "width": 800, "height": 420},
  "totalFrames": 300,
  "fps": 30
}
```

---
