[Remotion] CISQ Stat Callout — $2.41 Trillion Cost of Poor Software Quality

# Section 5.4: Stat Callout — CISQ Poor Software Quality Cost

**Tool:** Remotion
**Duration:** ~10s
**Timestamp:** 0:30 - 0:40

## Visual Description
A data callout card that slides in from the left side of the frame (opposite side from the maintenance stat, creating visual variety). The card features the headline stat "$2.41T" in large bold text with a subheading "cost of poor software quality in the US" and a source attribution "CISQ, 2022". Below the main stat, two qualifying details appear sequentially: "Technical debt is #1 driver" in red and "Growing 15% year-over-year" in amber — emphasizing the accelerating nature of the problem. The card has a frosted glass background with a danger red left-edge accent bar. After holding for 6 seconds, it slides back out to the left.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay
- Card position: left-aligned, vertically centered — card at (60, 300) to (860, 720)
- Card size: 800px x 420px

### Chart/Visual Elements
- Card background: rgba(15, 23, 42, 0.88) with backdrop-filter blur(12px) — frosted glass
- Card border: 1px solid rgba(239, 68, 68, 0.3)
- Card border-radius: 16px
- Left accent bar: 4px x full height, #EF4444 (red)
- Stat number: "$2.41T" — large, positioned at top-left of card content
- Stat descriptor: "cost of poor software quality in the US" — below stat number
- Detail row 1: "Technical debt is #1 driver" — red text with warning icon
- Detail row 2: "Growing 15% year-over-year" — amber text with trending-up icon
- Source: "CISQ, 2022" — small text, bottom of card
- Subtle glow: box-shadow 0 8px 32px rgba(239, 68, 68, 0.15)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Card slides in from left — translateX(-200)→translateX(0), opacity 0→1.
2. **Frame 15-35 (0.5-1.17s):** Stat "$2.41T" animates — scale 0.8→1.0, opacity 0→1.
3. **Frame 30-45 (1-1.5s):** Descriptor text fades in — opacity 0→1.
4. **Frame 40-60 (1.33-2s):** Detail "Technical debt is #1 driver" slides in from right within card — translateX(20)→0, opacity 0→1.
5. **Frame 55-75 (1.83-2.5s):** Detail "Growing 15% year-over-year" slides in — same animation, staggered.
6. **Frame 70-85 (2.33-2.83s):** Source attribution fades in — opacity 0→0.7.
7. **Frame 85-250 (2.83-8.33s):** Hold. Card fully visible.
8. **Frame 250-300 (8.33-10s):** Card slides out to left — translateX(0)→translateX(-200), opacity 1→0.

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
> "Patching accumulates debt linearly — each patch adds residual complexity."

The "$2.41T" stat animates in during the narration about debt accumulation. "Technical debt is #1 driver" appears as "residual complexity" is spoken. "Growing 15% year-over-year" appears shortly after.

## Code Structure (Remotion)
```typescript
<Sequence from={CISQ_STAT_START} durationInFrames={300}>
  <StatCalloutCard
    side="left"
    style={{
      transform: `translateX(${interpolate(frame, [0, 20, 250, 300], [-200, 0, 0, -200])}px)`,
      opacity: interpolate(frame, [0, 20, 250, 300], [0, 1, 1, 0]),
    }}
  >
    <CardBackground blur={12} bgColor="rgba(15, 23, 42, 0.88)" />
    <AccentBar color="#EF4444" />

    {/* Main stat */}
    <StatNumber
      text="$2.41T"
      style={{
        transform: `scale(${interpolate(frame, [15, 35], [0.8, 1.0], { extrapolateRight: 'clamp' })})`,
        opacity: interpolate(frame, [15, 35], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
      }}
    />

    <StatDescriptor
      text="cost of poor software quality in the US"
      opacity={interpolate(frame, [30, 45], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />

    {/* Detail rows */}
    <DetailRow
      icon="warning"
      text="Technical debt is #1 driver"
      color="#EF4444"
      style={{
        opacity: interpolate(frame, [40, 60], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
        transform: `translateX(${interpolate(frame, [40, 60], [20, 0], { extrapolateRight: 'clamp' })}px)`,
      }}
    />
    <DetailRow
      icon="trending_up"
      text="Growing 15% year-over-year"
      color="#F59E0B"
      style={{
        opacity: interpolate(frame, [55, 75], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
        transform: `translateX(${interpolate(frame, [55, 75], [20, 0], { extrapolateRight: 'clamp' })}px)`,
      }}
    />

    <SourceAttribution
      text="CISQ, 2022"
      opacity={interpolate(frame, [70, 85], [0, 0.7], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />
  </StatCalloutCard>
</Sequence>
```

## Data Points
```json
{
  "stat": "$2.41T",
  "descriptor": "cost of poor software quality in the US",
  "details": [
    {"text": "Technical debt is #1 driver", "color": "#EF4444", "icon": "warning"},
    {"text": "Growing 15% year-over-year", "color": "#F59E0B", "icon": "trending_up"}
  ],
  "source": "CISQ, 2022",
  "card_position": {"x": 60, "y": 300, "width": 800, "height": 420},
  "totalFrames": 300,
  "fps": 30
}
```

---
