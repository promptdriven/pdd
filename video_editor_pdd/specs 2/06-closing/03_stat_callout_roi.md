[Remotion] ROI Stat Callout — Economics Have Flipped

# Section 6.2: Stat Callout — ROI on PDD Adoption

**Tool:** Remotion
**Duration:** ~6s
**Timestamp:** 0:03 - 0:09

## Visual Description
A data callout card that slides in from the right side of the frame. The card features the headline stat "3–5×" in large bold text with a subheading "faster iteration with generation" and a source attribution "Early PDD Adopters". Below the main stat, two qualifying details appear sequentially: "Zero residual debt" in green and "Compounds each cycle" in amber — reinforcing that this isn't just speed but accumulating advantage. The card has a frosted glass background with an amber left-edge accent bar, signaling the opportunity. After holding for 3 seconds, it slides back out.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay
- Card position: right-aligned, vertically centered — card at (1060, 300) to (1860, 700)
- Card size: 800px x 400px

### Chart/Visual Elements
- Card background: rgba(15, 23, 42, 0.88) with backdrop-filter blur(12px) — frosted glass
- Card border: 1px solid rgba(245, 158, 11, 0.3)
- Card border-radius: 16px
- Left accent bar: 4px x full height, #F59E0B (amber)
- Stat number: "3–5×" — large, positioned at top-left of card content
- Stat descriptor: "faster iteration with generation" — below stat number
- Detail row 1: "Zero residual debt" — green text with checkmark icon
- Detail row 2: "Compounds each cycle" — amber text with trending-up icon
- Source: "Early PDD Adopters" — small text, bottom of card
- Subtle glow: box-shadow 0 8px 32px rgba(245, 158, 11, 0.15)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Card slides in from right — translateX(200)→translateX(0), opacity 0→1.
2. **Frame 15-32 (0.5-1.07s):** Stat "3–5×" animates — scale 0.8→1.0, opacity 0→1.
3. **Frame 28-42 (0.93-1.4s):** Descriptor text fades in — opacity 0→1.
4. **Frame 38-55 (1.27-1.83s):** Detail "Zero residual debt" slides in — translateX(-20)→0, opacity 0→1.
5. **Frame 50-67 (1.67-2.23s):** Detail "Compounds each cycle" slides in — same animation, staggered.
6. **Frame 62-75 (2.07-2.5s):** Source attribution fades in — opacity 0→0.7.
7. **Frame 75-140 (2.5-4.67s):** Hold. Card fully visible.
8. **Frame 140-180 (4.67-6s):** Card slides out to right — translateX(0)→translateX(200), opacity 1→0.

### Typography
- Stat number: Inter Black, 88px, #FFFFFF
- Stat descriptor: Inter Medium, 26px, #CBD5E1
- Detail row 1: Inter SemiBold, 22px, #22C55E (green)
- Detail row 2: Inter SemiBold, 22px, #F59E0B (amber)
- Icons: 18px inline, matching text color (checkmark for row 1, trending-up for row 2)
- Source: Inter Regular, 16px, #64748B (muted)

### Easing
- Card slide in: `spring({ damping: 15, stiffness: 180 })`
- Stat scale: `easeOutCubic`
- Detail slides: `easeOutQuad`
- Text fades: `easeOutQuad`
- Card slide out: `easeInCubic`

## Narration Sync
> "The economics have flipped. Patching is the old way — expensive, fragile, compounding."

The "3–5×" stat animates in overlapping with "economics have flipped." "Zero residual debt" appears as "expensive, fragile" is spoken — contrasting the old way. "Compounds each cycle" appears on "compounding" — reframing the concept positively.

## Code Structure (Remotion)
```typescript
<Sequence from={ROI_STAT_START} durationInFrames={180}>
  <StatCalloutCard
    style={{
      transform: `translateX(${interpolate(frame, [0, 20, 140, 180], [200, 0, 0, 200])}px)`,
      opacity: interpolate(frame, [0, 20, 140, 180], [0, 1, 1, 0]),
    }}
  >
    <CardBackground blur={12} bgColor="rgba(15, 23, 42, 0.88)" />
    <AccentBar color="#F59E0B" />

    {/* Main stat */}
    <StatNumber
      text="3–5×"
      style={{
        transform: `scale(${interpolate(frame, [15, 32], [0.8, 1.0], { extrapolateRight: 'clamp' })})`,
        opacity: interpolate(frame, [15, 32], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
      }}
    />

    <StatDescriptor
      text="faster iteration with generation"
      opacity={interpolate(frame, [28, 42], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />

    {/* Detail rows */}
    <DetailRow
      icon="checkmark"
      text="Zero residual debt"
      color="#22C55E"
      style={{
        opacity: interpolate(frame, [38, 55], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
        transform: `translateX(${interpolate(frame, [38, 55], [-20, 0], { extrapolateRight: 'clamp' })}px)`,
      }}
    />
    <DetailRow
      icon="trending_up"
      text="Compounds each cycle"
      color="#F59E0B"
      style={{
        opacity: interpolate(frame, [50, 67], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
        transform: `translateX(${interpolate(frame, [50, 67], [-20, 0], { extrapolateRight: 'clamp' })}px)`,
      }}
    />

    <SourceAttribution
      text="Early PDD Adopters"
      opacity={interpolate(frame, [62, 75], [0, 0.7], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />
  </StatCalloutCard>
</Sequence>
```

## Data Points
```json
{
  "stat": "3–5×",
  "descriptor": "faster iteration with generation",
  "details": [
    {"text": "Zero residual debt", "color": "#22C55E", "icon": "checkmark"},
    {"text": "Compounds each cycle", "color": "#F59E0B", "icon": "trending_up"}
  ],
  "source": "Early PDD Adopters",
  "card_position": {"x": 1060, "y": 300, "width": 800, "height": 400},
  "totalFrames": 180,
  "fps": 30
}
```

---
