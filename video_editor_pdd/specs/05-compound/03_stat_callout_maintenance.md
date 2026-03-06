[Remotion] Maintenance Cost Stat Callout — 80-90% of Software Cost

# Section 5.2: Stat Callout — Maintenance Cost Dominance

**Tool:** Remotion
**Duration:** ~10s
**Timestamp:** 0:15 - 0:25

## Visual Description
A data callout card that slides in from the right side of the frame. The card features the headline stat "80–90%" in large bold text with a subheading "of software cost is maintenance" and a source attribution "IEEE / Industry Studies". Below the main stat, two qualifying details appear sequentially: "Not features" in muted blue and "Not launch" in muted green — emphasizing what maintenance crowds out. The card has a frosted glass background with a red left-edge accent bar, signaling the severity of the statistic. After holding for 6 seconds, it slides back out to the right.

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
- Stat number: "80–90%" — large, positioned at top-left of card content
- Stat descriptor: "of software cost is maintenance" — below stat number
- Detail row 1: "Not features" — muted blue text with dash icon
- Detail row 2: "Not launch" — muted green text with dash icon
- Source: "IEEE / Industry Studies" — small text, bottom of card
- Subtle glow: box-shadow 0 8px 32px rgba(239, 68, 68, 0.15)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Card slides in from right — translateX(200)→translateX(0), opacity 0→1.
2. **Frame 15-35 (0.5-1.17s):** Stat "80–90%" animates — scale 0.8→1.0, opacity 0→1.
3. **Frame 30-45 (1-1.5s):** Descriptor text fades in — opacity 0→1.
4. **Frame 40-60 (1.33-2s):** Detail "Not features" slides in from left within card — translateX(-20)→0, opacity 0→1.
5. **Frame 55-75 (1.83-2.5s):** Detail "Not launch" slides in — same animation, staggered.
6. **Frame 70-85 (2.33-2.83s):** Source attribution fades in — opacity 0→0.7.
7. **Frame 85-250 (2.83-8.33s):** Hold. Card fully visible.
8. **Frame 250-300 (8.33-10s):** Card slides out to right — translateX(0)→translateX(200), opacity 1→0.

### Typography
- Stat number: Inter Black, 88px, #FFFFFF
- Stat descriptor: Inter Medium, 26px, #CBD5E1
- Detail row 1: Inter SemiBold, 22px, #3B82F6 (blue)
- Detail row 2: Inter SemiBold, 22px, #22C55E (green)
- Icons: 18px inline dash, matching text color
- Source: Inter Regular, 16px, #64748B (muted)

### Easing
- Card slide in: `spring({ damping: 15, stiffness: 180 })`
- Stat scale: `easeOutCubic`
- Detail slides: `easeOutQuad`
- Text fades: `easeOutQuad`
- Card slide out: `easeInCubic`

## Narration Sync
> "Eighty to ninety percent of software cost is maintenance. Not features. Not launch. Maintenance."

The "80–90%" stat animates in as "eighty to ninety percent" is spoken. "Not features" appears on "Not features." "Not launch" appears on "Not launch."

## Code Structure (Remotion)
```typescript
<Sequence from={MAINTENANCE_STAT_START} durationInFrames={300}>
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
      text="80–90%"
      style={{
        transform: `scale(${interpolate(frame, [15, 35], [0.8, 1.0], { extrapolateRight: 'clamp' })})`,
        opacity: interpolate(frame, [15, 35], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
      }}
    />

    <StatDescriptor
      text="of software cost is maintenance"
      opacity={interpolate(frame, [30, 45], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />

    {/* Detail rows */}
    <DetailRow
      icon="dash"
      text="Not features"
      color="#3B82F6"
      style={{
        opacity: interpolate(frame, [40, 60], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
        transform: `translateX(${interpolate(frame, [40, 60], [-20, 0], { extrapolateRight: 'clamp' })}px)`,
      }}
    />
    <DetailRow
      icon="dash"
      text="Not launch"
      color="#22C55E"
      style={{
        opacity: interpolate(frame, [55, 75], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
        transform: `translateX(${interpolate(frame, [55, 75], [-20, 0], { extrapolateRight: 'clamp' })}px)`,
      }}
    />

    <SourceAttribution
      text="IEEE / Industry Studies"
      opacity={interpolate(frame, [70, 85], [0, 0.7], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />
  </StatCalloutCard>
</Sequence>
```

## Data Points
```json
{
  "stat": "80–90%",
  "descriptor": "of software cost is maintenance",
  "details": [
    {"text": "Not features", "color": "#3B82F6", "icon": "dash"},
    {"text": "Not launch", "color": "#22C55E", "icon": "dash"}
  ],
  "source": "IEEE / Industry Studies",
  "card_position": {"x": 1060, "y": 300, "width": 800, "height": 420},
  "totalFrames": 300,
  "fps": 30
}
```

---
