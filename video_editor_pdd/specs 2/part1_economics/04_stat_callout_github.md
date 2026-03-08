[Remotion] GitHub Stat Callout — 55% Speedup, Greenfield Only

# Section 1.3: Stat Callout — GitHub Copilot Study

**Tool:** Remotion
**Duration:** ~8s
**Timestamp:** 1:30 - 1:38

## Visual Description
A data callout card that slides in from the right side of the frame. The card features the headline stat "55%" in large bold text with a subheading "faster task completion" and a source attribution "GitHub Copilot Study, 2023". Below the main stat, a qualifying footnote reads "greenfield tasks only" in amber warning text. The card has a frosted glass background with a blue left-edge accent bar. After holding for 5 seconds, it slides back out to the right.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay
- Card position: right-aligned, vertically centered — card at (1080, 340) to (1840, 680)
- Card size: 760px x 340px

### Chart/Visual Elements
- Card background: rgba(15, 23, 42, 0.85) with backdrop-filter blur(12px) — frosted glass
- Card border: 1px solid rgba(59, 130, 246, 0.3)
- Card border-radius: 16px
- Left accent bar: 4px x full height, #3B82F6 (vibrant blue)
- Stat number: "55%" — large, positioned at top-left of card content
- Stat descriptor: "faster task completion" — below stat number
- Source: "GitHub Copilot Study, 2023" — small text, bottom of card
- Qualifier: "greenfield tasks only" — amber warning text with small caution icon
- Subtle glow: box-shadow 0 8px 32px rgba(59, 130, 246, 0.2)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Card slides in from right — translateX(200)→translateX(0), opacity 0→1.
2. **Frame 15-30 (0.5-1s):** Stat "55%" counter animates from 0→55, scale 0.8→1.0.
3. **Frame 25-40 (0.83-1.33s):** Descriptor text fades in — opacity 0→1.
4. **Frame 35-50 (1.17-1.67s):** Source attribution fades in — opacity 0→0.7.
5. **Frame 45-65 (1.5-2.17s):** Qualifier "greenfield tasks only" fades in — opacity 0→1, slight pulse on amber color.
6. **Frame 65-195 (2.17-6.5s):** Hold. Card fully visible.
7. **Frame 195-240 (6.5-8s):** Card slides out to right — translateX(0)→translateX(200), opacity 1→0.

### Typography
- Stat number: Inter Black, 96px, #FFFFFF
- Stat descriptor: Inter Medium, 28px, #CBD5E1
- Source: Inter Regular, 16px, #64748B (muted)
- Qualifier: Inter SemiBold, 20px, #F59E0B (amber accent)
- Caution icon: 16px, inline before qualifier text

### Easing
- Card slide in: `spring({ damping: 15, stiffness: 180 })`
- Counter animate: `easeOutCubic`
- Text fades: `easeOutQuad`
- Card slide out: `easeInCubic`

## Narration Sync
> "These tools write code fast. GitHub measured a 55% speedup — but only on greenfield tasks."

The "55%" stat animates in as the narrator says "55% speedup." The qualifier appears as "but only on greenfield tasks" is spoken.

## Code Structure (Remotion)
```typescript
<Sequence from={GITHUB_STAT_START} durationInFrames={240}>
  <StatCalloutCard
    style={{
      transform: `translateX(${interpolate(frame, [0, 20, 195, 240], [200, 0, 0, 200])}px)`,
      opacity: interpolate(frame, [0, 20, 195, 240], [0, 1, 1, 0]),
    }}
  >
    {/* Frosted glass card */}
    <CardBackground blur={12} bgColor="rgba(15, 23, 42, 0.85)" />
    <AccentBar color="#3B82F6" />

    {/* Main stat */}
    <StatNumber
      value={Math.round(interpolate(frame, [15, 30], [0, 55], { extrapolateRight: 'clamp' }))}
      suffix="%"
      style={{
        transform: `scale(${interpolate(frame, [15, 30], [0.8, 1.0], { extrapolateRight: 'clamp' })})`,
      }}
    />

    {/* Descriptor */}
    <StatDescriptor
      text="faster task completion"
      opacity={interpolate(frame, [25, 40], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />

    {/* Source */}
    <SourceAttribution
      text="GitHub Copilot Study, 2023"
      opacity={interpolate(frame, [35, 50], [0, 0.7], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />

    {/* Qualifier with warning */}
    <Qualifier
      text="greenfield tasks only"
      icon="caution"
      color="#F59E0B"
      opacity={interpolate(frame, [45, 65], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />
  </StatCalloutCard>
</Sequence>
```

## Data Points
```json
{
  "stat": "55%",
  "descriptor": "faster task completion",
  "source": "GitHub Copilot Study, 2023",
  "qualifier": "greenfield tasks only",
  "qualifier_color": "#F59E0B",
  "card_position": {"x": 1080, "y": 340, "width": 760, "height": 340},
  "totalFrames": 240,
  "fps": 30
}
```

---
