[Remotion] Uplevel Stat Callout — 800 Devs, No Throughput Change, 41% More Bugs

# Section 1.5: Stat Callout — Uplevel Study

**Tool:** Remotion
**Duration:** ~10s
**Timestamp:** 2:50 - 3:00

## Visual Description
A stat callout card that slides in from the left side over the debt accumulation Veo background. This card has an ominous red accent, reflecting the negative finding. The headline shows "0% throughput change" in large text, with "41% more bugs" below in danger red as a secondary stat. The source reads "Uplevel — 800 developers, 6 months." A subtle red pulse effect on the card border emphasizes the alarming nature of the data. The card holds, then slides out to the left.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay
- Card position: left-aligned, vertically centered — card at (80, 320) to (840, 700)
- Card size: 760px x 380px

### Chart/Visual Elements
- Card background: rgba(15, 23, 42, 0.88) with backdrop-filter blur(12px)
- Card border: 1px solid rgba(239, 68, 68, 0.4) — red tint, pulsing
- Card border-radius: 16px
- Left accent bar: 4px x full height, #EF4444 (danger red)
- Primary stat: "0%" — large, white
- Primary descriptor: "throughput change" — below primary stat
- Secondary stat: "41%" — medium, #EF4444
- Secondary descriptor: "more bugs introduced" — next to secondary stat
- Source: "Uplevel Study — 800 developers, 6 months" — small text
- Border pulse: red glow oscillates 0.3→0.6 opacity, 3s cycle

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Card slides in from left — translateX(-200)→translateX(0), opacity 0→1.
2. **Frame 15-30 (0.5-1s):** Primary "0%" appears — scale 0.85→1.0, opacity 0→1.
3. **Frame 25-40 (0.83-1.33s):** "throughput change" fades in.
4. **Frame 40-65 (1.33-2.17s):** Secondary stat "41%" counter animates 0→41, color fades to #EF4444. "more bugs" text appears.
5. **Frame 60-80 (2-2.67s):** Source attribution fades in — opacity 0→0.6.
6. **Frame 80-240 (2.67-8s):** Hold. Border red pulse cycles.
7. **Frame 240-300 (8-10s):** Card slides out to left — translateX(0)→translateX(-200), opacity 1→0.

### Typography
- Primary stat: Inter Black, 88px, #FFFFFF
- Primary descriptor: Inter Medium, 26px, #CBD5E1
- Secondary stat: Inter Black, 56px, #EF4444
- Secondary descriptor: Inter Medium, 22px, #FCA5A5
- Source: Inter Regular, 15px, #64748B

### Easing
- Card slide in: `spring({ damping: 14, stiffness: 170 })`
- Counter animate: `easeOutCubic`
- Text fades: `easeOutQuad`
- Border pulse: sinusoidal, 3s period
- Card slide out: `easeInCubic`

## Narration Sync
> "Uplevel tracked 800 developers for six months. Throughput? No change. Bug rate? Up 41 percent."

"0%" appears as "Throughput? No change." is spoken. "41%" animates in on "Bug rate? Up 41 percent."

## Code Structure (Remotion)
```typescript
<Sequence from={UPLEVEL_STAT_START} durationInFrames={300}>
  <StatCalloutCard
    position="left"
    style={{
      transform: `translateX(${interpolate(frame, [0, 20, 240, 300], [-200, 0, 0, -200])}px)`,
      opacity: interpolate(frame, [0, 20, 240, 300], [0, 1, 1, 0]),
      borderColor: `rgba(239, 68, 68, ${interpolate(Math.sin(frame * 0.07), [-1, 1], [0.3, 0.6])})`,
    }}
  >
    <AccentBar color="#EF4444" />

    {/* Primary stat */}
    <StatNumber value={0} suffix="%" fontSize={88} color="#FFFFFF"
      style={{ transform: `scale(${interpolate(frame, [15, 30], [0.85, 1.0], { extrapolateRight: 'clamp' })})` }}
    />
    <StatDescriptor text="throughput change"
      opacity={interpolate(frame, [25, 40], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />

    {/* Secondary stat */}
    <StatNumber
      value={Math.round(interpolate(frame, [40, 65], [0, 41], { extrapolateRight: 'clamp' }))}
      suffix="%"
      fontSize={56}
      color="#EF4444"
    />
    <StatDescriptor text="more bugs introduced" color="#FCA5A5"
      opacity={interpolate(frame, [50, 65], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />

    <SourceAttribution text="Uplevel Study — 800 developers, 6 months"
      opacity={interpolate(frame, [60, 80], [0, 0.6], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />
  </StatCalloutCard>
</Sequence>
```

## Data Points
```json
{
  "primary_stat": "0%",
  "primary_descriptor": "throughput change",
  "secondary_stat": "41%",
  "secondary_descriptor": "more bugs introduced",
  "source": "Uplevel Study — 800 developers, 6 months",
  "accent_color": "#EF4444",
  "card_position": {"x": 80, "y": 320, "width": 760, "height": 380},
  "totalFrames": 300,
  "fps": 30
}
```

---
