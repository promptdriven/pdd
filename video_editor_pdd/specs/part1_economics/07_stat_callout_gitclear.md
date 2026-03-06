[Remotion] GitClear Stat Callout — 211M Lines, Churn +44%, Refactoring -60%

# Section 1.6: Stat Callout — GitClear Study

**Tool:** Remotion
**Duration:** ~10s
**Timestamp:** 3:15 - 3:25

## Visual Description
A stat callout card that enters from the right side, appearing after the Uplevel card has departed. This card presents two parallel stat bars: "Churn" with an upward red arrow showing "+44%" and "Refactoring" with a downward red arrow showing "-60%". Both bars animate their fill to visualize the magnitude. The source reads "GitClear — 211 million lines analyzed." The dual-stat layout with opposing arrows creates a visual "scissors" effect — things getting worse in both directions simultaneously.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay
- Card position: right-aligned, vertically centered — card at (1020, 300) to (1840, 720)
- Card size: 820px x 420px

### Chart/Visual Elements
- Card background: rgba(15, 23, 42, 0.88) with backdrop-filter blur(12px)
- Card border: 1px solid rgba(239, 68, 68, 0.3)
- Card border-radius: 16px
- Left accent bar: 4px x full height, gradient #EF4444 → #F59E0B
- Stat bar A (Churn): horizontal bar, fills left-to-right to 44% of track width
  - Bar color: #EF4444 → #F59E0B gradient
  - Label: "Code Churn" left-aligned, "+44%" right of bar, upward arrow icon
  - Track background: rgba(239, 68, 68, 0.15)
- Stat bar B (Refactoring): horizontal bar, fills left-to-right to 60% of track width
  - Bar color: #EF4444 → #DC2626 gradient
  - Label: "Refactoring" left-aligned, "-60%" right of bar, downward arrow icon
  - Track background: rgba(239, 68, 68, 0.15)
- Headline: "211 million lines analyzed" — top of card
- Source: "GitClear, 2024" — bottom of card

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Card slides in from right — translateX(200)→translateX(0), opacity 0→1.
2. **Frame 15-35 (0.5-1.17s):** Headline "211 million lines analyzed" fades in.
3. **Frame 30-80 (1-2.67s):** Churn bar fills 0→44% of track. "+44%" counter animates. Arrow pulses.
4. **Frame 60-110 (2-3.67s):** Refactoring bar fills 0→60% of track. "-60%" counter animates. Arrow pulses.
5. **Frame 100-120 (3.33-4s):** Source fades in — opacity 0→0.6.
6. **Frame 120-240 (4-8s):** Hold.
7. **Frame 240-300 (8-10s):** Card slides out to right — translateX(0)→translateX(200), opacity 1→0.

### Typography
- Headline: Inter Bold, 28px, #FFFFFF
- Bar labels: Inter SemiBold, 22px, #CBD5E1
- Stat values: Inter Black, 40px, #EF4444
- Arrow icons: 24px, #EF4444
- Source: Inter Regular, 15px, #64748B

### Easing
- Card slide in: `spring({ damping: 14, stiffness: 170 })`
- Bar fill: `easeOutQuart`
- Counter animate: `easeOutCubic`
- Card slide out: `easeInCubic`

## Narration Sync
> "GitClear analyzed 211 million lines of code. Code churn — up 44 percent. Refactoring effort — down 60 percent."

Headline appears on "211 million lines." Churn bar fills on "churn — up 44 percent." Refactoring bar fills on "Refactoring effort — down 60 percent."

## Code Structure (Remotion)
```typescript
<Sequence from={GITCLEAR_STAT_START} durationInFrames={300}>
  <StatCalloutCard
    position="right"
    style={{
      transform: `translateX(${interpolate(frame, [0, 20, 240, 300], [200, 0, 0, 200])}px)`,
      opacity: interpolate(frame, [0, 20, 240, 300], [0, 1, 1, 0]),
    }}
  >
    <AccentBar gradient={['#EF4444', '#F59E0B']} />

    {/* Headline */}
    <Headline text="211 million lines analyzed"
      opacity={interpolate(frame, [15, 35], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />

    {/* Churn stat bar */}
    <StatBar
      label="Code Churn"
      value={Math.round(interpolate(frame, [30, 80], [0, 44], { extrapolateRight: 'clamp' }))}
      suffix="%"
      prefix="+"
      fillPercent={interpolate(frame, [30, 80], [0, 0.44], { easing: Easing.out(Easing.quart) })}
      barGradient={['#EF4444', '#F59E0B']}
      arrowDirection="up"
    />

    {/* Refactoring stat bar */}
    <StatBar
      label="Refactoring"
      value={Math.round(interpolate(frame, [60, 110], [0, 60], { extrapolateRight: 'clamp' }))}
      suffix="%"
      prefix="-"
      fillPercent={interpolate(frame, [60, 110], [0, 0.60], { easing: Easing.out(Easing.quart) })}
      barGradient={['#EF4444', '#DC2626']}
      arrowDirection="down"
    />

    <SourceAttribution text="GitClear, 2024"
      opacity={interpolate(frame, [100, 120], [0, 0.6], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />
  </StatCalloutCard>
</Sequence>
```

## Data Points
```json
{
  "headline": "211 million lines analyzed",
  "stats": [
    {
      "label": "Code Churn",
      "value": "+44%",
      "direction": "up",
      "bar_fill": 0.44,
      "color_gradient": ["#EF4444", "#F59E0B"]
    },
    {
      "label": "Refactoring",
      "value": "-60%",
      "direction": "down",
      "bar_fill": 0.60,
      "color_gradient": ["#EF4444", "#DC2626"]
    }
  ],
  "source": "GitClear, 2024",
  "card_position": {"x": 1020, "y": 300, "width": 820, "height": 420},
  "totalFrames": 300,
  "fps": 30
}
```

---
