[Remotion] DORA Stat Callout — AI Without Tests = Instability

# Section 3.3: Stat Callout — DORA AI and Testing Study

**Tool:** Remotion
**Duration:** ~10s
**Timestamp:** 0:40 - 0:50

## Visual Description
A data callout card that slides in from the left side of the frame (opposite side from the CodeRabbit card for visual balance). The card presents a dual-stat comparison: the top half shows "AI without tests" with a red downward arrow and "instability" label; the bottom half shows "AI with tests" with a green upward arrow and "delivery amplification" label. A thin horizontal divider separates the two states. The card has a frosted glass background with a green left-edge accent bar, emphasizing the positive outcome when tests are present. Source: "DORA State of DevOps, 2024."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay
- Card position: left-aligned, vertically centered — card at (60, 300) to (860, 700)
- Card size: 800px x 400px

### Chart/Visual Elements
- Card background: rgba(15, 23, 42, 0.88) with backdrop-filter blur(12px)
- Card border: 1px solid rgba(34, 197, 94, 0.3)
- Card border-radius: 16px
- Left accent bar: 4px x full height, #22C55E (test green)
- Top section ("without tests"):
  - Label: "AI without tests" — muted text
  - Arrow: downward chevron, #EF4444, 32px
  - Result: "instability" — red text, bold
- Horizontal divider: 1px, rgba(255,255,255,0.1), at vertical midpoint
- Bottom section ("with tests"):
  - Label: "AI with tests" — muted text
  - Arrow: upward chevron, #22C55E, 32px
  - Result: "delivery amplification" — green text, bold
- Source: "DORA State of DevOps, 2024" — small text, bottom of card
- Subtle glow: box-shadow 0 8px 32px rgba(34, 197, 94, 0.15)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Card slides in from left — translateX(-200)→translateX(0), opacity 0→1.
2. **Frame 20-40 (0.67-1.33s):** Top section fades in — "AI without tests" label, red arrow, "instability."
3. **Frame 35-50 (1.17-1.67s):** Horizontal divider fades in — opacity 0→0.1.
4. **Frame 45-65 (1.5-2.17s):** Bottom section fades in — "AI with tests" label, green arrow, "delivery amplification."
5. **Frame 60-75 (2-2.5s):** Green result text pulses briefly — scale 1.0→1.05→1.0 with brightness increase.
6. **Frame 70-85 (2.33-2.83s):** Source attribution fades in — opacity 0→0.7.
7. **Frame 85-250 (2.83-8.33s):** Hold. Card fully visible.
8. **Frame 250-300 (8.33-10s):** Card slides out to left — translateX(0)→translateX(-200), opacity 1→0.

### Typography
- Labels: Inter Regular, 20px, #94A3B8 (muted blue-gray)
- Result "instability": Inter Bold, 32px, #EF4444
- Result "delivery amplification": Inter Bold, 32px, #22C55E
- Arrow icons: 32px, inline before result text
- Source: Inter Regular, 16px, #64748B (muted)

### Easing
- Card slide in: `spring({ damping: 15, stiffness: 180 })`
- Section fades: `easeOutQuad`
- Green pulse: `easeInOutSine`
- Card slide out: `easeInCubic`

## Narration Sync
> "DORA's State of DevOps report found that AI without tests leads to instability — but AI with tests becomes a delivery amplifier."

Top section appears on "AI without tests leads to instability." Bottom section appears on "AI with tests becomes a delivery amplifier." The green pulse emphasizes "delivery amplifier."

## Code Structure (Remotion)
```typescript
<Sequence from={DORA_STAT_START} durationInFrames={300}>
  <StatCalloutCard
    side="left"
    style={{
      transform: `translateX(${interpolate(frame, [0, 20, 250, 300], [-200, 0, 0, -200])}px)`,
      opacity: interpolate(frame, [0, 20, 250, 300], [0, 1, 1, 0]),
    }}
  >
    <CardBackground blur={12} bgColor="rgba(15, 23, 42, 0.88)" />
    <AccentBar color="#22C55E" />

    {/* Top: without tests */}
    <DualStatSection
      label="AI without tests"
      arrow="down"
      arrowColor="#EF4444"
      result="instability"
      resultColor="#EF4444"
      opacity={interpolate(frame, [20, 40], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />

    <Divider opacity={interpolate(frame, [35, 50], [0, 0.1])} />

    {/* Bottom: with tests */}
    <DualStatSection
      label="AI with tests"
      arrow="up"
      arrowColor="#22C55E"
      result="delivery amplification"
      resultColor="#22C55E"
      opacity={interpolate(frame, [45, 65], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
      pulseFrames={[60, 75]}
    />

    <SourceAttribution
      text="DORA State of DevOps, 2024"
      opacity={interpolate(frame, [70, 85], [0, 0.7], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />
  </StatCalloutCard>
</Sequence>
```

## Data Points
```json
{
  "without_tests": {
    "label": "AI without tests",
    "result": "instability",
    "color": "#EF4444",
    "arrow": "down"
  },
  "with_tests": {
    "label": "AI with tests",
    "result": "delivery amplification",
    "color": "#22C55E",
    "arrow": "up"
  },
  "source": "DORA State of DevOps, 2024",
  "card_position": {"x": 60, "y": 300, "width": 800, "height": 400},
  "totalFrames": 300,
  "fps": 30
}
```

---
