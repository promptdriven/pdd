[Remotion] NL Context Stat Callout — 41% Improved Code Generation

# Section 3.7: Stat Callout — Natural Language Context Study

**Tool:** Remotion
**Duration:** ~8s
**Timestamp:** 3:27 - 3:35

## Visual Description
A data callout card that slides in from the right side of the frame. The card features the headline stat "41%" in large bold text with a subheading "improved code generation" and a qualifier "when natural language context is provided." The card has a frosted glass background with a gold left-edge accent bar, tying it to the prompt capital theme. A secondary stat "30x" appears below with "more NL than code in training data" to reinforce why prompts are powerful. Source attribution reads "Rao et al., 2024."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay
- Card position: right-aligned, vertically centered — card at (1060, 320) to (1860, 700)
- Card size: 800px x 380px

### Chart/Visual Elements
- Card background: rgba(15, 23, 42, 0.88) with backdrop-filter blur(12px) — frosted glass
- Card border: 1px solid rgba(245, 158, 11, 0.3)
- Card border-radius: 16px
- Left accent bar: 4px x full height, #F59E0B (prompt gold)
- Primary stat: "41%" — large, positioned at top-left of card content
- Primary descriptor: "improved code generation" — below stat
- Qualifier: "with natural language context" — smaller, gold tint
- Secondary stat: "30x" — medium size, below a thin divider
- Secondary descriptor: "more NL than code in training data"
- Source: "Rao et al., 2024" — small text, bottom of card
- Subtle glow: box-shadow 0 8px 32px rgba(245, 158, 11, 0.15)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Card slides in from right — translateX(200)→translateX(0), opacity 0→1.
2. **Frame 15-35 (0.5-1.17s):** Primary stat "41%" counter animates 0→41, scale 0.8→1.0.
3. **Frame 30-45 (1-1.5s):** Primary descriptor fades in — opacity 0→1.
4. **Frame 40-55 (1.33-1.83s):** Qualifier fades in — opacity 0→0.9.
5. **Frame 50-60 (1.67-2s):** Thin divider fades in.
6. **Frame 55-75 (1.83-2.5s):** Secondary stat "30x" fades in — scale 0.9→1.0.
7. **Frame 70-85 (2.33-2.83s):** Secondary descriptor and source fade in.
8. **Frame 85-195 (2.83-6.5s):** Hold.
9. **Frame 195-240 (6.5-8s):** Card slides out to right — translateX(0)→translateX(200), opacity 1→0.

### Typography
- Primary stat: Inter Black, 88px, #FFFFFF
- Primary descriptor: Inter Medium, 26px, #CBD5E1
- Qualifier: Inter Medium, 20px, #F59E0B (gold)
- Secondary stat: Inter Black, 48px, #F59E0B
- Secondary descriptor: Inter Regular, 20px, #94A3B8
- Source: Inter Regular, 16px, #64748B (muted)

### Easing
- Card slide in: `spring({ damping: 15, stiffness: 180 })`
- Counter animate: `easeOutCubic`
- Text fades: `easeOutQuad`
- Card slide out: `easeInCubic`

## Narration Sync
> "Natural language comments improved code generation by 41 percent. Models are trained on 30 times more natural language than code — the prompt speaks their native language."

"41%" animates on "41 percent." "30x" appears on "30 times more natural language."

## Code Structure (Remotion)
```typescript
<Sequence from={NL_STAT_START} durationInFrames={240}>
  <StatCalloutCard
    style={{
      transform: `translateX(${interpolate(frame, [0, 20, 195, 240], [200, 0, 0, 200])}px)`,
      opacity: interpolate(frame, [0, 20, 195, 240], [0, 1, 1, 0]),
    }}
  >
    <CardBackground blur={12} bgColor="rgba(15, 23, 42, 0.88)" />
    <AccentBar color="#F59E0B" />

    {/* Primary stat */}
    <StatNumber
      value={Math.round(interpolate(frame, [15, 35], [0, 41], { extrapolateRight: 'clamp' }))}
      suffix="%"
      style={{
        transform: `scale(${interpolate(frame, [15, 35], [0.8, 1.0], { extrapolateRight: 'clamp' })})`,
      }}
    />
    <StatDescriptor
      text="improved code generation"
      opacity={interpolate(frame, [30, 45], [0, 1])}
    />
    <Qualifier
      text="with natural language context"
      color="#F59E0B"
      opacity={interpolate(frame, [40, 55], [0, 0.9])}
    />

    <Divider opacity={interpolate(frame, [50, 60], [0, 0.15])} />

    {/* Secondary stat */}
    <StatNumber
      text="30x"
      fontSize={48}
      color="#F59E0B"
      style={{
        opacity: interpolate(frame, [55, 75], [0, 1]),
        transform: `scale(${interpolate(frame, [55, 75], [0.9, 1.0], { extrapolateRight: 'clamp' })})`,
      }}
    />
    <StatDescriptor
      text="more NL than code in training data"
      fontSize={20}
      color="#94A3B8"
      opacity={interpolate(frame, [70, 85], [0, 1])}
    />

    <SourceAttribution
      text="Rao et al., 2024"
      opacity={interpolate(frame, [70, 85], [0, 0.7])}
    />
  </StatCalloutCard>
</Sequence>
```

## Data Points
```json
{
  "primary_stat": "41%",
  "primary_descriptor": "improved code generation",
  "qualifier": "with natural language context",
  "secondary_stat": "30x",
  "secondary_descriptor": "more NL than code in training data",
  "source": "Rao et al., 2024",
  "card_position": {"x": 1060, "y": 320, "width": 800, "height": 380},
  "totalFrames": 240,
  "fps": 30
}
```

---
