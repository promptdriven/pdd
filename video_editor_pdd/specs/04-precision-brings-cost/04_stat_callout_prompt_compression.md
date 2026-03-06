[Remotion] Prompt Compression Stat Callout — 10x Token Reduction

# Section 4.3: Stat Callout — Prompt Compression

**Tool:** Remotion
**Duration:** ~8s
**Timestamp:** 0:22 - 0:30

## Visual Description
A data callout card that slides in from the right side of the frame. The card features the headline stat "10x" in large bold amber text with a subheading "token reduction with structured prompts" and a source attribution "PDD Benchmark, 2025". Below the main stat, a qualifying note reads "vs. free-form instructions" in cool blue text. The card has a frosted glass background with an amber left-edge accent bar. After holding for 5 seconds, it slides back out to the right.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay
- Card position: right-aligned, vertically centered — card at (1080, 340) to (1840, 680)
- Card size: 760px x 340px

### Chart/Visual Elements
- Card background: rgba(15, 23, 42, 0.85) with backdrop-filter blur(12px) — frosted glass
- Card border: 1px solid rgba(245, 158, 11, 0.3)
- Card border-radius: 16px
- Left accent bar: 4px x full height, #F59E0B (amber)
- Stat number: "10x" — large, positioned at top-left of card content
- Stat descriptor: "token reduction with structured prompts" — below stat number
- Source: "PDD Benchmark, 2025" — small text, bottom of card
- Qualifier: "vs. free-form instructions" — cool blue comparison text
- Subtle glow: box-shadow 0 8px 32px rgba(245, 158, 11, 0.2)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Card slides in from right — translateX(200)→translateX(0), opacity 0→1.
2. **Frame 15-35 (0.5-1.17s):** Stat "10x" counter animates — scale 0.8→1.0, opacity 0→1.
3. **Frame 25-40 (0.83-1.33s):** Descriptor text fades in — opacity 0→1.
4. **Frame 35-50 (1.17-1.67s):** Source attribution fades in — opacity 0→0.7.
5. **Frame 45-65 (1.5-2.17s):** Qualifier "vs. free-form instructions" fades in — opacity 0→1.
6. **Frame 65-195 (2.17-6.5s):** Hold. Card fully visible.
7. **Frame 195-240 (6.5-8s):** Card slides out to right — translateX(0)→translateX(200), opacity 1→0.

### Typography
- Stat number: Inter Black, 96px, #F59E0B (amber)
- Stat descriptor: Inter Medium, 28px, #CBD5E1
- Source: Inter Regular, 16px, #64748B (muted)
- Qualifier: Inter SemiBold, 20px, #3B82F6 (vibrant blue)

### Easing
- Card slide in: `spring({ damping: 15, stiffness: 180 })`
- Stat scale: `easeOutCubic`
- Text fades: `easeOutQuad`
- Card slide out: `easeInCubic`

## Narration Sync
> "More detailed prompts mean slower generation. More comprehensive tests mean longer feedback cycles."

The "10x" stat animates in as the narrator discusses the cost of detailed prompts. The qualifier appears to contrast structured vs. free-form approaches.

## Code Structure (Remotion)
```typescript
<Sequence from={PROMPT_STAT_START} durationInFrames={240}>
  <StatCalloutCard
    style={{
      transform: `translateX(${interpolate(frame, [0, 20, 195, 240], [200, 0, 0, 200])}px)`,
      opacity: interpolate(frame, [0, 20, 195, 240], [0, 1, 1, 0]),
    }}
  >
    {/* Frosted glass card */}
    <CardBackground blur={12} bgColor="rgba(15, 23, 42, 0.85)" />
    <AccentBar color="#F59E0B" />

    {/* Main stat */}
    <StatNumber
      value="10x"
      style={{
        color: '#F59E0B',
        transform: `scale(${interpolate(frame, [15, 35], [0.8, 1.0], { extrapolateRight: 'clamp' })})`,
        opacity: interpolate(frame, [15, 35], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
      }}
    />

    {/* Descriptor */}
    <StatDescriptor
      text="token reduction with structured prompts"
      opacity={interpolate(frame, [25, 40], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />

    {/* Source */}
    <SourceAttribution
      text="PDD Benchmark, 2025"
      opacity={interpolate(frame, [35, 50], [0, 0.7], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />

    {/* Qualifier */}
    <Qualifier
      text="vs. free-form instructions"
      color="#3B82F6"
      opacity={interpolate(frame, [45, 65], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
    />
  </StatCalloutCard>
</Sequence>
```

## Data Points
```json
{
  "stat": "10x",
  "descriptor": "token reduction with structured prompts",
  "source": "PDD Benchmark, 2025",
  "qualifier": "vs. free-form instructions",
  "stat_color": "#F59E0B",
  "qualifier_color": "#3B82F6",
  "card_position": {"x": 1080, "y": 340, "width": 760, "height": 340},
  "totalFrames": 240,
  "fps": 30
}
```

---
