[split:Perception vs Reality] Developer Speed Perception Split Screen

# Section 1.9: Split Screen — Perceived Speed vs Actual Outcomes

**Tool:** Remotion
**Duration:** ~12s
**Timestamp:** 5:15 - 5:27

## Visual Description
A split-screen comparison that divides the frame vertically. The left half is labeled "PERCEPTION" with a green-tinted upward arrow and "+20% faster (self-reported)." The right half is labeled "REALITY" with a red-tinted downward arrow and "19% slower (measured)." A thin vertical divider separates the two halves with a subtle glow. The left side has a satisfied developer icon with a thumbs-up silhouette; the right side has a stopwatch icon showing actual time elapsed. The split screen slides in from both edges simultaneously, holds, then the divider dissolves and the "Reality" side expands to full width as emphasis.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Left panel: (0, 100) to (940, 980), semi-transparent dark backing
- Right panel: (980, 100) to (1920, 980), semi-transparent dark backing
- Divider: vertical line at x=960, 2px, glowing

### Chart/Visual Elements
- Left panel ("Perception"):
  - Background: rgba(34, 197, 94, 0.08) — faint green tint
  - Header: "PERCEPTION" in green (#22C55E)
  - Arrow: large upward chevron, #22C55E, 80px
  - Stat: "+20%" in large white text
  - Descriptor: "faster (self-reported)" in muted green
  - Icon: simplified happy-face/thumbs-up silhouette, #22C55E at 30% opacity
- Right panel ("Reality"):
  - Background: rgba(239, 68, 68, 0.08) — faint red tint
  - Header: "REALITY" in red (#EF4444)
  - Arrow: large downward chevron, #EF4444, 80px
  - Stat: "19%" in large white text
  - Descriptor: "slower (measured)" in muted red
  - Icon: simplified stopwatch silhouette, #EF4444 at 30% opacity
- Divider: 2px vertical line, white at 40% opacity, soft glow
- Source: "METR Study, 2024" — bottom center, spanning both panels

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Left panel slides in from left edge — translateX(-960)→translateX(0), opacity 0→1.
2. **Frame 0-25 (0-0.83s):** Right panel slides in from right edge — translateX(960)→translateX(0), opacity 0→1. (Simultaneous with left.)
3. **Frame 15-30 (0.5-1s):** Divider fades in — opacity 0→0.4, glow appears.
4. **Frame 25-45 (0.83-1.5s):** Left header "PERCEPTION" and arrow fade in.
5. **Frame 35-55 (1.17-1.83s):** Left stat "+20%" counter animates, descriptor appears.
6. **Frame 45-65 (1.5-2.17s):** Right header "REALITY" and arrow fade in.
7. **Frame 55-75 (1.83-2.5s):** Right stat "19%" counter animates, descriptor appears.
8. **Frame 70-90 (2.33-3s):** Source attribution fades in.
9. **Frame 90-300 (3-10s):** Hold.
10. **Frame 300-360 (10-12s):** Both panels slide out — left to left, right to right. Divider fades.

### Typography
- Headers: Inter Black, 28px, uppercase, letter-spacing 0.15em
  - Left: #22C55E
  - Right: #EF4444
- Stat numbers: Inter Black, 96px, #FFFFFF
- Descriptors: Inter Medium, 24px
  - Left: #86EFAC (muted green)
  - Right: #FCA5A5 (muted red)
- Source: Inter Regular, 16px, #64748B

### Easing
- Panel slides: `spring({ damping: 16, stiffness: 160 })`
- Text fades: `easeOutQuad`
- Counter animate: `easeOutCubic`
- Panel slide out: `easeInCubic`

## Narration Sync
> "Small codebases — AI transforms. Large codebases — developers are 19 percent slower but perceive themselves 20 percent faster."

Left "Perception" panel appears as "perceive themselves 20 percent faster" is spoken. Right "Reality" panel emphasizes on "19 percent slower."

## Code Structure (Remotion)
```typescript
<Sequence from={SPLIT_START} durationInFrames={360}>
  <AbsoluteFill>
    {/* Left panel — Perception */}
    <SplitPanel
      side="left"
      style={{
        transform: `translateX(${interpolate(frame, [0, 25, 300, 360], [-960, 0, 0, -960])}px)`,
        opacity: interpolate(frame, [0, 25, 300, 360], [0, 1, 1, 0]),
      }}
    >
      <PanelHeader text="PERCEPTION" color="#22C55E" />
      <ArrowIcon direction="up" color="#22C55E" size={80} />
      <StatNumber value={20} prefix="+" suffix="%" fontSize={96} />
      <StatDescriptor text="faster (self-reported)" color="#86EFAC" />
    </SplitPanel>

    {/* Divider */}
    <VerticalDivider
      opacity={interpolate(frame, [15, 30, 300, 360], [0, 0.4, 0.4, 0])}
      glowColor="#FFFFFF"
    />

    {/* Right panel — Reality */}
    <SplitPanel
      side="right"
      style={{
        transform: `translateX(${interpolate(frame, [0, 25, 300, 360], [960, 0, 0, 960])}px)`,
        opacity: interpolate(frame, [0, 25, 300, 360], [0, 1, 1, 0]),
      }}
    >
      <PanelHeader text="REALITY" color="#EF4444" />
      <ArrowIcon direction="down" color="#EF4444" size={80} />
      <StatNumber value={19} suffix="%" fontSize={96} />
      <StatDescriptor text="slower (measured)" color="#FCA5A5" />
    </SplitPanel>

    {/* Source */}
    <SourceAttribution
      text="METR Study, 2024"
      opacity={interpolate(frame, [70, 90, 300, 360], [0, 1, 1, 0])}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "perception": {
    "stat": "+20%",
    "descriptor": "faster (self-reported)",
    "color": "#22C55E",
    "direction": "up"
  },
  "reality": {
    "stat": "19%",
    "descriptor": "slower (measured)",
    "color": "#EF4444",
    "direction": "down"
  },
  "source": "METR Study, 2024",
  "totalFrames": 360,
  "fps": 30
}
```

---
