[split:Patching vs PDD] Patching Approach vs PDD Generation Approach Split Screen

# Section 5.7: Split Screen — Patching vs PDD

**Tool:** Remotion
**Duration:** ~12s
**Timestamp:** 1:15 - 1:27

## Visual Description
A split-screen comparison that divides the frame vertically. The left half is labeled "PATCHING" with a red-tinted code diff icon showing layered edit marks — representing the traditional approach of modifying existing code. The right half is labeled "GENERATION" with a green-tinted refresh-cycle icon showing a clean loop — representing the PDD approach of regenerating fresh code. Each side has a timeline showing what happens over 12 months: left shows "Debt accumulates" with a rising red bar, right shows "Debt resets" with a flat green line. A thin vertical divider separates the two halves with a subtle glow. Below each timeline, outcome labels appear: "Fragile, slow, expensive" (left, red) and "Fresh, fast, compounding" (right, green). The panels slide in simultaneously from both edges, hold, then slide out.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Left panel: (0, 100) to (940, 980), semi-transparent dark backing
- Right panel: (980, 100) to (1920, 980), semi-transparent dark backing
- Divider: vertical line at x=960, 2px, glowing

### Chart/Visual Elements
- Left panel ("Patching"):
  - Background: rgba(239, 68, 68, 0.06) — faint red tint
  - Header: "PATCHING" in red (#EF4444)
  - Icon: code diff with layered edit strikethroughs, #EF4444 at 30% opacity, 100px
  - Mini timeline: 12-month bar chart, bars rising from left to right, #EF4444
  - Timeline label: "Debt accumulates" in #94A3B8
  - Outcome: "Fragile, slow, expensive" in #EF4444
- Right panel ("Generation"):
  - Background: rgba(34, 197, 94, 0.06) — faint green tint
  - Header: "GENERATION" in green (#22C55E)
  - Icon: refresh cycle loop with checkmark, #22C55E at 30% opacity, 100px
  - Mini timeline: 12-month flat line with sawtooth resets, #22C55E
  - Timeline label: "Debt resets each cycle" in #94A3B8
  - Outcome: "Fresh, fast, compounding" in #22C55E
- Divider: 2px vertical line, white at 40% opacity, soft glow
- Footer: "The approach you choose compounds over time" — centered across both panels, #CBD5E1

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Left panel slides in from left edge — translateX(-960)→translateX(0), opacity 0→1.
2. **Frame 0-25 (0-0.83s):** Right panel slides in from right edge — translateX(960)→translateX(0), opacity 0→1. (Simultaneous.)
3. **Frame 15-30 (0.5-1s):** Divider fades in — opacity 0→0.4, glow appears.
4. **Frame 25-45 (0.83-1.5s):** Left header "PATCHING" and icon fade in.
5. **Frame 35-55 (1.17-1.83s):** Left mini timeline bars animate upward sequentially.
6. **Frame 45-65 (1.5-2.17s):** Right header "GENERATION" and icon fade in.
7. **Frame 55-75 (1.83-2.5s):** Right mini timeline draws flat line with resets.
8. **Frame 70-90 (2.33-3s):** Outcome labels fade in on both sides.
9. **Frame 85-105 (2.83-3.5s):** Footer text fades in.
10. **Frame 105-300 (3.5-10s):** Hold.
11. **Frame 300-360 (10-12s):** Both panels slide out — left to left, right to right. Divider fades.

### Typography
- Headers: Inter Black, 28px, uppercase, letter-spacing 0.15em
  - Left: #EF4444
  - Right: #22C55E
- Timeline labels: Inter Medium, 18px, #94A3B8
- Outcome text: Inter Bold, 24px
  - Left: #EF4444
  - Right: #22C55E
- Footer: Inter SemiBold, 22px, #CBD5E1

### Easing
- Panel slides: `spring({ damping: 16, stiffness: 160 })`
- Timeline bar animation: `easeOutQuad` (staggered 3 frames per bar)
- Text fades: `easeOutQuad`
- Panel slide out: `easeInCubic`

## Narration Sync
> "Your grandmother didn't need a study to figure this out. When the economics flip, you stop darning. You start buying new socks."

Left "Patching" panel appears as the darning metaphor is introduced. Right "Generation" panel appears as "buying new socks" is spoken. Footer emphasizes the compounding nature of the choice.

## Code Structure (Remotion)
```typescript
<Sequence from={SPLIT_START} durationInFrames={360}>
  <AbsoluteFill>
    {/* Left panel — Patching */}
    <SplitPanel
      side="left"
      style={{
        transform: `translateX(${interpolate(frame, [0, 25, 300, 360], [-960, 0, 0, -960])}px)`,
        opacity: interpolate(frame, [0, 25, 300, 360], [0, 1, 1, 0]),
      }}
    >
      <PanelHeader text="PATCHING" color="#EF4444" />
      <DiffIcon color="#EF4444" size={100} opacity={0.3} />
      <MiniTimeline type="rising_bars" color="#EF4444" months={12} />
      <TimelineLabel text="Debt accumulates" />
      <OutcomeText text="Fragile, slow, expensive" color="#EF4444" />
    </SplitPanel>

    {/* Divider */}
    <VerticalDivider
      opacity={interpolate(frame, [15, 30, 300, 360], [0, 0.4, 0.4, 0])}
      glowColor="#FFFFFF"
    />

    {/* Right panel — Generation */}
    <SplitPanel
      side="right"
      style={{
        transform: `translateX(${interpolate(frame, [0, 25, 300, 360], [960, 0, 0, 960])}px)`,
        opacity: interpolate(frame, [0, 25, 300, 360], [0, 1, 1, 0]),
      }}
    >
      <PanelHeader text="GENERATION" color="#22C55E" />
      <RefreshCycleIcon color="#22C55E" size={100} opacity={0.3} />
      <MiniTimeline type="flat_sawtooth" color="#22C55E" months={12} />
      <TimelineLabel text="Debt resets each cycle" />
      <OutcomeText text="Fresh, fast, compounding" color="#22C55E" />
    </SplitPanel>

    {/* Footer */}
    <FooterText
      text="The approach you choose compounds over time"
      opacity={interpolate(frame, [85, 105, 300, 360], [0, 1, 1, 0])}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "patching": {
    "header": "PATCHING",
    "icon": "code_diff",
    "timeline_type": "rising_bars",
    "timeline_label": "Debt accumulates",
    "outcome": "Fragile, slow, expensive",
    "color": "#EF4444"
  },
  "generation": {
    "header": "GENERATION",
    "icon": "refresh_cycle",
    "timeline_type": "flat_sawtooth",
    "timeline_label": "Debt resets each cycle",
    "outcome": "Fresh, fast, compounding",
    "color": "#22C55E"
  },
  "footer": "The approach you choose compounds over time",
  "totalFrames": 360,
  "fps": 30
}
```

---
