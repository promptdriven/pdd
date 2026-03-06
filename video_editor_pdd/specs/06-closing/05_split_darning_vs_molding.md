[split:Darning vs Molding] Darning Economics vs Molding Economics Split Screen

# Section 6.4: Split Screen — Darning vs Molding

**Tool:** Remotion
**Duration:** ~8s
**Timestamp:** 0:09 - 0:17

## Visual Description
A split-screen comparison that divides the frame vertically, delivering the closing argument's central metaphor. The left half is labeled "DARNING" with a red-tinted thread-and-needle icon — representing patching and repair. The right half is labeled "MOLDING" with a green-tinted cast-mold icon — representing generation from a template. Each side has a simple cost trajectory: left shows "Cost rises over time" with a red exponential curve, right shows "Cost stays flat" with a flat green line. Below each trajectory, a single outcome word appears in large text: "FRAGILE" (left, red) and "RESILIENT" (right, green). A thin glowing vertical divider separates the halves. The panels slide in simultaneously, hold for emphasis, then dissolve out.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Left panel: (0, 100) to (940, 980), semi-transparent dark backing
- Right panel: (980, 100) to (1920, 980), semi-transparent dark backing
- Divider: vertical line at x=960, 2px, glowing

### Chart/Visual Elements
- Left panel ("Darning"):
  - Background: rgba(239, 68, 68, 0.06) — faint red tint
  - Header: "DARNING" in red (#EF4444)
  - Icon: thread-and-needle with criss-cross stitching, #EF4444 at 30% opacity, 90px
  - Cost curve: exponential rise from left to right, #EF4444, 3px stroke
  - Curve label: "Cost rises over time" in #94A3B8
  - Outcome: "FRAGILE" in #EF4444, large centered text
- Right panel ("Molding"):
  - Background: rgba(34, 197, 94, 0.06) — faint green tint
  - Header: "MOLDING" in green (#22C55E)
  - Icon: cast-mold with clean edges, #22C55E at 30% opacity, 90px
  - Cost curve: flat horizontal line, #22C55E, 3px stroke
  - Curve label: "Cost stays flat" in #94A3B8
  - Outcome: "RESILIENT" in #22C55E, large centered text
- Divider: 2px vertical line, white at 40% opacity, soft glow
- Footer: "Stop darning. Start molding." — centered across both panels, #FFFFFF, bold

### Animation Sequence
1. **Frame 0-22 (0-0.73s):** Left panel slides in from left — translateX(-960)→translateX(0), opacity 0→1.
2. **Frame 0-22 (0-0.73s):** Right panel slides in from right — translateX(960)→translateX(0), opacity 0→1. (Simultaneous.)
3. **Frame 12-25 (0.4-0.83s):** Divider fades in — opacity 0→0.4.
4. **Frame 22-38 (0.73-1.27s):** Left header "DARNING" and icon fade in.
5. **Frame 30-55 (1-1.83s):** Left cost curve draws from left to right (path animation).
6. **Frame 38-54 (1.27-1.8s):** Right header "MOLDING" and icon fade in.
7. **Frame 46-65 (1.53-2.17s):** Right flat line draws from left to right.
8. **Frame 60-78 (2-2.6s):** Outcome words "FRAGILE" and "RESILIENT" scale up from 0.7→1.0, opacity 0→1.
9. **Frame 75-95 (2.5-3.17s):** Footer "Stop darning. Start molding." fades in — opacity 0→1.
10. **Frame 95-195 (3.17-6.5s):** Hold.
11. **Frame 195-240 (6.5-8s):** Both panels dissolve out — opacity 1→0.

### Typography
- Headers: Inter Black, 28px, uppercase, letter-spacing 0.15em
  - Left: #EF4444
  - Right: #22C55E
- Curve labels: Inter Medium, 18px, #94A3B8
- Outcome text: Inter Black, 48px, uppercase
  - Left: #EF4444
  - Right: #22C55E
- Footer: Inter Bold, 28px, #FFFFFF

### Easing
- Panel slides: `spring({ damping: 16, stiffness: 160 })`
- Curve draw: `easeInOutCubic`
- Outcome scale: `easeOutBack`
- Text fades: `easeOutQuad`
- Panel dissolve: `easeInCubic`

## Narration Sync
> "Stop darning. Start molding."

Left "Darning" panel appears as the closing metaphor is set up. Right "Molding" panel appears simultaneously. Footer text "Stop darning. Start molding." lands precisely on the narration beat. The split holds through the transition to the developer callback.

## Code Structure (Remotion)
```typescript
<Sequence from={SPLIT_START} durationInFrames={240}>
  <AbsoluteFill>
    {/* Left panel — Darning */}
    <SplitPanel
      side="left"
      style={{
        transform: `translateX(${interpolate(frame, [0, 22, 195, 240], [-960, 0, 0, -960])}px)`,
        opacity: interpolate(frame, [0, 22, 195, 240], [0, 1, 1, 0]),
      }}
    >
      <PanelHeader text="DARNING" color="#EF4444" />
      <NeedleIcon color="#EF4444" size={90} opacity={0.3} />
      <CostCurve type="exponential" color="#EF4444" strokeWidth={3} />
      <CurveLabel text="Cost rises over time" />
      <OutcomeWord text="FRAGILE" color="#EF4444" />
    </SplitPanel>

    {/* Divider */}
    <VerticalDivider
      opacity={interpolate(frame, [12, 25, 195, 240], [0, 0.4, 0.4, 0])}
      glowColor="#FFFFFF"
    />

    {/* Right panel — Molding */}
    <SplitPanel
      side="right"
      style={{
        transform: `translateX(${interpolate(frame, [0, 22, 195, 240], [960, 0, 0, 960])}px)`,
        opacity: interpolate(frame, [0, 22, 195, 240], [0, 1, 1, 0]),
      }}
    >
      <PanelHeader text="MOLDING" color="#22C55E" />
      <MoldIcon color="#22C55E" size={90} opacity={0.3} />
      <CostCurve type="flat" color="#22C55E" strokeWidth={3} />
      <CurveLabel text="Cost stays flat" />
      <OutcomeWord text="RESILIENT" color="#22C55E" />
    </SplitPanel>

    {/* Footer */}
    <FooterText
      text="Stop darning. Start molding."
      style={{
        opacity: interpolate(frame, [75, 95, 195, 240], [0, 1, 1, 0]),
        fontWeight: 'bold',
        fontSize: 28,
        color: '#FFFFFF',
      }}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "darning": {
    "header": "DARNING",
    "icon": "needle_thread",
    "curve_type": "exponential",
    "curve_label": "Cost rises over time",
    "outcome": "FRAGILE",
    "color": "#EF4444"
  },
  "molding": {
    "header": "MOLDING",
    "icon": "cast_mold",
    "curve_type": "flat",
    "curve_label": "Cost stays flat",
    "outcome": "RESILIENT",
    "color": "#22C55E"
  },
  "footer": "Stop darning. Start molding.",
  "totalFrames": 240,
  "fps": 30
}
```

---
