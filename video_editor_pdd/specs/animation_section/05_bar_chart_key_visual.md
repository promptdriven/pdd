[Remotion]

# Section 1.5: Animated Bar Chart — Key Visual

**Tool:** Remotion
**Duration:** ~2.5s (75 frames)
**Timestamp:** 0:06 - 0:08

## Visual Description
Four vertical bars rise sequentially from the bottom of the screen against a dark slate background. The bars alternate between sky-blue and emerald-green, each growing to a different height representing relative data values. Percentage labels fade in above each bar after it finishes growing. A bold "Key Visual" heading anchors the top-left corner. The staggered growth creates a cascading wave effect that draws the eye left-to-right, demonstrating a classic Remotion data visualization.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (slate-950)
- No grid lines

### Chart/Visual Elements
- **Bar 1:** 120px wide, max height 126px (35% of 360px), border-radius 24px, color #38BDF8 (sky-400)
- **Bar 2:** 120px wide, max height 198px (55% of 360px), border-radius 24px, color #22C55E (green-500)
- **Bar 3:** 120px wide, max height 288px (80% of 360px), border-radius 24px, color #38BDF8 (sky-400)
- **Bar 4:** 120px wide, max height 216px (60% of 360px), border-radius 24px, color #22C55E (green-500)
- **Bar spacing:** 36px gap between bars, group centered horizontally, aligned to Y baseline = 750px
- **Value labels:** "35%", "55%", "80%", "60%" above each bar, 24px Inter bold, #E2E8F0
- **Heading:** "Key Visual" at (72, 72), 52px Inter bold, #F8FAFC
- **Shadow:** Each bar has `boxShadow: 0 12px 40px rgba(15, 23, 42, 0.45)`

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Bar 1 grows from height 0 to 126px with spring overshoot
2. **Frame 10-30 (0.33-1.0s):** Bar 2 grows from height 0 to 198px — 10-frame stagger
3. **Frame 20-40 (0.67-1.33s):** Bar 3 grows from height 0 to 288px — 10-frame stagger
4. **Frame 30-50 (1.0-1.67s):** Bar 4 grows from height 0 to 216px — 10-frame stagger
5. **Frame 50-65 (1.67-2.17s):** Value labels fade in above each bar (staggered by 5 frames)
6. **Frame 65-75 (2.17-2.5s):** Hold final state

### Typography
- Heading: Inter, 52px, bold (weight 700), #F8FAFC
- Value labels: Inter, 24px, bold (weight 700), #E2E8F0

### Easing
- Bar growth: `spring({ damping: 12, stiffness: 100 })` (Remotion spring)
- Label fade: `easeOutQuad`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

Plays during the middle of Segment 2 (6.0s-8.0s). The bar chart demonstrates a pure Remotion data visualization — no video footage needed.

## Code Structure (Remotion)
```typescript
<Sequence from={180} durationInFrames={75}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A', justifyContent: 'center', alignItems: 'center' }}>
    <div style={{ position: 'absolute', top: 72, left: 72, color: '#F8FAFC', fontSize: 52, fontWeight: 700 }}>
      Key Visual
    </div>
    <div style={{ display: 'flex', gap: 36, alignItems: 'flex-end', height: 420 }}>
      {BARS.map((bar, index) => (
        <AnimatedBar
          key={index}
          targetHeight={360 * bar.value}
          delay={index * 10}
          color={bar.color}
          label={`${Math.round(bar.value * 100)}%`}
          labelDelay={50 + index * 5}
        />
      ))}
    </div>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "bars": [
    { "label": "Metric A", "value": 0.35, "color": "#38BDF8" },
    { "label": "Metric B", "value": 0.55, "color": "#22C55E" },
    { "label": "Metric C", "value": 0.80, "color": "#38BDF8" },
    { "label": "Metric D", "value": 0.60, "color": "#22C55E" }
  ],
  "barWidth": 120,
  "maxBarHeight": 360,
  "gap": 36,
  "staggerDelayFrames": 10
}
```

---
