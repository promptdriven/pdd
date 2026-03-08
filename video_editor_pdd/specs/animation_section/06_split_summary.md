[split:]

# Section 1.6: Split Summary — Before / After

**Tool:** Remotion
**Duration:** ~3s (90 frames)
**Timestamp:** 0:07 - 0:10

## Visual Description
A split-screen comparison layout divides the canvas into two halves with an animated vertical divider. The left side shows "Before" (a static placeholder representing raw footage or no animation) with a muted dark background. The right side shows "After" (animated, vibrant content representing the Remotion-processed result) with a brighter background. The divider slides slightly right from center, revealing more of the "After" panel, emphasizing the transformation. A bold heading "Split Summary" anchors the top-left.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (slate-950) base
- No grid lines

### Chart/Visual Elements
- **Left panel ("Before"):** Background #1E293B (slate-800), fills left half of screen
  - Center text: "Before" at 46px, Inter bold, #E2E8F0
  - Faint static noise texture at 3% opacity
- **Right panel ("After"):** Background #0F4C81 (dark teal-blue), fills right half
  - Center text: "After" at 46px, Inter bold, #E2E8F0
  - Subtle animated gradient shift (hue rotation 0-15deg over duration)
- **Vertical divider:** 6px wide bar, full height, color #3B82F6 (blue-500)
  - Initial position: X=640 (left of center)
  - Final position: X=720 (right of center, biased toward "After")
  - Glow: 20px blur, #3B82F6 at 40% opacity
- **Heading:** "Split Summary" at position (64, 64), 54px Inter bold, #E2E8F0

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Both panels fade in simultaneously from opacity 0 to 1
2. **Frame 0-90 (0-3.0s):** Divider slides from X=640 to X=720 with slow easing, revealing more "After" content
3. **Frame 15-30 (0.5-1.0s):** "Before" text fades in on left panel
4. **Frame 20-35 (0.67-1.17s):** "After" text fades in on right panel
5. **Frame 0-90 (continuous):** Right panel background gradient slowly shifts hue
6. **Frame 60-90 (2.0-3.0s):** Divider glow pulses once (opacity 40% → 70% → 40%)

### Typography
- Heading: Inter, 54px, bold (weight 700), #E2E8F0
- Panel labels: Inter, 46px, bold (weight 700), #E2E8F0

### Easing
- Panel fade: `easeOutCubic`
- Divider slide: `easeInOutCubic`
- Text fade: `easeOutQuad`
- Glow pulse: `easeInOutSine`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

This visual spans the latter half of the section (Segment 2, 3.0s-6.0s into the hold period). The before/after split emphasizes the contrast between static content and Remotion-animated output.

## Code Structure (Remotion)
```typescript
<Sequence from={225} durationInFrames={90}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    <div style={{ position: 'absolute', inset: 0, display: 'flex' }}>
      <AbsoluteFill style={{ flex: 1, backgroundColor: '#1E293B' }}>
        <NoiseOverlay opacity={0.03} />
        <Sequence from={15}>
          <FadeInText text="Before" size={46} />
        </Sequence>
      </AbsoluteFill>
      <AbsoluteFill style={{ flex: 1, backgroundColor: '#0F4C81' }}>
        <AnimatedGradient hueRange={[0, 15]} />
        <Sequence from={20}>
          <FadeInText text="After" size={46} />
        </Sequence>
      </AbsoluteFill>
    </div>
    <AnimatedDivider fromX={640} toX={720} width={6} color="#3B82F6" glowRadius={20} />
    <div style={{ position: 'absolute', top: 64, left: 64, fontSize: 54, fontWeight: 700, color: '#E2E8F0' }}>
      Split Summary
    </div>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "panels": [
    { "label": "Before", "background": "#1E293B", "side": "left" },
    { "label": "After", "background": "#0F4C81", "side": "right" }
  ],
  "divider": {
    "startX": 640,
    "endX": 720,
    "width": 6,
    "color": "#3B82F6"
  }
}
```

---
