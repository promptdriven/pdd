[split:]

# Section 1.7: Before / After Split Summary

**Tool:** Remotion
**Duration:** ~2.4s (73 frames)
**Timestamp:** 0:05 - 0:07

## Visual Description
A before/after split-screen view with a slowly animating vertical divider. The left side displays "Before" in large bold text on a red background, and the right side displays "After" on the same red background. A vertical white divider line slides gently from x=640 to x=720 over the duration, creating a subtle reveal effect. A "Split Summary" heading anchors the top-left corner.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Solid #FF0000 (red) on both halves
- No grid lines

### Chart/Visual Elements
- **Left half:**
  - Background: #FF0000
  - Text: "Before" centered in left half, color #E2E8F0, 46px, bold
  - Occupies full height, width determined by divider position

- **Right half:**
  - Background: #FF0000
  - Text: "After" centered in right half, color #E2E8F0, 46px, bold
  - Occupies full height, width determined by divider position

- **Animated divider:** Vertical line, 6px wide, color #FF0000, animates from x=640 to x=720
- **Section heading:** "Split Summary" at (64, 64), color #E2E8F0, 54px, bold

### Animation Sequence
1. **Frame 0-90 (0-3.0s):** Divider slowly slides from x=640 to x=720 (80px travel over 90 frames, clamped at frame 73)
2. **Frame 0-73 (0-2.43s):** "Before" and "After" labels remain stationary, centered in their respective halves
3. **Frame 0 (static):** "Split Summary" heading visible immediately, no animation

### Typography
- Heading: sans-serif, 54px, bold (700), #E2E8F0
- Panel labels: sans-serif, 46px, bold (700), #E2E8F0

### Easing
- Divider slide: `linear` (clamped extrapolation, constant speed)

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

This visual appears during the final portion of segment 2 (5.0s-6.0s) and continues past the narration into the section tail. The simple split-screen demonstrates a compositional layout achievable purely through Remotion code.

## Code Structure (Remotion)
```typescript
<Sequence from={146} durationInFrames={73}>
  <AbsoluteFill style={{ backgroundColor: '#FF0000', fontFamily: 'sans-serif', color: '#E2E8F0' }}>
    {/* Two-panel layout */}
    <div style={{ position: 'absolute', inset: 0, display: 'flex' }}>
      <div style={{ flex: 1, display: 'flex', justifyContent: 'center', alignItems: 'center' }}>
        <div style={{ fontSize: 46, fontWeight: 700 }}>Before</div>
      </div>
      <div style={{ flex: 1, display: 'flex', justifyContent: 'center', alignItems: 'center' }}>
        <div style={{ fontSize: 46, fontWeight: 700 }}>After</div>
      </div>
    </div>

    {/* Animated vertical divider */}
    <AnimatedDivider
      startX={640}
      endX={720}
      width={6}
      color="#FF0000"
      durationFrames={90}
    />

    {/* Section heading */}
    <div style={{ position: 'absolute', top: 64, left: 64, fontSize: 54, fontWeight: 700 }}>
      Split Summary
    </div>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "divider": {
    "startX": 640,
    "endX": 720,
    "width": 6,
    "animationFrames": 90
  },
  "panels": {
    "left": { "label": "Before", "background": "#FF0000" },
    "right": { "label": "After", "background": "#FF0000" }
  },
  "heading": "Split Summary"
}
```

---
