[Remotion]

# Section 1.8: Key Visual — Bar Chart

**Tool:** Remotion
**Duration:** ~0.8s (24 frames @ 30fps)
**Timestamp:** 0:06 - 0:07

## Visual Description
A four-bar animated bar chart rises from the bottom of the screen. Each bar grows upward with staggered timing, creating a cascading reveal effect. The bars alternate between cyan and green colors. A "Key Visual" label sits in the top-left corner. The chart communicates a simple data comparison without axis labels — purely visual impact.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep navy (#0A1628), solid fill

### Chart/Visual Elements
- **Bar container:** Centered on screen, flexbox row with 36px gap, 420px max height, bottom-aligned
- **Bar 1:** Width 120px, max height 126px (35% of 360), cyan (#38BDF8), border-radius 24px
- **Bar 2:** Width 120px, max height 198px (55% of 360), green (#22C55E), border-radius 24px
- **Bar 3:** Width 120px, max height 288px (80% of 360), cyan (#38BDF8), border-radius 24px
- **Bar 4:** Width 120px, max height 216px (60% of 360), green (#22C55E), border-radius 24px
- **Box shadow:** Each bar has `0 12px 40px rgba(15, 23, 42, 0.45)` for depth
- **"Key Visual" label:** Top-left corner at (72, 72)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Bar 1 grows from height 0 to target height (126px)
2. **Frame 10-30 (0.33-1.0s):** Bar 2 grows from height 0 to target height (198px) — staggered 10 frames after Bar 1
3. **Frame 20-40 (0.67-1.33s):** Bar 3 grows from height 0 to target height (288px) — staggered 10 frames after Bar 2
4. **Frame 30-50 (1.0-1.67s):** Bar 4 grows from height 0 to target height (216px) — staggered 10 frames after Bar 3

(Note: Visual is time-scaled via SlotScaledSequence to fit its allocated slot in the section timeline)

### Typography
- "Key Visual" label: sans-serif 700, 52px, white (#F8FAFC)

### Easing
- Bar growth: `linear` (interpolate clamps at endpoints)

## Narration Sync
> (Tail end of narration — visual reinforcement after spoken content)

## Code Structure (Remotion)
```typescript
<AbsoluteFill style={{ backgroundColor: '#0A1628' }}>
  <div style={{ position: 'absolute', top: 72, left: 72, color: '#F8FAFC', fontSize: 52, fontWeight: 700 }}>
    Key Visual
  </div>
  <div style={{ display: 'flex', gap: 36, alignItems: 'flex-end', height: 420 }}>
    {BARS.map((value, index) => {
      const scale = interpolate(frame, [0, 20 + index * 10, 90 + index * 10], [0, value, value], { extrapolateRight: 'clamp' });
      return (
        <div key={index} style={{
          width: 120,
          height: 360 * scale,
          borderRadius: 24,
          background: index % 2 === 0 ? '#38BDF8' : '#22C55E',
          boxShadow: '0 12px 40px rgba(15, 23, 42, 0.45)',
        }} />
      );
    })}
  </div>
</AbsoluteFill>
```

## Data Points
```json
{
  "bars": [
    { "value": 0.35, "maxHeight": 126, "color": "#38BDF8" },
    { "value": 0.55, "maxHeight": 198, "color": "#22C55E" },
    { "value": 0.80, "maxHeight": 288, "color": "#38BDF8" },
    { "value": 0.60, "maxHeight": 216, "color": "#22C55E" }
  ],
  "barWidth": 120,
  "barGap": 36,
  "containerHeight": 420,
  "barBaseHeight": 360
}
```

---
