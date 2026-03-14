[split:]

# Section 1.9: Split Summary

**Tool:** Remotion
**Duration:** ~0.7s (22 frames @ 30fps)
**Timestamp:** 0:07 - 0:08

## Visual Description
A before/after split-screen layout serves as the section's closing summary. A "Before" panel on the left and an "After" panel on the right are separated by a glowing cyan vertical divider line. The divider slowly drifts rightward across the screen, subtly animating the boundary between the two halves. A "Split Summary" title label sits in the top-left corner.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Near-black (#020617) — base layer behind split panels

### Chart/Visual Elements
- **Left panel:** Full height, flex 1, background #0F172A (dark navy)
  - "Before" text: centered within panel
- **Right panel:** Full height, flex 1, background #111827 (slightly lighter navy)
  - "After" text: centered within panel
- **Vertical divider:** 6px wide, cyan (#38BDF8), full height, positioned absolutely
  - Start position: x=640
  - End position: x=720 (drifts 80px to the right)
- **"Split Summary" label:** Top-left corner at (64, 64)

### Animation Sequence
1. **Frame 0-90 (0-3.0s):** Divider slides — x position interpolates from 640 to 720 (slow, continuous drift)
2. **Frame 0-90:** All text and panels are static — no fade-in, visible from frame 0

(Note: Visual is time-scaled via SlotScaledSequence to fit its allocated slot; intrinsic 90 frames compressed to ~22 actual frames)

### Typography
- "Before" / "After" text: sans-serif 700, 46px, light slate (#E2E8F0)
- "Split Summary" label: sans-serif 700, 54px, light slate (#E2E8F0)

### Easing
- Divider slide: `linear` (slow constant drift)

## Narration Sync
> (Post-narration visual — section wrap-up beat)

## Code Structure (Remotion)
```typescript
<AbsoluteFill style={{ backgroundColor: '#020617', fontFamily: 'sans-serif', color: '#E2E8F0' }}>
  <div style={{ position: 'absolute', inset: 0, display: 'flex' }}>
    <div style={{ flex: 1, backgroundColor: '#0F172A', display: 'flex', justifyContent: 'center', alignItems: 'center' }}>
      <div style={{ fontSize: 46, fontWeight: 700 }}>Before</div>
    </div>
    <div style={{ flex: 1, backgroundColor: '#111827', display: 'flex', justifyContent: 'center', alignItems: 'center' }}>
      <div style={{ fontSize: 46, fontWeight: 700 }}>After</div>
    </div>
  </div>
  <div style={{ position: 'absolute', top: 0, bottom: 0, left: dividerX, width: 6, backgroundColor: '#38BDF8' }} />
  <div style={{ position: 'absolute', top: 64, left: 64, fontSize: 54, fontWeight: 700 }}>
    Split Summary
  </div>
</AbsoluteFill>
```

## Data Points
```json
{
  "divider": {
    "startX": 640,
    "endX": 720,
    "width": 6,
    "color": "#38BDF8"
  },
  "panels": {
    "left": { "background": "#0F172A", "label": "Before" },
    "right": { "background": "#111827", "label": "After" }
  }
}
```

---
