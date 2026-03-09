[Remotion]

# Section 1.5: Animation Timeline Diagram

**Tool:** Remotion
**Duration:** ~5s
**Timestamp:** 0:18 - 0:23

## Visual Description
A horizontal timeline diagram visualizing the animation sequence of the entire section. The timeline is a thin horizontal track spanning most of the screen width, with labeled milestone markers at key moments: "Title Card", "Circle Pulse", "Morph", "Slide Right", and "Showcase". Each marker is a small vertical tick with a colored dot and label. A glowing playhead sweeps left to right across the timeline, illuminating each milestone as it passes.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Near-black (#090E1A)
- Grid lines: None

### Chart/Visual Elements
- Timeline track: Horizontal line from x=160 to x=1760, y=540, 2px solid #334155 (slate-700)
- Milestones (5 total), evenly spaced along track:
  1. x=260: Dot #A78BFA (violet-400), label "Title Card"
  2. x=560: Dot #3B82F6 (blue-500), label "Circle Pulse"
  3. x=860: Dot #F59E0B (amber-500), label "Morph"
  4. x=1160: Dot #22C55E (green-500), label "Slide Right"
  5. x=1460: Dot #EC4899 (pink-500), label "Showcase"
- Each milestone: 12px filled circle, 24px vertical tick (1px #475569), label below
- Playhead: 16px circle with outer glow (box-shadow 0 0 20px), color #FFFFFF, travels along the track line

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Timeline track draws in from left to right (stroke-dashoffset animation).
2. **Frame 20-40 (0.67-1.33s):** Milestone dots and ticks pop in sequentially, staggered by 4 frames each. Labels fade in with their respective dots.
3. **Frame 40-120 (1.33-4.0s):** Playhead sweeps from x=160 to x=1760 at a constant rate. As it passes each milestone dot, the dot briefly scales to 1.5x and its glow intensifies (opacity 40% → 80%) for 6 frames before settling back.
4. **Frame 120-150 (4.0-5.0s):** Playhead reaches end and fades out. All milestones remain at full brightness. Subtle shimmer on the track (opacity oscillation 80%-100%).

### Typography
- Milestone labels: Inter Regular, 18px, #CBD5E1 (slate-300)
- No title text — the timeline is self-describing

### Easing
- Track draw: `easeInOutQuad`
- Milestone pop-in: `easeOutBack`
- Playhead sweep: `linear`
- Milestone highlight pulse: `easeOutQuad`

## Narration Sync
> (Bridge visual — no direct narration; provides pacing between narrated segments)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#090E1A' }}>
    <Sequence from={0} durationInFrames={20}>
      <DrawLine from={[160, 540]} to={[1760, 540]} color="#334155" />
    </Sequence>
    <Sequence from={20} durationInFrames={20}>
      {milestones.map((m, i) => (
        <Sequence key={m.label} from={i * 4}>
          <MilestoneDot x={m.x} y={540} color={m.color} label={m.label} />
        </Sequence>
      ))}
    </Sequence>
    <Sequence from={40} durationInFrames={80}>
      <Playhead fromX={160} toX={1760} y={540} milestones={milestones} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "milestones": [
    { "x": 260, "color": "#A78BFA", "label": "Title Card" },
    { "x": 560, "color": "#3B82F6", "label": "Circle Pulse" },
    { "x": 860, "color": "#F59E0B", "label": "Morph" },
    { "x": 1160, "color": "#22C55E", "label": "Slide Right" },
    { "x": 1460, "color": "#EC4899", "label": "Showcase" }
  ],
  "track": {
    "startX": 160,
    "endX": 1760,
    "y": 540
  }
}
```

---
