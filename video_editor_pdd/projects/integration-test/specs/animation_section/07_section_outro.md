[title:]

# Section 1.7: Section Outro Card

**Tool:** Remotion
**Duration:** ~0.75s (22 frames @ 30fps)
**Timestamp:** 0:07 – 0:07

## Visual Description
A minimal outro card closes the Animation Section. A horizontal divider line contracts from full width to a small centered segment, drawing attention inward. A green checkmark draws itself in with a stroke animation directly above center. The word "Complete" fades in below the checkmark. After a brief hold, the entire composition fades to black, cleanly ending the section.

## Technical Specifications

### Canvas
- Resolution: 1280x720 (16:9)
- Background: Dark navy (#0B1120)
- No grid lines

### Chart/Visual Elements
- **Divider line:** Horizontal, 2px height, #FFFFFF at 40% opacity, y=330. Starts at 300px width, contracts to 80px width (centered at x=640).
- **Checkmark:** SVG path stroke animation, #22C55E (green), 40px bounding box, 3px stroke width, centered at (640, 340). Draws from 0% to 100% stroke-dashoffset.
- **"Complete" label:** Centered at (640, 400), white text
- **Fade overlay:** Full-canvas black rectangle, opacity 0→1 for final fade

### Animation Sequence
1. **Frame 0–5 (0–0.17s):** Divider line contracts from 300px→80px width, remaining centered. Opacity holds at 40%.
2. **Frame 5–12 (0.17–0.4s):** Checkmark stroke draws in — stroke-dashoffset transitions from full path length to 0. Appears to "write" the checkmark left-to-right then down-to-up.
3. **Frame 12–16 (0.4–0.53s):** "Complete" text fades in from opacity 0→1, with subtle translateY from +8px→0px.
4. **Frame 16–19 (0.53–0.63s):** Hold — all elements visible and static.
5. **Frame 19–22 (0.63–0.73s):** Full-canvas fade to black (overlay opacity 0→1).

### Typography
- Label: Inter, 20px, #FFFFFF, font-weight 400, text-align center, letter-spacing 1px

### Easing
- Divider contract: `easeInOutCubic`
- Checkmark draw: `easeInOutQuad`
- Label fade: `easeOutQuad`
- Fade to black: `easeInCubic`

## Narration Sync
> (No narration — section concludes over the tail end of the previous narration.)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={22}>
  <AbsoluteFill style={{ backgroundColor: "#0B1120" }}>
    <ContractingDivider
      width={interpolate(frame, [0, 5], [300, 80], { extrapolateRight: "clamp" })}
      color="rgba(255,255,255,0.4)"
      y={330}
    />
    <Sequence from={5}>
      <AnimatedCheckmark
        size={40}
        strokeWidth={3}
        color="#22C55E"
        progress={interpolate(frame, [0, 7], [0, 1], { extrapolateRight: "clamp" })}
      />
    </Sequence>
    <Sequence from={12}>
      <FadeInLabel
        text="Complete"
        fontSize={20}
        color="#FFFFFF"
      />
    </Sequence>
    {/* Fade to black */}
    <AbsoluteFill
      style={{
        backgroundColor: "#000000",
        opacity: interpolate(frame, [19, 22], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
      }}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "divider": {
    "startWidth": 300,
    "endWidth": 80,
    "height": 2,
    "y": 330,
    "color": "rgba(255,255,255,0.4)"
  },
  "checkmark": {
    "size": 40,
    "strokeWidth": 3,
    "color": "#22C55E"
  },
  "label": {
    "text": "Complete",
    "fontSize": 20,
    "color": "#FFFFFF"
  },
  "fadeToBlack": {
    "startFrame": 19,
    "endFrame": 22,
    "color": "#000000"
  }
}
```

---
