[split:question_vs_answer] Closing Question — Still Patching?

# Section 0.8: Closing Question Card — "Why Are We Still Patching?"

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:12.68 - 0:15.68

## Visual Description
A split-screen composition that emerges during the final seconds of the cold open, reinforcing the thesis question. The left half shows a faded, desaturated image of tangled legacy code (simulated with a code texture overlay), while the right half shows a clean, luminous empty canvas — representing the possibility of starting fresh. A single bold question appears centered across both halves: "Why are we still patching?" The split emphasizes the tension between old habits and new possibilities.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo footage
- Split line: vertical at x=960, 2px wide, rgba(255, 255, 255, 0.2)

### Chart/Visual Elements
- Left panel (0-960px): semi-transparent overlay
  - Color: rgba(15, 23, 42, 0.6) with desaturation filter
  - Texture: subtle code-line pattern (horizontal lines at 8px intervals, rgba(255,255,255,0.04))
  - Label: "patching" — Inter Regular, 18px, rgba(255,255,255,0.3), bottom-left at (40, 1040)
- Right panel (960-1920px): semi-transparent overlay
  - Color: rgba(15, 23, 42, 0.3) — slightly lighter, more open
  - Subtle radial glow from center-right: #3B82F6 at 5% opacity
  - Label: "building" — Inter Regular, 18px, rgba(59,130,246,0.4), bottom-right at (1880, 1040), right-aligned
- Center question: spans both panels
  - Text: "Why are we still patching?"
  - Position: centered at (960, 480)

### Animation Sequence
1. **Frame 380-400 (12.67-13.33s):** Split panels fade in from 0% to full opacity. Split line draws from top to bottom.
2. **Frame 400-420 (13.33-14.0s):** Question text fades in — opacity 0→1, slight upward drift (y: 500→480, 20px).
3. **Frame 420-440 (14.0-14.67s):** Hold. "patching" and "building" labels fade in subtly (opacity 0→0.3/0.4 over 10 frames).
4. **Frame 440-470 (14.67-15.68s):** Entire card fades out with the section's black fade-out (06_fade_bookends.md).

### Typography
- Question: Inter Bold, 48px, white (#FFFFFF)
- Text shadow: 0 2px 20px rgba(0, 0, 0, 0.7)
- Letter spacing: -0.01em
- Panel labels: Inter Regular, 18px, see colors above

### Easing
- Panel fade-in: `easeOutCubic`
- Split line draw: `easeInOutCubic`
- Question text fade + drift: `easeOutQuad`
- Label fade-in: `linear`

## Narration Sync
> "So why are we still patching?"

The question card appears as the narrator asks the thesis question. The text reinforces the audio — the viewer reads what they hear.

## Code Structure (Remotion)
```typescript
<Sequence from={380} durationInFrames={90}>
  <AbsoluteFill>
    {/* Left panel — patching */}
    <div
      style={{
        position: 'absolute', left: 0, top: 0, width: '50%', height: '100%',
        backgroundColor: 'rgba(15, 23, 42, 0.6)',
        filter: 'saturate(0.4)',
        opacity: interpolate(frame, [380, 400], [0, 1], { extrapolateRight: 'clamp' }),
      }}
    />
    {/* Right panel — building */}
    <div
      style={{
        position: 'absolute', right: 0, top: 0, width: '50%', height: '100%',
        backgroundColor: 'rgba(15, 23, 42, 0.3)',
        opacity: interpolate(frame, [380, 400], [0, 1], { extrapolateRight: 'clamp' }),
      }}
    />
    {/* Split line */}
    <SplitLine
      x={960}
      drawProgress={interpolate(frame, [380, 400], [0, 1], { extrapolateRight: 'clamp' })}
    />
    {/* Question text */}
    <Sequence from={20}>
      <CenterText
        text="Why are we still patching?"
        style={{
          opacity: interpolate(frame, [400, 420], [0, 1], { extrapolateRight: 'clamp' }),
          transform: `translateY(${interpolate(frame, [400, 420], [20, 0], { extrapolateRight: 'clamp' })}px)`,
        }}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "question_text": "Why are we still patching?",
  "split_position_x": 960,
  "left_label": "patching",
  "right_label": "building",
  "entry_frame": 380,
  "question_frame": 400,
  "total_frames": 90,
  "left_panel_color": "rgba(15, 23, 42, 0.6)",
  "right_panel_color": "rgba(15, 23, 42, 0.3)"
}
```

---
