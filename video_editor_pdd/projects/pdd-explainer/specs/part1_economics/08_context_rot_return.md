[Remotion]

# Section 1.8: Context Rot Return — Faster Patching, Faster Rot

**Tool:** Remotion
**Duration:** ~11s (330 frames @ 30fps)
**Timestamp:** 2:25 - 2:36

## Visual Description

A brief return to the code cost chart, refocused on the "Context Rot" layer in the debt shading area. The Context Rot layer pulses with the noise texture from spec 06. A new annotation materializes:

**"Faster patching → faster growth → faster rot"**

This is a feedback loop annotation — three words connected by arrows, showing the vicious cycle. Each arrow pulses in sequence, creating a clockwise animation that conveys inevitability. The annotation sits over the debt area, making the connection between individual speed gains and systemic degradation.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: inherited from code cost chart, `#1E293B` at 0.06

### Chart/Visual Elements

#### Inherited Chart State
- Code cost chart visible with debt shading
- Context Rot layer highlighted with noise texture

#### Feedback Loop Annotation
- Three nodes arranged in a triangle:
  - "Faster patching" — top, Inter 16px, semi-bold, `#4A90D9`
  - "Faster growth" — bottom-right, Inter 16px, semi-bold, `#D9944A`
  - "Faster rot" — bottom-left, Inter 16px, semi-bold, `#EF4444`
- Connecting arrows: 2px, `#E2E8F0` at 0.5, curved
- Each arrow pulses `#FFFFFF` at 0.8 in sequence (clockwise)
- Cycle time: 90 frames (3s) per full rotation

#### Context Rot Pulse
- The noise texture in the debt area pulses in sync with the "faster rot" arrow highlight

### Animation Sequence
1. **Frame 0-60 (0-2s):** Chart visible with Context Rot layer highlighted. Noise texture pulses.
2. **Frame 60-150 (2-5s):** Feedback loop annotation builds: "Faster patching" appears, then arrow → "Faster growth", then arrow → "Faster rot", then arrow back to start.
3. **Frame 150-270 (5-9s):** Loop animates clockwise. Each node highlights as the pulse passes through it. Context Rot noise pulses in sync.
4. **Frame 270-330 (9-11s):** Hold. Loop continues cycling. Transition begins.

### Typography
- Loop nodes: Inter, 16px, semi-bold (600), respective colors
- Arrows: `#E2E8F0` at 0.5, 2px, with arrowhead

### Easing
- Node appear: `easeOut(back)` with scale 0.9→1.0 over 20 frames
- Arrow draw: `easeOut(quad)` over 25 frames
- Pulse travel: `easeInOut(sine)` per segment
- Noise pulse: `easeInOut(sine)` synced to "faster rot" highlight

## Narration Sync
> "Faster patching means faster growth means faster rot."

Segments: `part1_economics_018`

- **234.28s** (seg 018): Return to chart — "Faster patching"
- **237.00s**: Loop building — "faster growth"
- **240.00s**: Loop complete — "faster rot"
- **245.18s** (seg 018 ends): Loop cycling, transition begins

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={330}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Chart with Context Rot highlight */}
    <CodeCostChart state="context_rot_focus" />

    {/* Feedback loop annotation */}
    <Sequence from={60}>
      <FeedbackLoop
        nodes={[
          { text: "Faster patching", color: "#4A90D9", position: [960, 350] },
          { text: "Faster growth", color: "#D9944A", position: [1100, 550] },
          { text: "Faster rot", color: "#EF4444", position: [820, 550] }
        ]}
        arrowColor="#E2E8F0" arrowOpacity={0.5}
        buildDuration={90}
        pulseColor="#FFFFFF" pulseCycleDuration={90}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "annotation_overlay",
  "chartId": "code_cost_comparison",
  "parentSpec": "03_code_cost_chart",
  "feedbackLoop": {
    "nodes": [
      { "id": "faster_patching", "text": "Faster patching", "color": "#4A90D9" },
      { "id": "faster_growth", "text": "Faster growth", "color": "#D9944A" },
      { "id": "faster_rot", "text": "Faster rot", "color": "#EF4444" }
    ],
    "direction": "clockwise",
    "cycleDurationFrames": 90
  },
  "narrationSegments": ["part1_economics_018"]
}
```

---
