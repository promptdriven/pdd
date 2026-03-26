[title:]

# Section 1.14: Key Insight Stillness — The 3Blue1Brown Pause

**Tool:** Title
**Duration:** ~7s (210 frames @ 30fps)
**Timestamp:** 7:29 - 7:36

## Visual Description

A moment of deliberate visual stillness — the "and here's the key insight" beat borrowed from 3Blue1Brown's signature pacing. The screen clears completely. A beat of pure dark navy-black. Then a clean, minimal text setup fades in.

This is the palate cleanser between the overwhelming data of the economics argument and the clean conclusion. The stillness itself is the design — it forces the viewer to pause, reset, and prepare for the synthesis.

After 2 seconds of darkness, a single clean line fades in: no chart, no graph, no data. Just the breathing room before the double meter insight.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none — deliberately empty
- Blueprint grid from earlier specs: REMOVED for this beat

### Chart/Visual Elements

#### Phase 1 — Clear (0-2s)
- Pure `#0A0F1A` background. Nothing on screen.
- A thin, barely visible horizontal line at y: 540 slowly pulses in opacity from 0.0 to 0.03 and back — subtle enough to be almost subliminal. Color: `#E2E8F0`.

#### Phase 2 — Setup (2-7s)
- A faint, warm glow appears at center: `#FFB347` at 0.02, 200px radial gradient
- This warm glow is a callback to the grandmother's lamplight — the craft metaphor
- No text. The warmth hangs. The transition to the double meter insight happens at the cut.

### Animation Sequence
1. **Frame 0-60 (0-2s):** Pure dark. Previous visual has faded. Barely visible horizontal line pulses.
2. **Frame 60-90 (2-3s):** Warm glow begins to appear at center. Very subtle.
3. **Frame 90-180 (3-6s):** Glow holds at peak (still barely visible). The stillness is the point.
4. **Frame 180-210 (6-7s):** Hold. Transition to next spec.

### Typography
- None. This is a deliberately text-free visual beat.

### Easing
- Horizontal line pulse: `easeInOut(sine)` on 120-frame cycle, 0.0 → 0.03
- Warm glow appear: `easeOut(cubic)` over 30 frames
- Warm glow hold: steady

## Narration Sync
> (No narration during the pure stillness beat — this is the pause between segments 032 and 033, or the transition moment.)

This falls in the gap between `part1_economics_032` (ending ~447.88s) and `part1_economics_033` (starting ~448.18s), but the visual stillness can extend slightly before and after as a pacing beat.

- **447.88s**: Previous visual fades out
- **448.18s**: Stillness holds, then transitions to double meter insight

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={210}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Barely visible horizontal line pulse */}
    <PulsingLine
      y={540} color="#E2E8F0"
      minOpacity={0.0} maxOpacity={0.03}
      cycleFrames={120} strokeWidth={1} />

    {/* Warm center glow */}
    <Sequence from={60}>
      <FadeIn duration={30}>
        <RadialGlow
          center={[960, 540]} radius={200}
          color="#FFB347" opacity={0.02} />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "variant": "stillness_beat",
  "backgroundColor": "#0A0F1A",
  "elements": [
    {
      "type": "pulsing_line",
      "color": "#E2E8F0",
      "maxOpacity": 0.03,
      "purpose": "subliminal_presence"
    },
    {
      "type": "radial_glow",
      "color": "#FFB347",
      "opacity": 0.02,
      "purpose": "warmth_callback"
    }
  ],
  "narrationSegments": []
}
```

---
