[title:]

# Section 0.8: Still Patching Beat — The Question Lingers

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 0:35 - 0:39

## Visual Description

A minimal title card that lets the central question breathe. Over the dark IDE background — still carrying the faint afterimage of the regenerated code — a single line of text fades in at center screen: "So why are we still patching?" The text is large, clean, and unhurried. It sits in white against the dark background with generous negative space. No ornamentation, no animation beyond the fade. The question is rhetorical and the beat is confident — it trusts the viewer to feel the weight. After 2 seconds of hold, the text begins a slow fade-out, yielding to the title card.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` — solid, matching the editor from previous scenes
- No grid, no decorative elements

### Chart/Visual Elements

**Question Text**
- Text: "So why are we still patching?"
- Font: Inter SemiBold, 52px
- Color: `#C9D1D9` at 0.92
- Position: centered horizontally (x: 960), vertically (y: 520)
- Text-align: center
- Letter-spacing: -0.5px (slightly tightened for authority)

**Ambient Glow**
- Subtle radial gradient behind text: `#4A90D9` at 0.03, radius 400px, centered on text
- Reinforces the "code world" palette without being distracting

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Text fades in from opacity 0 → 0.92. The glow fades in simultaneously at half the text's rate.
2. **Frame 20-80 (0.67-2.67s):** Hold. Text fully visible. The question sits with the viewer. No movement, no distraction.
3. **Frame 80-120 (2.67-4s):** Text and glow fade out together: opacity 0.92 → 0 over 40 frames. Smooth exit into the title card.

### Typography
- Question: Inter SemiBold, 52px, `#C9D1D9` at 0.92, letter-spacing: -0.5px

### Easing
- Fade in: `easeOut(cubic)` — fast appearance, gentle settle
- Fade out: `easeIn(cubic)` — slow start, accelerating exit

## Narration Sync
> (No narration — the question text IS the narration echo from scene 0.7. Silent beat.)

| Segment ID | Text | Sync Point |
|---|---|---|
| `cold_open_009` | (silence) | Full duration — the pause lets the previous narration resonate |

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: "#0D1117" }}>
    {/* Ambient glow */}
    <RadialGlow
      center={[960, 520]}
      radius={400}
      color="#4A90D9"
      opacity={interpolate(frame, [0, 20, 80, 120], [0, 0.03, 0.03, 0])}
    />

    {/* Question text */}
    <FadeInOut
      fadeInFrames={20}
      holdFrames={60}
      fadeOutFrames={40}
    >
      <Text
        text="So why are we still patching?"
        font="Inter"
        weight={600}
        size={52}
        color="#C9D1D9"
        opacity={0.92}
        x={960}
        y={520}
        align="center"
        letterSpacing={-0.5}
      />
    </FadeInOut>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "text": "So why are we still patching?",
  "font": { "family": "Inter", "weight": 600, "size": 52 },
  "color": "#C9D1D9",
  "opacity": 0.92,
  "position": { "x": 960, "y": 520 },
  "background": "#0D1117",
  "ambientGlow": { "color": "#4A90D9", "opacity": 0.03, "radius": 400 },
  "timing": {
    "fadeInFrames": 20,
    "holdFrames": 60,
    "fadeOutFrames": 40
  },
  "narrationSegments": ["cold_open_009"]
}
```
