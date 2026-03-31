[title:]

# Section 0.9: Title Card — "Prompt-Driven Development"

**Tool:** Title
**Duration:** ~2s (60 frames @ 30fps)
**Timestamp:** 0:31 - 0:33

## Visual Description

The title card fades in OVER the regenerated code from spec 08, which remains visible but dims to ~20% opacity. The title "Prompt-Driven Development" appears in large, clean typography — centered on screen. No subtitle, no explanation. The name speaks after the demo.

The regenerated code behind the title provides visual context: this is what PDD produces. The title is a label for what the viewer just witnessed.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Code editor from spec 08 at 20% opacity, overlaid with semi-transparent `#0A0F1A` at 0.8
- No grid lines

### Chart/Visual Elements

#### Dimming Overlay
- `#0A0F1A` at 0.8, full canvas
- Fades in over the regenerated code

#### Title Text
- "Prompt-Driven" — Inter, 64px, bold (700), `#E2E8F0`, centered at y: 480
- "Development" — Inter, 64px, bold (700), `#E2E8F0`, centered at y: 560
- Subtle text-shadow: 0 0 40px `#4A90D9` at 0.15

#### Horizontal Accent
- Thin line: 200px wide, 2px, `#4A90D9` at 0.4, centered at y: 525

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Dimming overlay fades in over regenerated code.
2. **Frame 10-25 (0.33-0.83s):** "Prompt-Driven" fades in with 5px upward slide.
3. **Frame 20-30 (0.67-1s):** Horizontal accent draws from center outward.
4. **Frame 25-40 (0.83-1.33s):** "Development" fades in with 5px upward slide.
5. **Frame 40-60 (1.33-2s):** Hold. Title visible over dimmed code.

### Typography
- Title: Inter, 64px, bold (700), `#E2E8F0`
- Text-shadow: `0 0 40px rgba(74, 144, 217, 0.15)`

### Easing
- Dimming overlay: `easeOut(quad)` over 15 frames
- Title fade-in: `easeOut(quad)` over 15 frames
- Title slide-up: `easeOut(cubic)` over 15 frames
- Accent draw: `easeInOut(quad)` over 10 frames

## Narration Sync
> "15 lines of prompt, 200 lines of clean code."

Segment: `cold_open_008` (tail end)

- **31.00s**: Title fades in — overlapping tail of "200 lines of clean code"
- **32.68s** (seg 008 ends): Title fully visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  {/* Dimming overlay over previous code */}
  <Sequence from={0}>
    <FadeIn duration={15}>
      <AbsoluteFill style={{ backgroundColor: 'rgba(10, 15, 26, 0.8)' }} />
    </FadeIn>
  </Sequence>

  {/* Title: Prompt-Driven */}
  <Sequence from={10}>
    <SlideUp distance={5} duration={15}>
      <FadeIn duration={15}>
        <Text text="Prompt-Driven" font="Inter" size={64}
          weight={700} color="#E2E8F0"
          x={960} y={480} align="center"
          shadow="0 0 40px rgba(74,144,217,0.15)" />
      </FadeIn>
    </SlideUp>
  </Sequence>

  {/* Horizontal accent */}
  <Sequence from={20}>
    <DrawLine from={[860, 525]} to={[1060, 525]}
      color="#4A90D9" opacity={0.4} width={2}
      drawDuration={10} fromCenter />
  </Sequence>

  {/* Title: Development */}
  <Sequence from={25}>
    <SlideUp distance={5} duration={15}>
      <FadeIn duration={15}>
        <Text text="Development" font="Inter" size={64}
          weight={700} color="#E2E8F0"
          x={960} y={560} align="center"
          shadow="0 0 40px rgba(74,144,217,0.15)" />
      </FadeIn>
    </SlideUp>
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "titleLine1": "Prompt-Driven",
  "titleLine2": "Development",
  "backgroundColor": "rgba(10, 15, 26, 0.8)",
  "accentColor": "#4A90D9",
  "overlayOnPrevious": true,
  "narrationSegments": ["cold_open_008"]
}
```

---
