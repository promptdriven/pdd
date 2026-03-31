[title:]

# Section 0.7: Title Card — Prompt-Driven Development

**Tool:** Title
**Duration:** ~2s (60 frames @ 30fps)
**Timestamp:** 0:31 - 0:33

## Visual Description

The regenerated code from spec 06 is still visible behind, slightly dimmed. Over it, a title card fades in: **"Prompt-Driven Development"** in large, clean white type. The text appears centered over the code, with a semi-transparent dark overlay creating contrast. The code is still faintly visible beneath — the title is literally superimposed on the fresh, clean output. This establishes the name before the demo continues.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Inherited from spec 06 (code editor with regenerated code)
- Overlay: `#0A0F1A` at 0.7 opacity, full-screen

### Chart/Visual Elements

#### Dark Overlay
- Full screen `#0A0F1A` at 0.7 opacity
- Allows regenerated code to bleed through faintly

#### Title Text
- Text: "Prompt-Driven Development"
- Position: centered at (960, 480)
- Font: Inter, 72px, Bold (700)
- Color: `#E2E8F0` (light gray-blue)
- Letter-spacing: -1px
- Text-shadow: `0 2px 20px rgba(137, 180, 250, 0.3)` (subtle blue glow)

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Dark overlay fades in over the code. `easeOut(quad)`.
2. **Frame 15-35 (0.5-1.17s):** Title text fades up from 10px below, `easeOut(cubic)`. Subtle blue glow appears.
3. **Frame 35-60 (1.17-2s):** Hold. Title fully visible over the dimmed code background.

### Typography
- Title: Inter, 72px, Bold (700), `#E2E8F0`
- Blue glow shadow for depth

### Easing
- Overlay fade: `easeOut(quad)` over 15 frames
- Title fade-up: `easeOut(cubic)` over 20 frames, translateY from +10px to 0
- Hold: static

## Narration Sync
> "...and the code regenerates."

Segment: `cold_open_008` (partial — overlaps with end of spec 06 and beginning of spec 08)

- **31.00s**: Title overlay begins fading in
- **32.68s** (seg 008 ends): Title fully established

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  {/* Dark overlay */}
  <Sequence from={0} durationInFrames={60}>
    <FadeIn durationFrames={15}>
      <Overlay color="#0A0F1A" opacity={0.7} />
    </FadeIn>
  </Sequence>

  {/* Title text */}
  <Sequence from={15} durationInFrames={45}>
    <FadeSlideUp durationFrames={20} offsetY={10}>
      <TitleText
        text="Prompt-Driven Development"
        font="Inter"
        size={72}
        weight={700}
        color="#E2E8F0"
        letterSpacing={-1}
        glow={{ color: "#89B4FA", blur: 20, opacity: 0.3 }}
      />
    </FadeSlideUp>
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "componentId": "title_card_pdd",
  "durationFrames": 60,
  "fps": 30,
  "narrationSegments": ["cold_open_008"],
  "title": "Prompt-Driven Development",
  "overlayOpacity": 0.7,
  "inheritsBackground": "06_code_regeneration"
}
```

---
