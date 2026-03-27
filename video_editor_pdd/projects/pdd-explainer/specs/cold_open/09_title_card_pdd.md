[title:]

# Section 0.9: Title Card — "Prompt-Driven Development"

**Tool:** Title
**Duration:** ~2s (60 frames @ 30fps)
**Timestamp:** 0:17 - 0:18

## Visual Description
The title card fades in over the regenerated code from the previous shot. The clean code remains visible in the background at reduced opacity, creating a layered effect. "PROMPT-DRIVEN" appears first in large bold weight, then "DEVELOPMENT" fades in below with a slight offset. A thin horizontal rule draws between the two words. The text is white on the darkened code background — the regenerated code is the visual evidence of the thesis. This is the landing moment of the cold open: the name of the thing we've just demonstrated.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Inherited code editor (`#1E1E2E`) with code at 0.15 opacity
- Overlay: `#1E1E2E` at 0.7 (darkening layer over code)

### Chart/Visual Elements

#### Background Code Layer
- The regenerated clean function from 08_code_regeneration, visible at 15% opacity
- Creates texture and continuity — the title emerges FROM the code

#### Title Text
- "PROMPT-DRIVEN" — Inter, 64px, bold (700), `#CDD6F4`, centered at y: 470
- "DEVELOPMENT" — Inter, 64px, bold (700), `#CDD6F4`, centered at y: 545, offset-right 10px
- Horizontal rule: 300px wide, 2px, `#6C7086` at 0.5, centered between words at y: 510

#### Subtle Accent
- Thin glowing line beneath the rule: `#89B4FA` at 0.2, 200px wide, 1px, centered
- Suggests the technological/code nature of the concept

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Dark overlay fades in over regenerated code, dimming it to 15% opacity.
2. **Frame 10-25 (0.33-0.83s):** "PROMPT-DRIVEN" fades in with a 5px upward slide.
3. **Frame 25-30 (0.83-1.0s):** Horizontal rule draws from center outward.
4. **Frame 30-45 (1.0-1.5s):** "DEVELOPMENT" fades in with a 5px upward slide.
5. **Frame 45-48 (1.5-1.6s):** Blue accent glow pulses once beneath the rule.
6. **Frame 48-60 (1.6-2.0s):** Hold. Title fully visible over faded code. End of cold open.

### Typography
- Title words: Inter, 64px, bold (700), `#CDD6F4`
- Rule: `#6C7086` at 0.5
- Accent: `#89B4FA` at 0.2

### Easing
- Overlay fade: `easeOut(quad)` over 10 frames
- "PROMPT-DRIVEN" slide + fade: `easeOut(cubic)` over 15 frames
- Rule draw: `easeInOut(quad)` over 5 frames
- "DEVELOPMENT" slide + fade: `easeOut(cubic)` over 15 frames
- Accent pulse: `easeInOut(sine)` single cycle over 3 frames

## Narration Sync
> "So why are we still patching?"

Segment: `cold_open_006` (tail end — title card overlaps final beat)

- **17.40s**: Title card begins fade-in over regenerated code
- **17.90s**: Title fully visible — cold open ends

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <AbsoluteFill style={{ backgroundColor: '#1E1E2E' }}>
    {/* Background: regenerated code at low opacity */}
    <div style={{ opacity: 0.15 }}>
      <CodeEditor
        language="python"
        theme="catppuccin-mocha"
        code={CLEAN_FUNCTION_CODE}
      />
    </div>

    {/* Darkening overlay */}
    <Sequence from={0}>
      <FadeIn duration={10}>
        <AbsoluteFill style={{ backgroundColor: '#1E1E2E', opacity: 0.7 }} />
      </FadeIn>
    </Sequence>

    {/* Title: PROMPT-DRIVEN */}
    <Sequence from={10}>
      <SlideUp distance={5} duration={15}>
        <FadeIn duration={15}>
          <Text text="PROMPT-DRIVEN" font="Inter" size={64}
            weight={700} color="#CDD6F4"
            x={960} y={470} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={25}>
      <DrawLine from={[810, 510]} to={[1110, 510]}
        color="#6C7086" opacity={0.5} width={2}
        drawDuration={5} fromCenter />
    </Sequence>

    {/* Title: DEVELOPMENT */}
    <Sequence from={30}>
      <SlideUp distance={5} duration={15}>
        <FadeIn duration={15}>
          <Text text="DEVELOPMENT" font="Inter" size={64}
            weight={700} color="#CDD6F4"
            x={970} y={545} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Blue accent glow */}
    <Sequence from={45}>
      <GlowPulse
        color="#89B4FA" opacity={0.2}
        width={200} height={1}
        x={960} y={512}
        pulseFrames={3}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": 0,
  "titleLine1": "PROMPT-DRIVEN",
  "titleLine2": "DEVELOPMENT",
  "backgroundColor": "#1E1E2E",
  "backgroundLayer": "regenerated_code_at_15_percent",
  "accentColor": "#89B4FA",
  "narrationSegments": ["cold_open_006"],
  "durationSeconds": 2.0
}
```

---
