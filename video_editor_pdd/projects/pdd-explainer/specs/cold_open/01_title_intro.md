[title:]

# Section 0.1: Cold Open Title Intro

**Tool:** Remotion
**Duration:** ~3s (90 frames @ 30fps)
**Timestamp:** 0:00 - 0:03

## Visual Description
A minimal opening beat. The screen is dark. A single blinking cursor appears center-left, reminiscent of a code editor. The line "If you use Cursor, or Claude Code, or Copilot..." types out in elegant sans-serif on a dark background — not character-by-character, but fading in phrase-by-phrase with commas as break points. Each tool name briefly highlights in a subtle blue glow before settling to white. This establishes the conversational, knowing tone before the split screen appears.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep charcoal `#0A0A0F` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Cursor:** Blinking vertical bar, `#4A90D9`, 2px wide x 28px tall, at left edge of text baseline
- **Phrase 1:** "If you use " — white `#E2E8F0`, appears at center
- **Phrase 2:** "Cursor" — briefly glows `#4A90D9` then settles to `#FFFFFF`
- **Phrase 3:** ", or Claude Code" — white `#E2E8F0`, "Claude Code" glows `#4A90D9`
- **Phrase 4:** ", or Copilot..." — white `#E2E8F0`, "Copilot" glows `#4A90D9`
- Text block centered at approximately (960, 520)

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Black screen. Cursor blinks twice (500ms cycle)
2. **Frame 10-25 (0.33-0.83s):** "If you use " fades in (opacity 0→1), cursor moves to end
3. **Frame 25-40 (0.83-1.33s):** "Cursor" fades in with blue glow pulse (0→0.6→0 over 15 frames), settles white
4. **Frame 40-55 (1.33-1.83s):** ", or Claude Code" fades in, "Claude Code" gets blue glow pulse
5. **Frame 55-70 (1.83-2.33s):** ", or Copilot..." fades in, "Copilot" gets blue glow pulse
6. **Frame 70-90 (2.33-3.0s):** Hold. Cursor continues blinking. Full text visible.

### Typography
- Narration text: Inter, 48px, regular (400), `#E2E8F0`
- Tool names (highlight state): Inter, 48px, semi-bold (600), `#FFFFFF` with `#4A90D9` text-shadow
- Cursor: monospace, `#4A90D9`

### Easing
- Phrase fade-in: `easeOut(quad)`
- Glow pulse: `easeInOut(sin)`
- Cursor blink: step function (binary on/off, 15-frame period)

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot..."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <BlinkingCursor x={textLeftEdge} y={520} color="#4A90D9" />
  <Sequence from={10}>
    <FadeInPhrase text="If you use " color="#E2E8F0" />
  </Sequence>
  <Sequence from={25}>
    <GlowPhrase text="Cursor" glowColor="#4A90D9" />
  </Sequence>
  <Sequence from={40}>
    <GlowPhrase text=", or Claude Code" glowColor="#4A90D9" highlightWord="Claude Code" />
  </Sequence>
  <Sequence from={55}>
    <GlowPhrase text=", or Copilot..." glowColor="#4A90D9" highlightWord="Copilot" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "phrases": [
    { "text": "If you use ", "startFrame": 10, "style": "normal" },
    { "text": "Cursor", "startFrame": 25, "style": "glow" },
    { "text": ", or Claude Code", "startFrame": 40, "style": "glow", "highlightWord": "Claude Code" },
    { "text": ", or Copilot...", "startFrame": 55, "style": "glow", "highlightWord": "Copilot" }
  ],
  "backgroundColor": "#0A0A0F",
  "textColor": "#E2E8F0",
  "glowColor": "#4A90D9",
  "cursorColor": "#4A90D9"
}
```

---
