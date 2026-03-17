[Remotion]

# Section 0.6: "So Why Are We Still Patching?" — The Beat

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:28 - 0:33

## Visual Description

A moment of deliberate stillness — the 3Blue1Brown "let that sink in" beat. The clean regenerated code from the previous shot is still on screen but begins to dim, pulling focus away from the code and toward a single line of text that fades in at the center of the screen.

The text reads: **"So why are we still patching?"** — rendered in clean, large typography against the dimmed code background. The question hangs in the air. No animation beyond the fade-in. No clever transitions. Just the question, demanding an answer.

This is the pivot moment of the cold open. Everything before this was setup. Everything after is the answer. The stillness forces the viewer to sit with the question.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (continues from previous shot — IDE background)
- Code underlay: the 14-line clean code from spec 05, dimmed to 0.08 opacity

### Chart/Visual Elements

#### Dimmed Code Underlay
- The regenerated code from 05_code_blink remains visible but fades to 0.08 opacity
- Creates a subtle texture — the viewer knows code is there but can't read it
- Serves as a reminder: we just saw something transformative

#### Question Text
- "So why are we still patching?" — Inter, 42px, weight 300 (light), `#E2E8F0` at 0.9
- Centered: x: 960, y: 540
- Letter-spacing: 1px
- The word "patching" has a subtle warm amber tint: `#D9944A` at 0.9 — calling back to the grandmother's world

#### Subtle Accent
- A thin horizontal line beneath the text: 120px wide, 1px, `#334155` at 0.3
- Centered at y: 580
- Draws from center outward after text appears

### Animation Sequence
1. **Frame 0-30 (0-1s):** Code from previous shot dims from full visibility to 0.08 opacity. Smooth, continuous fade.
2. **Frame 30-75 (1-2.5s):** Question text fades in. "So why are we still " in `#E2E8F0`, then "patching?" in `#D9944A`. The text appears as one unit but the color difference is subtle.
3. **Frame 75-90 (2.5-3s):** Thin horizontal line draws from center outward beneath the text.
4. **Frame 90-150 (3-5s):** Hold. Complete stillness. The question sits. No movement at all — not even a blink or pulse.

### Typography
- Question: Inter, 42px, light (300), `#E2E8F0` at 0.9, centered
- "patching?" accent: `#D9944A` at 0.9 (same size and weight, different color)
- Letter-spacing: 1px

### Easing
- Code dim: `easeInOut(cubic)` over 30 frames
- Text fade-in: `easeOut(quad)` over 30 frames
- Accent line draw: `easeOut(cubic)` over 15 frames
- Hold: static (no easing — complete stillness)

## Narration Sync
> "So why are we still patching?"

Segment: `cold_open_005`

- **0:28** ("So why"): Code begins dimming
- **0:29** ("are we still"): Question text fading in
- **0:31** ("patching?"): Text fully visible. Accent line draws. Hold.
- **0:31-0:33** (silence): The question hangs. Beat.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Dimmed code underlay from previous shot */}
    <Sequence from={0}>
      <FadeTo targetOpacity={0.08} duration={30}>
        <CodeBlock
          code={regeneratedCodeLines}
          font="JetBrains Mono" size={14}
          syntaxTheme="github-dark"
        />
      </FadeTo>
    </Sequence>

    {/* Question text */}
    <Sequence from={30}>
      <FadeIn duration={30}>
        <AbsoluteFill style={{
          display: 'flex', alignItems: 'center', justifyContent: 'center',
          flexDirection: 'column'
        }}>
          <Text font="Inter" size={42} weight={300}
            letterSpacing={1} y={540} align="center">
            <Span color="#E2E8F0" opacity={0.9}>
              So why are we still{' '}
            </Span>
            <Span color="#D9944A" opacity={0.9}>
              patching?
            </Span>
          </Text>
        </AbsoluteFill>
      </FadeIn>
    </Sequence>

    {/* Accent line */}
    <Sequence from={75}>
      <DrawLine from={[900, 580]} to={[1020, 580]}
        color="#334155" opacity={0.3} width={1}
        drawDuration={15} fromCenter />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "text_beat",
  "chartId": "still_patching_question",
  "questionText": "So why are we still patching?",
  "accentWord": "patching?",
  "accentColor": "#D9944A",
  "textColor": "#E2E8F0",
  "backgroundColor": "#0D1117",
  "codeUnderlayOpacity": 0.08,
  "holdDuration": 60,
  "narrationSegments": ["cold_open_005"]
}
```

---
