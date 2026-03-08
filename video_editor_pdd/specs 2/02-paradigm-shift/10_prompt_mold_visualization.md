[Remotion] Prompt=Mold Metaphor — Animated Triad Equation

# Section 2.9: Prompt-Mold Visualization — "The Prompt Is Your Mold"

**Tool:** Remotion
**Duration:** ~20s
**Timestamp:** 2:50 - 3:10

## Visual Description
An animated equation-style infographic that makes the PDD metaphor explicit. Three labeled boxes animate in sequence, connected by equals signs and relationship arrows. Box 1 (left): a golden document icon labeled "PROMPT" with subtitle "your mold." Box 2 (center): a blue code block icon labeled "CODE" with subtitle "is plastic." Box 3 (right): a green shield/check icon labeled "TESTS" with subtitle "lock behavior." The boxes connect with animated arrows: PROMPT → CODE (labeled "generates"), CODE ↔ TESTS (labeled "validates"). Below the equation, a synthesis line reads: "Design the specification. Generate the implementation. Verify automatically." Each phrase highlights in sequence as its corresponding box pulses. The entire composition has the authority of a textbook diagram but the polish of a motion graphic.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Equation region: centered, 1500x400px area at (210, 340) to (1710, 740)
- Backing panel: rounded rect, rgba(15, 23, 42, 0.8), blur(10px), border-radius 16px

### Chart/Visual Elements
- Box 1 — PROMPT:
  - Position: centered at (420, 490)
  - Shape: rounded rect, 240x200px, border 3px solid #F97316, fill rgba(249,115,22,0.08)
  - Icon: document/scroll silhouette, 64x64px, #FBBF24, centered in box upper portion
  - Label: "PROMPT" — centered below icon
  - Subtitle: "your mold" — below label, italic
  - Glow: 0 0 20px rgba(249,115,22,0.3) on border
- Box 2 — CODE:
  - Position: centered at (960, 490)
  - Shape: rounded rect, 240x200px, border 3px solid #3B82F6, fill rgba(59,130,246,0.08)
  - Icon: code brackets `</>` silhouette, 64x64px, #60A5FA, centered in box upper portion
  - Label: "CODE" — centered below icon
  - Subtitle: "is plastic" — below label, italic
  - Glow: 0 0 20px rgba(59,130,246,0.3) on border
- Box 3 — TESTS:
  - Position: centered at (1500, 490)
  - Shape: rounded rect, 240x200px, border 3px solid #22C55E, fill rgba(34,197,94,0.08)
  - Icon: shield with checkmark, 64x64px, #4ADE80, centered in box upper portion
  - Label: "TESTS" — centered below icon
  - Subtitle: "lock behavior" — below label, italic
  - Glow: 0 0 20px rgba(34,197,94,0.3) on border
- Arrow 1: PROMPT → CODE
  - Horizontal arrow from x=540 to x=840, y=490
  - Color: #94A3B8, 2px, arrowhead 12px
  - Label: "generates" centered above arrow, #94A3B8
- Arrow 2: CODE ↔ TESTS
  - Bidirectional horizontal arrow from x=1080 to x=1380, y=490
  - Color: #94A3B8, 2px, arrowheads on both ends
  - Label: "validates" centered above arrow, #94A3B8
- Synthesis line: centered at (960, 700)
  - Three phrases with sequential highlighting

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Backing panel fades in.
2. **Frame 25-55 (0.83-1.83s):** Box 1 (PROMPT) scales in — spring animation, border glow pulses. Icon, label, subtitle fade in.
3. **Frame 55-75 (1.83-2.5s):** Arrow 1 draws left-to-right. "generates" label fades in.
4. **Frame 75-105 (2.5-3.5s):** Box 2 (CODE) scales in — spring animation. Icon, label, subtitle fade in.
5. **Frame 105-125 (3.5-4.17s):** Arrow 2 draws with bidirectional arrowheads. "validates" label fades in.
6. **Frame 125-155 (4.17-5.17s):** Box 3 (TESTS) scales in — spring animation. Icon, label, subtitle fade in.
7. **Frame 155-200 (5.17-6.67s):** Hold. All three boxes visible with gentle glow pulses.
8. **Frame 200-240 (6.67-8s):** Synthesis line appears. "Design the specification." highlights — Box 1 pulses brighter.
9. **Frame 240-280 (8-9.33s):** "Generate the implementation." highlights — Box 2 pulses brighter.
10. **Frame 280-320 (9.33-10.67s):** "Verify automatically." highlights — Box 3 pulses brighter.
11. **Frame 320-480 (10.67-16s):** Hold at full display.
12. **Frame 480-600 (16-20s):** Entire visualization fades out — opacity 1→0 over 30 frames, then continues fading with section close.

### Typography
- Box labels: Inter Black, 24px, matching box border color, letter-spacing 0.1em
- Box subtitles: Inter Medium Italic, 18px, matching box border color at 70% opacity
- Arrow labels: Inter Medium, 14px, #94A3B8
- Synthesis line: Inter SemiBold, 22px, #94A3B8 (default), highlighted phrase #FFFFFF with text-shadow matching box color
  - Phrase separator: em-dash
  - Active phrase: transitions from #94A3B8 → #FFFFFF over 15 frames

### Easing
- Box scale-in: `spring({ damping: 14, stiffness: 180 })`
- Arrow draw: `easeInOutCubic`
- Glow pulse: sinusoidal, 2.5s period
- Box pulse on highlight: `easeInOutSine` (brightness 1.0→1.4→1.0 over 30 frames)
- Synthesis highlight: `easeOutCubic`
- Fade out: `easeInCubic`

## Narration Sync
> "The prompt is your mold. Code is plastic. Tests lock the behavior. We've seen this before — we just didn't recognize it."

Box 1 appears on "the prompt is your mold." Box 2 on "code is plastic." Box 3 on "tests lock the behavior." Synthesis line appears on "we've seen this before."

## Code Structure (Remotion)
```typescript
<Sequence from={TRIAD_START} durationInFrames={600}>
  <AbsoluteFill>
    <BackingPanel
      bounds={{ x: 210, y: 340, w: 1500, h: 400 }}
      opacity={interpolate(frame, [0, 25, 570, 600], [0, 0.8, 0.8, 0])}
    />

    {/* Box 1 — PROMPT */}
    <Sequence from={25} durationInFrames={575}>
      <TriadBox
        position={[420, 490]}
        icon="document"
        label="PROMPT"
        subtitle="your mold"
        borderColor="#F97316"
        iconColor="#FBBF24"
        scale={spring({ frame: frame - 25, fps: 30, config: { damping: 14, stiffness: 180 } })}
        glowOpacity={interpolate(Math.sin(frame * 0.084), [-1, 1], [0.15, 0.3])}
        pulseAt={200}
      />
    </Sequence>

    {/* Arrow: PROMPT → CODE */}
    <Sequence from={55} durationInFrames={20}>
      <ArrowConnector
        from={[540, 490]} to={[840, 490]}
        label="generates"
        drawProgress={interpolate(frame, [0, 20], [0, 1])}
      />
    </Sequence>

    {/* Box 2 — CODE */}
    <Sequence from={75} durationInFrames={525}>
      <TriadBox
        position={[960, 490]}
        icon="code_brackets"
        label="CODE"
        subtitle="is plastic"
        borderColor="#3B82F6"
        iconColor="#60A5FA"
        scale={spring({ frame: frame - 75, fps: 30, config: { damping: 14, stiffness: 180 } })}
        glowOpacity={interpolate(Math.sin(frame * 0.084), [-1, 1], [0.15, 0.3])}
        pulseAt={240}
      />
    </Sequence>

    {/* Arrow: CODE ↔ TESTS */}
    <Sequence from={105} durationInFrames={20}>
      <ArrowConnector
        from={[1080, 490]} to={[1380, 490]}
        label="validates"
        bidirectional
        drawProgress={interpolate(frame, [0, 20], [0, 1])}
      />
    </Sequence>

    {/* Box 3 — TESTS */}
    <Sequence from={125} durationInFrames={475}>
      <TriadBox
        position={[1500, 490]}
        icon="shield_check"
        label="TESTS"
        subtitle="lock behavior"
        borderColor="#22C55E"
        iconColor="#4ADE80"
        scale={spring({ frame: frame - 125, fps: 30, config: { damping: 14, stiffness: 180 } })}
        glowOpacity={interpolate(Math.sin(frame * 0.084), [-1, 1], [0.15, 0.3])}
        pulseAt={280}
      />
    </Sequence>

    {/* Synthesis line */}
    <Sequence from={200} durationInFrames={400}>
      <SynthesisLine
        phrases={[
          { text: "Design the specification.", highlightFrame: 0, color: "#F97316" },
          { text: "Generate the implementation.", highlightFrame: 40, color: "#3B82F6" },
          { text: "Verify automatically.", highlightFrame: 80, color: "#22C55E" },
        ]}
        position={[960, 700]}
        defaultColor="#94A3B8"
        highlightColor="#FFFFFF"
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "boxes": [
    {
      "label": "PROMPT",
      "subtitle": "your mold",
      "icon": "document",
      "border_color": "#F97316",
      "icon_color": "#FBBF24",
      "position": [420, 490],
      "entry_frame": 25
    },
    {
      "label": "CODE",
      "subtitle": "is plastic",
      "icon": "code_brackets",
      "border_color": "#3B82F6",
      "icon_color": "#60A5FA",
      "position": [960, 490],
      "entry_frame": 75
    },
    {
      "label": "TESTS",
      "subtitle": "lock behavior",
      "icon": "shield_check",
      "border_color": "#22C55E",
      "icon_color": "#4ADE80",
      "position": [1500, 490],
      "entry_frame": 125
    }
  ],
  "arrows": [
    { "from": [540, 490], "to": [840, 490], "label": "generates", "bidirectional": false },
    { "from": [1080, 490], "to": [1380, 490], "label": "validates", "bidirectional": true }
  ],
  "synthesis_phrases": [
    "Design the specification.",
    "Generate the implementation.",
    "Verify automatically."
  ],
  "total_frames": 600,
  "fps": 30
}
```

---
