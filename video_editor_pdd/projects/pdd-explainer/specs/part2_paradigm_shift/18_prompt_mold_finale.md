[Remotion]

# Section 2.18: The Prompt Is Your Mold — Finale

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 3:35 - 3:47

## Visual Description

The culminating visual that ties together the injection molding metaphor with the chip synthesis analogy. A glowing document labeled "PROMPT" pulses at center. From it, lines of code flow outward, filling a defined shape — like plastic filling a mold cavity. Test assertions appear as illuminated walls around the code, constraining its shape — like the steel walls of an injection mold.

The code is different each time it generates (shown by a subtle shimmer/regeneration cycle), but the test walls hold firm. The shape is always the same. The prompt is the mold. The code is the plastic. The tests are the walls.

This is the thesis visual for the entire section.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid: None — clean, focused

### Chart/Visual Elements

#### Prompt Document (center-top)
- Glowing document shape: rounded rectangle, `#D9944A` border 2px, `#D9944A` at 0.1 fill
- Label: "PROMPT", Inter, 16px, bold, `#D9944A`, centered inside
- Pulsing glow: `#D9944A` at 0.2, 30px blur, pulsing on 45-frame cycle
- Position: centered, y: 100, width: 300px, height: 80px

#### Code Flow (center)
- Lines of code text (JetBrains Mono, 12px, `#E2E8F0` at 0.6) flow downward from the prompt
- Code fills a defined rectangular shape (the "mold cavity")
- Cavity shape: 600px × 400px, centered at y: 400
- Code flow has particle-like behavior — lines stream in and settle into position

#### Test Walls (around code shape)
- Four walls around the code cavity: `#5AAA6E`, 3px, glowing
- Wall glow: `#5AAA6E` at 0.2, 15px blur
- Small labels on each wall: "assert", "expect", "verify", "test"
- Walls illuminate when code touches them — containment is active

#### Regeneration Cycle
- Every ~90 frames, the code inside shimmers/dissolves and regenerates
- New code fills the same shape — different text, same boundaries
- Test walls flash briefly during regeneration — still holding

### Animation Sequence
1. **Frame 0-45 (0-1.5s):** Prompt document fades in at top. Begins pulsing.
2. **Frame 45-90 (1.5-3s):** Test walls draw around the cavity space — four sides illuminate. Wall labels appear.
3. **Frame 90-150 (3-5s):** Code begins flowing from the prompt, streaming downward into the cavity. Lines settle into position.
4. **Frame 150-180 (5-6s):** Cavity full. Code is contained by test walls. First generation complete.
5. **Frame 180-210 (6-7s):** Code shimmers, dissolves. Regeneration. New code streams in. Same shape. Walls flash green — still holding.
6. **Frame 210-270 (7-9s):** Second generation complete. Different code, same boundaries. Hold.
7. **Frame 270-300 (9-10s):** One more regeneration cycle. Walls hold firm. The process is deterministic in shape if not in content.
8. **Frame 300-360 (10-12s):** Hold. The metaphor is complete. Slow fade to black.

### Typography
- Prompt label: Inter, 16px, bold (700), `#D9944A`
- Wall labels: JetBrains Mono, 11px, `#5AAA6E` at 0.7
- Code text: JetBrains Mono, 12px, `#E2E8F0` at 0.6

### Easing
- Prompt fade-in: `easeOut(cubic)` over 30 frames
- Prompt pulse: `easeInOut(sine)` on 45-frame cycle
- Wall draw: `easeInOut(cubic)` over 20 frames per wall
- Code flow: `easeOut(quad)` — streams fast, settles gently
- Code dissolve: `easeIn(quad)` over 15 frames
- Code regenerate: `easeOut(cubic)` over 20 frames
- Wall flash: `easeOut(quad)` over 10 frames
- Final fade: `easeIn(quad)` over 60 frames

## Narration Sync
> "The prompt is your mold. The code is just plastic. And just like chip synthesis — the code is different every generation. But the tests lock the behavior. The process is deterministic."

Segments: `part2_paradigm_shift_016` (tail — implied continuation)

- **230.0s**: Prompt document appears — "The prompt is your mold"
- **232.0s**: Test walls draw — "The code is just plastic"
- **234.0s**: Code flows in — "the code is different every generation"
- **237.0s**: Regeneration cycle — "But the tests lock the behavior"
- **240.0s**: Hold — "The process is deterministic"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Prompt document */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <PulsingDocument
          label="PROMPT" color="#D9944A"
          glowOpacity={0.2} glowBlur={30}
          pulseCycle={45} easing="easeInOutSine"
          x={960} y={100} width={300} height={80}
        />
      </FadeIn>
    </Sequence>

    {/* Test walls (mold cavity) */}
    <Sequence from={45}>
      <TestWalls
        x={660} y={200} width={600} height={400}
        wallColor="#5AAA6E" wallWidth={3}
        glowOpacity={0.2} glowBlur={15}
        labels={["assert", "expect", "verify", "test"]}
        drawDuration={20}
      />
    </Sequence>

    {/* Code flow with regeneration */}
    <Sequence from={90}>
      <CodeFlowWithRegeneration
        sourceY={180} cavityBounds={{ x: 660, y: 200, w: 600, h: 400 }}
        font="JetBrains Mono" fontSize={12}
        textColor="#E2E8F0" textOpacity={0.6}
        regenerateEvery={90} dissolveDuration={15}
        fillDuration={30}
        wallFlashColor="#5AAA6E" wallFlashDuration={10}
      />
    </Sequence>

    {/* Fade to black */}
    <Sequence from={300}>
      <FadeOut duration={60} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "metaphor_animation",
  "chartId": "prompt_mold_finale",
  "elements": {
    "prompt": { "label": "PROMPT", "color": "#D9944A", "role": "mold_specification" },
    "code": { "color": "#E2E8F0", "role": "plastic_output", "regenerates": true },
    "tests": { "color": "#5AAA6E", "role": "mold_walls", "labels": ["assert", "expect", "verify", "test"] }
  },
  "regenerationCycles": 3,
  "thesis": "The prompt is your mold. The code is just plastic.",
  "narrationSegments": ["part2_paradigm_shift_016"]
}
```

---
