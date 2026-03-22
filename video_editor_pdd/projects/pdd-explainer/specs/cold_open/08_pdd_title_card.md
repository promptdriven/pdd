[title:]

# Section 0.5: PDD Title Card — Prompt-Driven Development

**Tool:** Title
**Duration:** ~2s (60 frames @ 30fps)
**Timestamp:** 0:16 - 0:18

## Visual Description

The title card fades in over the dimmed regenerated code from the previous spec. "Prompt-Driven Development" appears in clean, authoritative type — the answer to the rhetorical question "So why are we still patching?"

The title uses the blue prompt color (`#4A90D9`) — this is the PDD color, the "new way" color, contrasting with the amber "patching" color that dominated the grandmother/darning imagery. The title sits at vertical center, slightly above midpoint.

Below the title, a thin subtitle: "The code is just plastic. The mold is what matters." — this is the thesis of the entire video, planted here as a seed.

The faded code from the previous spec serves as a textured background — the title literally sits on top of the regenerated code, reinforcing that PDD produces this clean output.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#111827` (slightly brightened dark, carried from previous spec)
- Underlayer: faded regenerated code at 30% opacity (from previous spec)

### Chart/Visual Elements

#### Main Title
- "Prompt-Driven Development" — Inter, 56px, bold (700), `#4A90D9` at 0.95
- Centered horizontally at x: 960
- Vertical position: y: 480 (slightly above center)
- Letter-spacing: 1px

#### Thin Horizontal Rule
- 80px wide, 1.5px, `#4A90D9` at 0.15, centered at y: 540
- Draws from center outward

#### Subtitle / Thesis Seed
- "The code is just plastic. The mold is what matters." — Inter, 15px, weight 300 (light), italic, `#94A3B8` at 0.35
- Centered at y: 570

#### Code Underlayer (from previous spec)
- Clean regenerated code at 30% opacity, same layout
- Provides texture without competing with title
- Continues fading to 20% opacity during title hold

### Animation Sequence
1. **Frame 0-5 (0-0.17s):** Code underlayer at 50% opacity (carried from previous spec). Title not yet visible.
2. **Frame 5-25 (0.17-0.83s):** Title "Prompt-Driven Development" fades in with 12px upward slide. Code underlayer continues fading to 30%.
3. **Frame 25-35 (0.83-1.17s):** Horizontal rule draws from center outward.
4. **Frame 35-45 (1.17-1.5s):** Subtitle fades in.
5. **Frame 45-60 (1.5-2s):** Hold. Title card sits with authority over the faded code. Code underlayer settles at 20%.

### Typography
- Title: Inter, 56px, bold (700), `#4A90D9` at 0.95, letter-spacing 1px
- Subtitle: Inter, 15px, light (300), italic, `#94A3B8` at 0.35
- Horizontal rule: 1.5px, `#4A90D9` at 0.15

### Easing
- Title fade-in + slide: `easeOut(cubic)` over 20 frames
- Rule draw: `easeOut(cubic)` over 10 frames
- Subtitle fade-in: `easeOut(quad)` over 10 frames
- Code underlayer fade: `easeIn(quad)` continuous from 50% → 20% over full duration

## Narration Sync
> "So why are we still patching?"

Segment: `cold_open_006` (shared with previous spec — this title lands on the final beat)

- **16.02s** ("So why"): Title begins to fade in
- **17.00s** ("still patching?"): Title fully visible — the answer is on screen
- **17.54s**: Hold — title and subtitle visible, cold open complete

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <AbsoluteFill>
    {/* Background */}
    <Fill color="#111827" />

    {/* Code underlayer — fading from previous spec */}
    <FadeOut startFrame={0} duration={60}
      fromOpacity={0.5} toOpacity={0.2}>
      <CodeBlock
        code={CLEAN_REGENERATED_CODE}
        font="JetBrains Mono" size={13}
        x={80} y={120}
        lineNumbers
        color="#E2E8F0"
      />
    </FadeOut>

    {/* Main title */}
    <Sequence from={5}>
      <SlideUp distance={12} duration={20}>
        <FadeIn duration={20}>
          <Text text="Prompt-Driven Development"
            font="Inter" size={56} weight={700}
            color="#4A90D9" opacity={0.95}
            letterSpacing={1}
            x={960} y={480} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={25}>
      <DrawLine from={[920, 540]} to={[1000, 540]}
        color="#4A90D9" opacity={0.15} width={1.5}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Subtitle */}
    <Sequence from={35}>
      <FadeIn duration={10}>
        <Text text="The code is just plastic. The mold is what matters."
          font="Inter" size={15} weight={300}
          fontStyle="italic"
          color="#94A3B8" opacity={0.35}
          x={960} y={570} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": 0,
  "sectionLabel": "Cold Open",
  "title": "Prompt-Driven Development",
  "titleColor": "#4A90D9",
  "subtitle": "The code is just plastic. The mold is what matters.",
  "subtitleColor": "#94A3B8",
  "backgroundColor": "#111827",
  "codeUnderlayer": {
    "content": "clean_regenerated_code",
    "opacity": { "from": 0.5, "to": 0.2 }
  },
  "narrationSegments": ["cold_open_006"]
}
```

---
