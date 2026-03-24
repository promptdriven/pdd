[Remotion]

# Section 6.7: Transition to Closing

**Tool:** Remotion
**Duration:** ~3s (90 frames @ 30fps)
**Timestamp:** 0:29 - 0:32

## Visual Description

A brief transition that bridges the "where to start" section into the closing. The quote card from the previous shot dissolves. The screen holds on deep navy-black for a beat — clean, empty, anticipatory. Then a faint ghost echo of the sock metaphor appears at very low opacity: the outline of a sock being discarded. This visual whisper sets up the closing section's full sock callback split.

The transition is intentionally minimal. The argument is complete. The "where to start" section answered the practical question. Now the closing will land the emotional punch.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none

### Chart/Visual Elements

#### Quote Echo (dissolving)
- Ghost of previous quote text: `#E2E8F0` at 0.06, fading to 0
- Ghost of amber line: `#D9944A` at 0.04, fading to 0
- These are residual opacity from the previous card

#### Sock Outline Ghost
- Simple line drawing of a sock silhouette, centered at (960, 540)
- Stroke: 1.5px, `#D9944A` at 0.05
- Scale: approximately 200x280px
- Appears briefly at low opacity, then dissolves — a preview, not a scene

### Animation Sequence
1. **Frame 0-30 (0-1s):** Quote text ghosts dissolve from 0.06 → 0. Screen settles to clean black. `easeInQuad`.
2. **Frame 30-60 (1-2s):** Sock outline ghost fades in to 0.05, holds briefly. `easeOutQuad` in, `easeInQuad` out.
3. **Frame 60-90 (2-3s):** Everything fades to pure black. Clean transition. Ready for closing section.

### Typography
- None (text-free transition)

### Easing
- Quote ghost dissolve: `easeIn(quad)` over 30 frames
- Sock outline fade-in: `easeOut(quad)` over 15 frames
- Sock outline fade-out: `easeIn(quad)` over 15 frames
- Final black: `linear`

## Narration Sync
> "Code just got that cheap."

Segment: `where_to_start_003`

- **0:29** (pause after quote): Quote dissolves, clean black
- **0:30** ("Code just got"): Sock ghost flickers
- **0:32** ("that cheap"): Pure black — ready for closing

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Quote ghost dissolve */}
    <Sequence from={0} durationInFrames={30}>
      <FadeOut duration={30}>
        <GhostText lines={[
          { text: "You don't patch socks", color: "#E2E8F0", opacity: 0.06 },
          { text: "because socks got cheap.", color: "#D9944A", opacity: 0.04 }
        ]} />
      </FadeOut>
    </Sequence>

    {/* Sock outline ghost */}
    <Sequence from={30} durationInFrames={30}>
      <FadeIn duration={15}>
        <FadeOut duration={15} startFrom={15}>
          <SockOutline
            cx={960} cy={540}
            width={200} height={280}
            strokeColor="#D9944A"
            strokeWidth={1.5}
            opacity={0.05}
          />
        </FadeOut>
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "transition",
  "transitionId": "where_to_start_to_closing",
  "echoes": [
    { "source": "no_big_bang_callout", "opacity": 0.06 },
    { "source": "sock_metaphor", "opacity": 0.05 }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["where_to_start_003"]
}
```

---
