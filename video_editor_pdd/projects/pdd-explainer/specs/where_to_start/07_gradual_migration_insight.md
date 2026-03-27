[Remotion]

# Section 6.7: Value Migration — From Code to Specification

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:29 - 0:34

## Visual Description

A final visual coda that transitions from the "Where to Start" section into the Closing. The partially-migrated codebase from spec 05 is visible, but now it transforms into an abstract visualization of value flow.

Two labeled containers sit side by side:
- **Left: "CODE"** — a container that was once full (represented by a filled rectangle) is now partially drained, with a flowing liquid-like animation showing value leaving.
- **Right: "SPECIFICATION"** — a container that was once empty is now filling up with the same green-tinted "value" flowing in from the left.

Between them, a gentle arc of flowing particles connects the two — value transferring from code to specification. The metaphor is intuitive: value is relocating, not being destroyed.

Below, a single line of text fades in: "from code to specification" — the thesis of the entire section distilled.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Code Container (Left)
- Position: (380, 420), 250x300px
- Outer border: `#64748B`, 2px, 6px radius
- Fill level: starts at 70%, drains to 40% during animation
- Fill color: `#94A3B8` at 0.3 (gray, indicating devalued)
- Label: "CODE" — Inter, 18px, semi-bold (600), `#64748B`, centered above container at y: 250

#### Specification Container (Right)
- Position: (1160, 420), 250x300px
- Outer border: `#5AAA6E`, 2px, 6px radius
- Fill level: starts at 30%, fills to 60% during animation
- Fill color: `#5AAA6E` at 0.25 (green, indicating value)
- Label: "SPECIFICATION" — Inter, 18px, semi-bold (600), `#5AAA6E`, centered above container at y: 250

#### Flow Arc
- 15-20 particles flowing from left container to right, along a gentle parabolic arc
- Particles: 3px circles, `#5AAA6E` at 0.5
- Arc peak at y: 300 (above containers)
- Particles transition from gray (`#94A3B8`) at source to green (`#5AAA6E`) at destination

#### Thesis Text
- "from code to specification" — Inter, 24px, regular (400), `#94A3B8`
- "specification" in `#5AAA6E` for emphasis
- Centered at (960, 820)

### Animation Sequence
1. **Frame 0-30 (0-1s):** Two containers fade in, already at their starting fill levels. Labels appear.
2. **Frame 30-90 (1-3s):** Flow arc particles begin traveling. Code container drains slowly. Specification container fills.
3. **Frame 90-120 (3-4s):** Thesis text fades in: "from code to specification."
4. **Frame 120-150 (4-5s):** Hold. Particles continue flowing gently. Final frame for the section before closing transition.

### Typography
- Container labels: Inter, 18px, semi-bold (600), respective colors
- Thesis text: Inter, 24px, regular (400), `#94A3B8` with `#5AAA6E` accent
- "specification": `#5AAA6E`

### Easing
- Container fade-in: `easeOut(quad)` over 20 frames
- Fill level change: `easeInOut(cubic)` over 60 frames
- Particle flow: `easeInOut(quad)` per particle, continuous stagger
- Particle color transition: linear along arc path
- Thesis text fade-in: `easeOut(quad)` over 20 frames

## Narration Sync
> "don't patch socks because socks got cheap."

Segment: `where_to_start_003`

- **29.88s** (seg 003): Containers visible, flow begins
- **32.00s**: Thesis text appears
- **34.88s** (seg 003 ends): Hold, transition to Closing section

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.03} />

    {/* Container labels */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <Text text="CODE" font="Inter" size={18}
          weight={600} color="#64748B"
          x={380} y={250} align="center" />
        <Text text="SPECIFICATION" font="Inter" size={18}
          weight={600} color="#5AAA6E"
          x={1160} y={250} align="center" />
      </FadeIn>
    </Sequence>

    {/* Code container (draining) */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <FillContainer
          position={[380, 420]} size={[250, 300]}
          borderColor="#64748B"
          fillColor="#94A3B8" fillOpacity={0.3}
          fromLevel={0.7} toLevel={0.4}
          drainDuration={60} drainStart={30}
        />
      </FadeIn>
    </Sequence>

    {/* Specification container (filling) */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <FillContainer
          position={[1160, 420]} size={[250, 300]}
          borderColor="#5AAA6E"
          fillColor="#5AAA6E" fillOpacity={0.25}
          fromLevel={0.3} toLevel={0.6}
          fillDuration={60} fillStart={30}
        />
      </FadeIn>
    </Sequence>

    {/* Flow arc particles */}
    <Sequence from={30}>
      <ParticleArc
        from={[505, 420]} to={[1035, 420]}
        arcPeak={300}
        count={18}
        particleSize={3}
        fromColor="#94A3B8" toColor="#5AAA6E"
        opacity={0.5}
        duration={60} looping
        staggerDelay={4}
      />
    </Sequence>

    {/* Thesis text */}
    <Sequence from={90}>
      <FadeIn duration={20}>
        <RichText x={960} y={820} align="center">
          <Span text="from code to " font="Inter" size={24}
            weight={400} color="#94A3B8" />
          <Span text="specification" font="Inter" size={24}
            weight={400} color="#5AAA6E" />
        </RichText>
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "value_flow_animation",
  "animationId": "code_to_specification",
  "containers": [
    {
      "id": "code",
      "label": "CODE",
      "color": "#64748B",
      "fillColor": "#94A3B8",
      "startLevel": 0.7,
      "endLevel": 0.4
    },
    {
      "id": "specification",
      "label": "SPECIFICATION",
      "color": "#5AAA6E",
      "fillColor": "#5AAA6E",
      "startLevel": 0.3,
      "endLevel": 0.6
    }
  ],
  "thesisText": "from code to specification",
  "narrationSegments": ["where_to_start_003"]
}
```

---
