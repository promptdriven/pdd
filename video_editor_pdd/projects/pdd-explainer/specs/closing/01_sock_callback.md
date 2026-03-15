[Remotion]

# Section 7.1: The Sock Callback — Metaphor Returns

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 24:15 - 24:23

## Visual Description
The sock metaphor from the cold open returns one final time, completing the narrative circle. A single holey sock sits center-frame on a clean, modern surface — the same geometric style as Section 0.4. A simplified geometric person notices the hole, pauses for a beat of consideration, then casually discards it to the left (same toss arc) and grabs a fresh sock from the right. The motion is unhurried and decisive — no hesitation, no sentimentality. The economics made the decision obvious.

The color palette mirrors the cold open's modern tones (cool neutrals) but is slightly darker and more cinematic, signaling we've arrived at the conclusion.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Muted neutral `#E8E4DF` — slightly darker than cold open's `#F0EDE8` to mark the closing mood
- Grid lines: None

### Chart/Visual Elements
- **Person:** Simplified geometric figure — circle head `#64748B`, rectangle torso `#475569`, rectangle legs `#334155`. Centered at (960, 580). ~200px tall. Same design vocabulary as cold open
- **Holey Sock:** Rounded rectangle `#8B7355`, 80x40px, with a 14px circular cutout (hole) revealing background `#E8E4DF`. Initial position at hand level (960, 630)
- **Hole Highlight:** Red circle outline `#EF4444` at 40% opacity, 14px diameter, single pulse around the cutout
- **Trash Area (left):** No visible bin — sock simply arcs off-screen left past X=200, emphasizing effortlessness
- **Fresh Sock (right):** Clean rounded rectangle `#FFFFFF` with subtle `#E2E8F0` border, appears from right shelf area at (1300, 700)
- **Shelf:** Thin horizontal line `#94A3B8` at Y=740, spanning X=1150-1450

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Fade in from previous section. Person stands center, holding holey sock at waist level. Scene establishes.
2. **Frame 20-40 (0.67-1.33s):** Head tilts down 5deg toward sock. Hole highlight pulses once (`#EF4444` opacity 0→0.4→0 over 20 frames).
3. **Frame 40-60 (1.33-2.0s):** Brief pause — the "consideration" beat. Person is still. This mirrors the narration rhythm.
4. **Frame 60-100 (2.0-3.33s):** Sock toss. Sock follows a parabolic arc from (960, 630) toward off-screen left (100, 400). Sock rotates 270deg during flight, fading to opacity 0 as it exits. No landing — it simply leaves frame.
5. **Frame 100-130 (3.33-4.33s):** Person walks right (translateX +340px). Reaches toward shelf area.
6. **Frame 130-160 (4.33-5.33s):** Hand pulls fresh white sock from shelf. Fresh sock has a subtle clean glow — white `#FFFFFF` with a 4px `#4A90D9` shadow at 15% opacity.
7. **Frame 160-240 (5.33-8.0s):** Hold. Person stands with fresh sock. Confident stillness. Gentle breathing idle (torso scaleY 1.0→1.01→1.0, 50-frame cycle).

### Typography
- None in scene — purely visual storytelling

### Easing
- Fade in: `easeOut(quad)`
- Head tilt: `easeInOut(quad)`
- Hole highlight pulse: `easeInOut(sin)`
- Sock toss arc: `easeIn(quad)` rise, `easeIn(cubic)` descent
- Sock rotation: `linear`
- Sock fade-out: `easeIn(quad)`
- Walk: `linear` translate, `easeInOut(sin)` leg alternation
- Fresh sock pull: `easeOut(quad)`

## Narration Sync
> "You don't patch socks because socks got cheap. The economics made patching irrational."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <Background color="#E8E4DF" />

  {/* Person figure */}
  <GeometricPerson position={[960, 580]}>
    <Sequence from={20}>
      <HeadTilt degrees={5} durationInFrames={20} />
    </Sequence>
    <Sequence from={100}>
      <WalkRight distance={340} durationInFrames={30} />
    </Sequence>
    <Sequence from={160}>
      <IdleBreathe cycleFrames={50} scaleRange={[1.0, 1.01]} />
    </Sequence>
  </GeometricPerson>

  {/* Holey Sock with highlight */}
  <Sequence from={0} durationInFrames={100}>
    <HoleySock position={[960, 630]} sockColor="#8B7355" holeColor="#E8E4DF">
      <Sequence from={20}>
        <HoleHighlightPulse color="#EF4444" maxOpacity={0.4} durationInFrames={20} />
      </Sequence>
    </HoleySock>
  </Sequence>

  {/* Sock Toss — arc off-screen left */}
  <Sequence from={60}>
    <ParabolicToss
      startPos={[960, 630]}
      endPos={[100, 400]}
      rotation={270}
      fadeOut={true}
      durationInFrames={40}
    />
  </Sequence>

  {/* Shelf and Fresh Sock */}
  <ShelfLine y={740} xRange={[1150, 1450]} color="#94A3B8" />
  <Sequence from={130}>
    <FreshSockPull
      position={[1300, 700]}
      sockColor="#FFFFFF"
      glowColor="#4A90D9"
      glowOpacity={0.15}
      durationInFrames={30}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "person": {
    "headColor": "#64748B",
    "torsoColor": "#475569",
    "legsColor": "#334155",
    "position": [960, 580]
  },
  "holeySock": {
    "color": "#8B7355",
    "holeHighlight": "#EF4444",
    "position": [960, 630]
  },
  "toss": {
    "startPos": [960, 630],
    "endPos": [100, 400],
    "rotation": 270,
    "fadeOut": true
  },
  "freshSock": {
    "color": "#FFFFFF",
    "borderColor": "#E2E8F0",
    "glowColor": "#4A90D9",
    "glowOpacity": 0.15,
    "shelfPosition": [1300, 700]
  },
  "shelf": {
    "y": 740,
    "xRange": [1150, 1450],
    "color": "#94A3B8"
  },
  "backgroundColor": "#E8E4DF"
}
```

---
