[Remotion]

# Section 0.4: The Sock Toss — When Cheap Enough, Stop

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 0:30 - 0:40

## Visual Description
Hard cut from the split screen to a single full-frame scene. A simplified, geometric modern-day person notices a hole in their sock (represented as a small circle cutout in a sock shape). They shrug (shoulders bob up then down), toss the sock into a trash bin (arc trajectory), and grab a fresh pair from a multi-pack on a shelf. The animation is minimal and clean — almost icon-like figures, no facial detail, flat colors. The tone is casual and deadpan, matching the narration.

The visual vocabulary shifts from warm/sepia grandmother tones to cool, modern neutrals — signaling the time jump.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Light neutral `#F0EDE8` (modern, clean)
- Grid lines: None

### Chart/Visual Elements
- **Person:** Simplified geometric figure — circle head `#64748B`, rectangle torso `#475569`, rectangle legs `#334155`. Centered at (960, 600). ~200px tall
- **Holey Sock:** Rounded rectangle `#8B7355` with a 12px circular cutout (hole) `#F0EDE8`. Held at hand level initially
- **Trash Bin:** Rounded trapezoid `#94A3B8` at (700, 850), 60px wide
- **Multi-Pack:** 3 sock shapes stacked in a box `#CBD5E1` on a shelf line at (1200, 750)
- **Fresh Sock Pair:** Two clean rounded rectangles `#FFFFFF` with subtle `#E2E8F0` border
- **Shelf:** Thin horizontal line `#94A3B8` at Y=780

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Hard cut in. Person and sock visible. Person "looks down" (head tilts 5deg toward sock)
2. **Frame 15-30 (0.5-1.0s):** Hole in sock becomes visible — a small red circle outline `#EF4444` pulses once around the cutout to draw attention
3. **Frame 30-50 (1.0-1.67s):** Shrug animation — shoulders (two small rectangles) translate Y: 0→-8→0 with a slight head tilt
4. **Frame 50-90 (1.67-3.0s):** Sock toss — sock follows a parabolic arc from hand (960, 650) to bin (700, 850). Sock rotates 180deg during flight. Subtle "crumple" squash on landing (scaleX: 1→1.3→1, scaleY: 1→0.7→0)
5. **Frame 90-120 (3.0-4.0s):** Person walks right (translateX +240px, legs alternate). Reaches toward multi-pack
6. **Frame 120-150 (4.0-5.0s):** Hand pulls fresh sock pair from multi-pack. Clean white socks glow slightly
7. **Frame 150-180 (5.0-6.0s):** Narration: "When socks got cheap enough... she stopped." Person holds fresh socks. Satisfied stillness
8. **Frame 180-300 (6.0-10.0s):** Hold on scene. Subtle idle animation (gentle breathing motion on torso, 40-frame cycle)

### Typography
- None in scene

### Easing
- Shrug: `easeInOut(quad)`
- Sock arc: `easeIn(quad)` for rise, `easeIn(cubic)` for fall (gravity feel)
- Sock rotation: `linear`
- Sock landing squash: `easeOut(elastic)` with damping
- Walk: `linear` translate, `easeInOut(sin)` leg alternation
- Fresh sock pull: `easeOut(quad)`

## Narration Sync
> "When socks got cheap enough... she stopped."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <Background color="#F0EDE8" />

  {/* Person figure */}
  <GeometricPerson position={[960, 600]}>
    <Sequence from={15}>
      <HeadTilt degrees={5} durationInFrames={15} />
    </Sequence>
    <Sequence from={30}>
      <ShrugAnimation durationInFrames={20} />
    </Sequence>
    <Sequence from={90}>
      <WalkRight distance={240} durationInFrames={30} />
    </Sequence>
  </GeometricPerson>

  {/* Holey Sock */}
  <Sequence from={0} durationInFrames={90}>
    <HoleySock position={[960, 650]} holeColor="#F0EDE8">
      <Sequence from={15}>
        <HoleHighlight color="#EF4444" />
      </Sequence>
    </HoleySock>
  </Sequence>

  {/* Sock Toss Arc */}
  <Sequence from={50}>
    <ParabolicToss
      startPos={[960, 650]}
      endPos={[700, 850]}
      rotation={180}
      durationInFrames={40}
    />
  </Sequence>

  {/* Trash Bin */}
  <TrashBin position={[700, 850]} color="#94A3B8" />

  {/* Multi-Pack and Fresh Socks */}
  <SockMultiPack position={[1200, 750]}>
    <Sequence from={120}>
      <PullFreshSock durationInFrames={30} />
    </Sequence>
  </SockMultiPack>
</Sequence>
```

## Data Points
```json
{
  "person": {
    "headColor": "#64748B",
    "torsoColor": "#475569",
    "legsColor": "#334155",
    "position": [960, 600]
  },
  "holeySock": {
    "color": "#8B7355",
    "holeHighlight": "#EF4444"
  },
  "toss": {
    "startPos": [960, 650],
    "endPos": [700, 850],
    "rotation": 180,
    "arcHeight": 150
  },
  "trashBin": {
    "color": "#94A3B8",
    "position": [700, 850]
  },
  "freshSocks": {
    "color": "#FFFFFF",
    "borderColor": "#E2E8F0",
    "packPosition": [1200, 750]
  },
  "backgroundColor": "#F0EDE8"
}
```

---
