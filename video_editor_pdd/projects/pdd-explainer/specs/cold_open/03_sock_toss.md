[Remotion]

# Section 0.3: Sock Toss — Economics Punch

**Tool:** Remotion
**Duration:** ~3s (90 frames @ 30fps)
**Timestamp:** 0:11 - 0:14

## Visual Description

Hard cut from the split screen to a clean, modern scene. A stylized hand holds a sock with a visible hole. The hand shrugs (slight rotation), then tosses the sock in a gentle arc toward a trash bin. The sock lands with a soft visual "puff." The hand reaches to the right and grabs a fresh pair from a multi-pack — cellophane wrapper glinting briefly.

The scene is rendered in a clean, flat illustration style with a warm modern interior palette. Minimal detail — just enough to read the action. The sock's hole is circled with a subtle dashed red line that disappears as it's tossed. The fresh pair is pristine white with a tiny price tag: "$4.99 / 6-pack."

This is the punchline visual — deadpan, casual, matter-of-fact. The economics speak for themselves.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #F5F0EB (warm off-white, modern interior)
- No grid lines

### Chart/Visual Elements

**Holey Sock**
- Sock shape: simplified silhouette, fill #E8DDD0 (oatmeal)
- Hole: circular cutout ~20px diameter, outlined with dashed red circle #EF4444, 1px dash
- Position: center frame at start (960, 500)

**Hand (stylized)**
- Flat illustration, fill #D4A88C (skin tone), simplified fingers
- Shrug rotation: 8° clockwise then back
- Toss arc: cubic bezier from (960, 500) to (1400, 700)

**Trash Bin**
- Simple cylinder, fill #94A3B8 (slate), 80×100px
- Position: (1400, 750)
- "Puff" particle effect: 6 small circles #D1D5DB, scale 0 → 1 → 0, scattered from landing point

**Fresh Pair**
- Pristine white socks #FFFFFF with subtle shadow
- Cellophane wrapper: #E0F2FE at 40% opacity, small glint animation
- Position: slides in from right (1920, 400) to (960, 500)
- Price tag: "$4.99 / 6-pack" in #64748B, 12px

### Animation Sequence
1. **Frame 0-5 (0-0.17s):** Hard cut in. Hand holding holey sock appears immediately (no fade).
2. **Frame 5-15 (0.17-0.5s):** Dashed red circle pulses once around the hole. Hand does a slight shrug rotation (8° CW then back).
3. **Frame 15-35 (0.5-1.17s):** Toss animation. Sock follows bezier arc to trash bin. Sock rotates 180° during flight. Red dashed circle fades out mid-flight.
4. **Frame 35-45 (1.17-1.5s):** Sock lands in bin. Puff particles expand and fade. Soft visual impact.
5. **Frame 45-70 (1.5-2.33s):** Hand reaches right. Fresh pair slides in from right edge. Cellophane glints once.
6. **Frame 70-90 (2.33-3.0s):** Hand holds fresh pair in center. Price tag fades in below. Hold.

### Typography
- Price tag: `Inter`, 12px, #64748B, opacity 0.7

### Easing
- Shrug rotation: `easeInOut(sin)`
- Sock toss arc: `easeOut(quad)` (natural gravity feel)
- Sock rotation during flight: `linear`
- Puff particles: `easeOut(cubic)`
- Fresh pair slide-in: `easeOut(back(1.2))`
- Price tag fade: `easeOut(quad)`

## Narration Sync
> "When socks got cheap enough... she stopped."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <ModernBackground color="#F5F0EB" />
  <Sequence from={0} durationInFrames={45}>
    <StylizedHand action="hold">
      <HoleySock holeSize={20} outlineColor="#EF4444" />
    </StylizedHand>
    <Sequence from={5} durationInFrames={10}>
      <HolePulse color="#EF4444" />
    </Sequence>
    <Sequence from={15} durationInFrames={20}>
      <TossArc
        from={[960, 500]}
        to={[1400, 700]}
        rotation={180}
      />
    </Sequence>
    <Sequence from={35} durationInFrames={10}>
      <TrashBin position={[1400, 750]} />
      <PuffParticles count={6} color="#D1D5DB" />
    </Sequence>
  </Sequence>
  <Sequence from={45} durationInFrames={45}>
    <StylizedHand action="grab">
      <FreshSockPair color="#FFFFFF" wrapperGlint={true} />
    </StylizedHand>
    <Sequence from={25} durationInFrames={20}>
      <PriceTag text="$4.99 / 6-pack" color="#64748B" />
    </Sequence>
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "background": "#F5F0EB",
  "holeySock": {
    "fillColor": "#E8DDD0",
    "holeSize": 20,
    "outlineColor": "#EF4444",
    "outlineDash": [4, 3],
    "startPosition": [960, 500]
  },
  "hand": {
    "fillColor": "#D4A88C",
    "shrugAngle": 8
  },
  "toss": {
    "bezierFrom": [960, 500],
    "bezierTo": [1400, 700],
    "sockRotation": 180
  },
  "trashBin": {
    "fillColor": "#94A3B8",
    "size": [80, 100],
    "position": [1400, 750]
  },
  "puff": {
    "particleCount": 6,
    "particleColor": "#D1D5DB"
  },
  "freshPair": {
    "color": "#FFFFFF",
    "wrapperColor": "#E0F2FE",
    "wrapperOpacity": 0.4,
    "slideFrom": [1920, 400],
    "slideTo": [960, 500]
  },
  "priceTag": {
    "text": "$4.99 / 6-pack",
    "color": "#64748B",
    "fontSize": 12
  },
  "narrationSegments": ["cold_open_004"],
  "narrationTimingSeconds": { "start": 11.46, "end": 13.94 }
}
```

---
