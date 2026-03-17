[veo:]

# Section 7.2: Sock Discard — The Final Toss

**Tool:** Veo
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 24:15 - 24:21

## Visual Description

A tight cinematic shot of someone discovering a hole in their sock, shrugging, and tossing it casually into a waste bin. They reach over and pull a fresh pair from a multi-pack sitting on a shelf. The gesture is completely casual — no hesitation, no sentimentality. This is the modern reality: socks are disposable.

The lighting is warm and neutral — modern domestic, not the grandmother's dramatic amber lamplight. Clean, matter-of-fact. The camera is static, observational. The entire action reads as utterly ordinary, which is the point: discarding has become so natural that it's unremarkable.

This clip is embedded within the left panel of 01_sock_callback_split.md.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Modern domestic interior, neutral warm lighting
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Close-up (CU) on hands, sock, and waste bin
- Movement: static, locked-off tripod — observational, not cinematic
- Depth of field: moderate, f/2.8 — hands sharp, background soft
- No drift, no push-in — pure observation

**Lighting**
- Key light: warm neutral #E8D5B8, soft overhead — modern household
- Fill: ambient room light, balanced
- No dramatic shadows — this is everyday life, not art
- Overall tone: clean, slightly warm, naturalistic

**Subject**
- Person's hands holding a sock with a visible hole in the toe
- Waste bin nearby — simple, modern
- Multi-pack of socks on a shelf or counter
- The hands are modern — no weathering, no age markers

**Key Moments**
- 0-1.5s: Hands hold sock, thumb pokes through hole — a brief examination
- 1.5-3s: Shrug. Sock tossed casually into waste bin
- 3-5s: Hand reaches to shelf, pulls fresh pair from multi-pack
- 5-6s: Fresh socks held — clean, new. Hold

### Animation Sequence

1. **Frame 0-45 (0-1.5s):** Shot opens on hands holding sock. Thumb pushes through the hole. Brief assessment.
2. **Frame 45-90 (1.5-3s):** Sock tossed into waste bin. Casual, no ceremony. The sock lands with a soft thump.
3. **Frame 90-150 (3-5s):** Hand reaches to a nearby shelf. Pulls a fresh pair from a plastic-wrapped multi-pack.
4. **Frame 150-180 (5-6s):** Fresh socks in hand. Hold. The old sock is already forgotten.

### Typography

- None (pure B-roll footage)

### Easing

- Fade-in: `easeOut(quad)`, 0.5s
- Fade-out: `easeIn(quad)`, 0.33s

### Veo Prompt

```
Close-up of a person's hands holding a wool sock with a visible hole in the toe. Thumb pushes through the hole. They shrug casually, toss the sock into a small waste bin nearby. Hand reaches to a shelf and pulls a fresh pair of socks from a plastic multi-pack. Hands hold the new socks. Modern domestic interior, clean warm lighting from overhead, neutral color palette. Static locked-off camera, no movement. Moderate depth of field, f/2.8. Naturalistic, everyday feel. No dramatic lighting. Cinematic, 24fps, clean color grade.
```

## Narration Sync

> "You don't patch socks because socks got cheap."

Segment: `closing_001a`
Timing: 24:15 - 24:21 (embedded in left panel of 01_sock_callback_split)

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={180}>
  <VeoClip
    clipId="sock_final_discard"
    src="/clips/sock_final_discard.mp4"
    fit="cover"
  />
  {/* Fade in */}
  <Sequence from={0} durationInFrames={15}>
    <FadeIn />
  </Sequence>
  {/* Fade out */}
  <Sequence from={170} durationInFrames={10}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points JSON

```json
{
  "type": "veo_clip",
  "clipId": "sock_final_discard",
  "camera": {
    "framing": "close_up",
    "movement": "static",
    "dof": "moderate",
    "drift": false
  },
  "lighting": {
    "key": { "color": "#E8D5B8", "position": "overhead", "type": "household" },
    "fill": "ambient",
    "grade": "warm_neutral"
  },
  "embeddedIn": "01_sock_callback_split",
  "panel": "left",
  "narrationSegments": ["closing_001a"],
  "narrationTimingSeconds": { "start": 1455.0, "end": 1461.0 }
}
```

---
