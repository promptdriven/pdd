[veo:]

# Section 0.4: Sock Toss — Economics in Action

**Tool:** Veo
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:15 - 0:20

## Visual Description

Hard cut to modern day. A person in a bright, clean apartment notices a hole in their sock. No ceremony — they shrug, toss it casually into a trash can, and grab a fresh pair from a cellophane-wrapped multi-pack on a nearby shelf. The price sticker "$4.99" is briefly visible on the packaging.

The lighting is flat and modern — overhead LEDs, neutral white. The apartment is clean, contemporary, unremarkable. This isn't cinematic drama — it's Tuesday morning. The gesture is completely reflexive. The person doesn't consider darning for even a fraction of a second. The sock is garbage the instant the hole appears.

The camera is static and observational — locked-off, no movement, no style. Documentary feel. The banality is the point: this is what rational economic behavior looks like when materials get cheap enough.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Modern apartment interior, neutral daylight
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Medium shot (waist up), person seated on couch or bed edge
- Movement: static, locked-off tripod — observational, no drift
- Depth of field: moderate, f/4.0 — subject sharp, background recognizable but soft
- Angle: eye level, straight on

**Lighting**
- Key light: neutral white overhead LED `#F0ECE4`, diffused
- Fill: window ambient from the side, cool daylight `#D4E0EC`
- No dramatic shadows — flat, modern, everyday
- Overall tone: clean, slightly cool, naturalistic

**Subject**
- Person seated, casual clothing (t-shirt, shorts/sweats)
- Sock with a visible hole in the toe — simple cotton ankle sock, white or gray
- Small waste bin nearby
- Multi-pack of socks on a shelf or nightstand — cellophane-wrapped, "$4.99" sticker visible
- The person's expression: brief glance at hole, shrug, toss — zero hesitation

**Key Moments**
- 0-1s: Person pulls on sock, notices hole. Thumb pokes through.
- 1-2.5s: Shrug. Sock tossed casually toward trash can. Lands softly.
- 2.5-4s: Hand reaches to shelf, grabs multi-pack, tears open cellophane, pulls out fresh pair.
- 4-5s: Fresh socks held briefly. Already moving on. The old sock is forgotten.

### Animation Sequence
1. **Frame 0-5 (0-0.17s):** Hard cut in — no fade. Immediate presence. Modern apartment.
2. **Frame 5-30 (0.17-1s):** Person holds sock, notices hole, thumb pushes through.
3. **Frame 30-75 (1-2.5s):** Shrug. Sock tossed toward trash. Lands. Zero ceremony.
4. **Frame 75-120 (2.5-4s):** Hand reaches for multi-pack. Cellophane tears. Fresh pair pulled out. "$4.99" visible.
5. **Frame 120-150 (4-5s):** Fresh socks in hand. Hold. Person already moving on to next thing.

### Typography
- None (pure B-roll footage)

### Easing
- Hard cut in (no fade)
- Fade-out: `easeIn(quad)`, 0.33s

### Veo Prompt

```
Medium shot of a person in casual clothes sitting on the edge of a modern bed or couch. They pull on a white cotton ankle sock, notice a hole in the toe, poke their thumb through it. They shrug casually, toss the sock into a small trash can nearby. Hand reaches to a shelf and grabs a cellophane-wrapped multi-pack of socks with a visible $4.99 price sticker. They tear open the packaging and pull out a fresh pair. Modern apartment interior, neutral white overhead LED lighting, clean and contemporary. Static locked-off camera at eye level, no movement. Moderate depth of field. Naturalistic, everyday, documentary feel. No drama. Cinematic, 24fps, neutral color grade.
```

## Narration Sync

> "When socks got cheap enough... she stopped."

Segment: `cold_open_003`
Timing: 0:15 - 0:20

- **0:15** ("When socks got"): Person notices hole, thumb pokes through
- **0:17** ("cheap enough"): Sock tossed in trash, "$4.99" multi-pack visible
- **0:19** ("she stopped"): Fresh pair in hand, old sock forgotten

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={150}>
  <VeoClip
    clipId="modern_sock_toss"
    src="/clips/modern_sock_toss.mp4"
    fit="cover"
  />
  {/* Hard cut in — no fade */}
  {/* Fade out */}
  <Sequence from={140} durationInFrames={10}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points JSON

```json
{
  "type": "veo_clip",
  "clipId": "modern_sock_toss",
  "camera": {
    "framing": "medium_shot",
    "movement": "static",
    "dof": "moderate",
    "angle": "eye_level",
    "drift": false
  },
  "lighting": {
    "key": { "color": "#F0ECE4", "position": "overhead", "type": "LED" },
    "fill": { "color": "#D4E0EC", "position": "side_window", "type": "daylight" },
    "grade": "neutral_cool"
  },
  "props": {
    "sock": "white cotton ankle sock with hole in toe",
    "multiPack": "cellophane-wrapped, $4.99 sticker visible",
    "trashCan": "small modern waste bin"
  },
  "narrationSegments": ["cold_open_003"],
  "narrationTimingSeconds": { "start": 15.0, "end": 20.0 }
}
```

---
