[veo:]

# Section 7.1: Sock Callback — Discard and Replace

**Tool:** Veo
**Duration:** ~3s (78 frames @ 30fps)
**Timestamp:** 0:00 - 0:03

## Visual Description

The sock metaphor returns one final time as a bookend. A pair of hands holds up a worn-out sock with a visible hole in the heel. The person considers it briefly — then drops it into a wastebasket and picks up a fresh, identical sock from a neat stack. The gesture is casual, decisive. No hesitation. The economics have already been internalized.

The scene is modern — clean countertop, natural daylight, everyday domestic setting. This is not the 1950s grandmother darning scene; this is the present day.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Modern domestic interior, natural daylight
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Medium close-up (MCU) — hands, sock, wastebasket edge, fresh sock stack
- Movement: static, locked-off — clean, observational
- Depth of field: moderate, f/2.8 — hands and socks sharp, background soft
- No drift

**Lighting**
- Key light: cool natural daylight from window, upper-right
- Fill: ambient room light — soft, even
- Overall tone: neutral-cool, modern, everyday

**Subject**
- Person's hands holding a worn sock with visible hole
- Small wastebasket at frame edge
- Stack of fresh identical socks nearby
- Clean modern surface (countertop or table)

### Animation Sequence
1. **Frame 0-10 (0-0.3s):** Fade in. Hands holding holey sock, examining it.
2. **Frame 10-50 (0.3-1.7s):** Person drops sock into wastebasket. Hand reaches for fresh sock from stack.
3. **Frame 50-78 (1.7-2.6s):** Hand picks up fresh sock. Brief hold. Begin fade out.

### Typography
- None (pure B-roll footage)

### Easing
- Fade-in: `easeOut(quad)`, 0.3s
- Fade-out: `easeIn(quad)`, 0.3s

### Veo Prompt

```
Medium close-up of a person's hands holding a worn sock with a visible hole in the heel. The person examines it briefly, then drops it into a small wastebasket below frame. Hand reaches to a neat stack of fresh identical socks and picks one up. Modern domestic interior with clean countertop surface. Natural daylight from a window at upper-right. Neutral cool tones. Static locked-off camera. Shallow depth of field, f/2.8. Casual, decisive gesture — no hesitation. Cinematic, 24fps.
```

## Narration Sync
> "You don't patch socks because socks got cheap. The economics made patching irrational."

Segment: `closing_001`

- **0:00** ("You don't patch socks"): Fade in on hands examining holey sock
- **0:01** ("socks got cheap"): Sock drops into wastebasket, hand reaches for fresh one
- **0:02** ("economics made patching irrational"): Fresh sock picked up, hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={78}>
  <VeoClip
    clipId="sock_callback_discard"
    src="/clips/sock_callback_discard.mp4"
    fit="cover"
  />
  <Sequence from={0} durationInFrames={10}>
    <FadeIn />
  </Sequence>
  <Sequence from={68} durationInFrames={10}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "sock_callback_discard",
  "camera": {
    "framing": "medium_close_up",
    "movement": "static",
    "dof": "moderate",
    "drift": false
  },
  "lighting": {
    "key": { "color": "natural_daylight", "position": "upper_right", "type": "window" },
    "fill": "ambient",
    "grade": "neutral_cool"
  },
  "callbackTo": "part1_economics/sock_metaphor",
  "narrationSegments": ["closing_001"]
}
```

---
