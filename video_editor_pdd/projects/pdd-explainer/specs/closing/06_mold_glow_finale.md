[veo:]

# Section 7.6: Mold Glow Finale — The Mold Is What Matters

**Tool:** Veo
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 0:16 - 0:19

## Visual Description

Close-up of an injection mold in a dimly lit industrial setting. The mold glows with a warm amber-gold light emanating from within — the precision walls are the source of value. Beside it, a freshly ejected plastic part sits on the surface. The plastic part is present but unremarkable — matte, gray, utilitarian. The contrast is everything: the mold radiates importance, the output is forgettable.

Camera holds static. The glow pulses very gently — alive, valuable, permanent. The plastic part sits still — disposable, replaceable, cheap.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark industrial interior, low ambient light
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Close-up (CU) — mold filling 60% of frame, plastic part at edge
- Movement: static, locked-off — reverent, observational
- Depth of field: moderate, f/3.5 — mold sharp, background falls off
- No drift

**Lighting**
- Key light: warm amber-gold `#D4A043` emanating from within the mold (practical/motivated light)
- Fill: minimal ambient — industrial darkness
- Rim: subtle cool edge light `#60A5FA` at 0.1 on mold silhouette
- Plastic part: unlit, catching only ambient — deliberately unremarkable
- Overall tone: high contrast, warm-on-dark

**Subject**
- Precision injection mold — metal, detailed wall geometry visible
- Warm amber glow from within mold channels
- Plastic part: small, gray, matte, generic shape — sits to one side
- Industrial surface (steel table or conveyor edge)

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Fade in from black. Mold and plastic part establish.
2. **Frame 15-100 (0.5-3.3s):** Hold. Mold glows with gentle amber pulse (very slow, ~4s period). Plastic part sits unremarkably.
3. **Frame 100-120 (3.3-4s):** Hold continues. Begin subtle fade out.

### Typography
- None (pure B-roll footage)

### Easing
- Fade-in: `easeOut(quad)`, 0.5s
- Glow pulse: `easeInOut(sine)`, very slow continuous
- Fade-out: `easeIn(quad)`, 0.7s

### Veo Prompt

```
Close-up of a precision metal injection mold on a dark industrial surface. The mold glows with warm amber-gold light emanating from within its channels and wall geometry. Beside the mold, a small matte gray plastic part sits unremarkably — freshly ejected, utilitarian. High contrast lighting: the mold radiates warm amber light while the plastic part catches only minimal ambient light. Dark industrial background. Subtle cool rim light on mold silhouette. Static locked-off camera. Moderate depth of field, f/3.5. Reverent, observational composition. Cinematic, 24fps.
```

## Narration Sync
> "The code is just plastic."

Segment: `closing_004`

- **0:16** ("The code"): Mold visible, glowing. Plastic part present but unremarkable.
- **0:18** ("is just plastic"): Hold on contrast — glow vs matte.
- **0:19** (segment boundary): Begin fade.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <VeoClip
    clipId="mold_glow_finale"
    src="/clips/mold_glow_finale.mp4"
    fit="cover"
  />
  <Sequence from={0} durationInFrames={15}>
    <FadeIn />
  </Sequence>
  <Sequence from={100} durationInFrames={20}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "mold_glow_finale",
  "camera": {
    "framing": "close_up",
    "movement": "static",
    "dof": "moderate",
    "drift": false
  },
  "lighting": {
    "key": { "color": "#D4A043", "position": "internal", "type": "practical_glow" },
    "fill": "minimal",
    "rim": { "color": "#60A5FA", "opacity": 0.1 },
    "grade": "high_contrast_warm"
  },
  "callbackTo": "part2_injection_mold",
  "narrationSegments": ["closing_004"]
}
```

---
