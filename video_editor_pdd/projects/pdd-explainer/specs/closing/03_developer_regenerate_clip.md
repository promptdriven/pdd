[veo:]

# Section 7.3: Developer Regenerate Clip — Adding a Test, Not a Patch

**Tool:** Veo
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 0:03 - 0:07

## Visual Description

Over-the-shoulder shot of a developer at a modern workstation. The screen is visible but slightly out of focus — what's important is the *gesture*. The developer's hands hover over the keyboard, they glance at the screen (where a code error is implied), then their hands move deliberately — not scrolling to a buggy line, but typing at the bottom of the file (adding a test). A sense of calm confidence: this person knows the workflow.

This clip provides the human anchor for the Remotion code animation in spec 02. It plays underneath or intercut with the code workflow.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Modern office / home office, dim ambient light with monitor glow
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Over-the-shoulder (OTS), medium shot — developer's back/shoulder in foreground, monitor visible
- Movement: static with subtle drift, 1-2px — observational
- Depth of field: shallow, f/2.0 — hands sharp, screen slightly soft, background very soft
- Focus pull: none

**Lighting**
- Key light: monitor glow, blue-white `#B0C4DE`, from front
- Fill: dim ambient room light, warm `#2A1F14`
- Overall tone: cool-neutral with warm ambient edges

**Subject**
- Developer from behind, seated at desk
- Mechanical keyboard visible
- Single monitor with code on screen (soft focus)
- Hands moving with purpose — typing at bottom of visible code

### Animation Sequence
1. **Frame 0-10 (0-0.3s):** Fade in. Developer seated, hands resting near keyboard.
2. **Frame 10-90 (0.3-3s):** Hands move to keyboard and begin typing deliberately. The gesture reads as "adding something new" — typing at the bottom of the file, not scrolling to find a bug.
3. **Frame 90-120 (3-4s):** Hold on typing. Gentle fade out.

### Typography
- None (pure B-roll footage)

### Easing
- Fade-in: `easeOut(quad)`, 0.3s
- Fade-out: `easeIn(quad)`, 1s

### Veo Prompt

```
Over-the-shoulder medium shot of a developer seated at a modern workstation with a single monitor showing code. The developer's hands move from resting position to keyboard and begin typing deliberately near the bottom of the file on screen. Mechanical keyboard visible. Dim ambient room lighting with monitor glow as key light, blue-white tones on face and hands. Shallow depth of field, f/2.0 — hands and keyboard sharp, screen slightly soft. Static camera with minimal drift. Calm, confident gesture. Modern home office setting. Cinematic, 24fps.
```

## Narration Sync
> "Code just got that cheap."

Segment: `closing_001` (tail) → `closing_002` (start)

- **0:03** ("Code"): Fade in, developer visible
- **0:05** ("just got that cheap"): Hands typing — adding a test, not patching
- **0:07** (hold): Fade out

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <VeoClip
    clipId="code_regenerate_closing"
    src="/clips/code_regenerate_closing.mp4"
    fit="cover"
  />
  <Sequence from={0} durationInFrames={10}>
    <FadeIn />
  </Sequence>
  <Sequence from={90} durationInFrames={30}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "code_regenerate_closing",
  "camera": {
    "framing": "over_the_shoulder",
    "movement": "static_with_drift",
    "dof": "shallow",
    "drift": true
  },
  "lighting": {
    "key": { "color": "#B0C4DE", "position": "front", "type": "monitor_glow" },
    "fill": { "color": "#2A1F14", "type": "ambient" },
    "grade": "cool_neutral"
  },
  "characters": [
    {
      "id": "developer_protagonist",
      "label": "Developer",
      "referencePrompt": "Developer seated at modern workstation, seen from behind, mechanical keyboard, monitor glow lighting"
    }
  ],
  "narrationSegments": ["closing_001", "closing_002"]
}
```

---
