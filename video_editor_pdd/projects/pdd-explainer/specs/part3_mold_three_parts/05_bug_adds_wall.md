[veo:]

# Section 3.5: Bug Adds Wall — The Developer's Terminal Moment

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 13:41 - 13:49

## Visual Description

A cinematic close-up of a developer's workstation. The screen shows a terminal with red error output — a bug has been discovered. The developer's hands are visible at the keyboard, lit by the cool blue glow of the monitor in an otherwise dim room. The atmosphere is focused, not panicked — this is a practiced workflow.

The developer types a command. The terminal clears the error and shows a new output: a test being written. The screen shifts from red error text to green test output. The camera slowly pushes in on the terminal screen, the red-to-green transition visible in the reflection on the developer's glasses.

This is the pivotal PDD workflow moment: instead of patching code, you add a wall. The cinematic treatment elevates a terminal interaction into something that feels consequential. The warm amber desk lamp in the background provides a subtle callback to the injection mold's wall color.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dim developer office, single monitor as primary light source
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Medium close-up (MCU) — developer's hands, keyboard, and monitor visible
- Push-in: subtle, ~8% zoom over 8 seconds, ending on terminal text
- Depth of field: moderate, f/2.8 equivalent — monitor sharp, background soft
- Rack focus: at 4s mark, focus shifts from hands to screen content

**Lighting**
- Key light: cool blue #4A90D9 from monitor, casting onto hands and keyboard
- Transition: monitor shifts from red #EF4444 tones to green #5AAA6E tones at midpoint
- Fill: warm amber #D9944A from desk lamp, background right — very subtle, practical
- Rim: faint blue edge light on developer's shoulders from second monitor (off-screen)
- Overall tone: high contrast, moody, cinematic

**Terminal Content (visible on screen)**
- First half: red error text, traceback visible, "BUG" or "FAILED" prominent
- Second half: green text, "Creating failing test...", "Test written", checkmark
- Command visible: `pdd bug user_parser`

**Subject**
- Developer: mid-30s, focused expression, dark hoodie
- Keyboard: mechanical, backlit keys (subtle)
- Desk: minimal, one amber desk lamp, dark surface

### Animation Sequence
1. **Frame 0-30 (0-1s):** Shot fades in. Terminal shows red error output. Developer's hands rest on keyboard. Blue-red mixed light on face.
2. **Frame 30-90 (1-3s):** Developer begins typing. Keystrokes visible. Terminal scrolls. Command `pdd bug user_parser` entered.
3. **Frame 90-120 (3-4s):** Terminal clears. Brief pause. Camera rack-focuses to screen. Monitor light shifts from red to neutral.
4. **Frame 120-180 (4-6s):** New output appears: "Creating failing test..." in amber, then "Test wall added" in green. Monitor light shifts to green tones. Developer's hands relax.
5. **Frame 180-210 (6-7s):** Terminal shows `pdd fix user_parser` → "All tests passing ✓". Full green glow on developer's face.
6. **Frame 210-240 (7-8s):** Hold. Green terminal reflected in glasses. Amber desk lamp visible in background — the wall metaphor embodied. Fade begins at frame 230.

### Typography
- None (all text is diegetic — on the terminal screen within the footage)

### Easing
- Camera push-in: `linear` (smooth mechanical tracking)
- Rack focus: `easeInOut(cubic)`, 0.5s transition
- Fade-in: `easeOut(quad)`, 1s
- Fade-out: `easeIn(quad)`, 0.33s

### Veo Prompt

```
Medium close-up of a software developer at their workstation in a dim room. Monitor displays a terminal with red error text. The developer types on a mechanical keyboard. The terminal screen transitions from red error output to green success output. Cool blue monitor light on the developer's face shifts from red-tinged to green-tinged. Shallow depth of field, rack focus from hands to screen. An amber desk lamp glows softly in the background right. Modern minimalist desk setup, dark hoodie, focused expression. Cinematic, moody lighting, high contrast, 24fps.
```

## Narration Sync
> "Now watch what happens when you find a bug... you don't patch the code. You add a wall."
> "That wall is permanent. That bug can never occur again — not in this generation, not in any future generation."

Segment: `part3_005`

- **13:41** ("Now watch what happens when you find a bug"): Developer sees red error
- **13:44** ("you don't patch the code"): Developer types `pdd bug` command
- **13:46** ("You add a wall"): Terminal shifts to green, test added
- **13:48** ("That wall is permanent"): Hold on green success, amber lamp visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="bug_adds_wall"
    src="/clips/bug_adds_wall.mp4"
    fit="cover"
  />
  {/* Fade in */}
  <Sequence from={0} durationInFrames={30}>
    <FadeIn />
  </Sequence>
  {/* Fade out */}
  <Sequence from={230} durationInFrames={10}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "bug_adds_wall",
  "characters": [
    {
      "id": "developer",
      "label": "Developer",
      "referencePrompt": "Mid-30s software developer, dark hoodie, focused expression, mechanical keyboard, minimalist desk, dim room lit by monitor glow"
    }
  ],
  "camera": {
    "framing": "medium_close_up",
    "movement": "push_in",
    "zoomPercent": 8,
    "dof": "moderate",
    "rackFocus": true
  },
  "lighting": {
    "key": { "color": "#4A90D9", "position": "front", "type": "monitor_glow" },
    "transition": { "from": "#EF4444", "to": "#5AAA6E", "trigger": "midpoint" },
    "fill": { "color": "#D9944A", "position": "background_right", "type": "desk_lamp" }
  },
  "narrationSegments": ["part3_005"],
  "narrationTimingSeconds": { "start": 41.0, "end": 49.0 }
}
```

---
