[veo:]

# Section 7.2: Developer Regenerates Instead of Patching

**Tool:** Veo
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 0:02 - 0:06

## Visual Description

A developer sits at a modern workstation. On screen, code with a visible bug is highlighted in a dark-themed editor. Rather than opening the file and manually editing the line, the developer's hands move to the terminal. The focus is on the screen: a terminal prompt appears, the developer types briefly, and the terminal shows the regeneration workflow completing. The moment captures the paradigm shift — the instinct is no longer to patch, but to regenerate.

The framing is over-the-shoulder, showing both the developer and the monitor. Cool blue-white monitor glow on the developer's face. The gesture is confident and unhesitating.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Framing: Over-the-shoulder, medium shot showing developer and monitor
- Color temperature: Cool (5500K), blue-white monitor glow
- Depth of field: Medium, f/4 — both developer and screen readable

### Veo Prompt

```
Over-the-shoulder shot of a software developer at a modern desk with an ultrawide monitor. The screen shows a dark-themed code editor with syntax-highlighted code. The developer's hands move confidently to the keyboard, typing a brief command in a terminal panel at the bottom of the screen. Cool blue-white monitor glow illuminates their face. Modern minimalist workspace, mechanical keyboard, single monitor setup. Cinematic 4K, shallow depth of field, cool color grade.
```

### Animation Sequence
1. **Frame 0-40 (0-1.3s):** Over-the-shoulder view, code visible on screen with a highlighted line
2. **Frame 40-80 (1.3-2.7s):** Developer's hands move to terminal, begin typing
3. **Frame 80-120 (2.7-4s):** Terminal shows command executing, developer leans back slightly

## Narration Sync
> "Encode intent. Tests preserve behavior."
> — closing_002 (2.14s – 7.58s, first half)

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "developer_regenerate_closing",
  "durationSeconds": 4,
  "narrationSegments": ["closing_002"],
  "characters": [
    {
      "id": "developer_protagonist",
      "label": "Developer",
      "referencePrompt": "A 30-something software developer, gender-neutral, wearing a dark henley shirt. Modern desk with mechanical keyboard and single ultrawide monitor. Cool blue-white lighting from LED desk lamp and monitor glow."
    }
  ]
}
```

---
