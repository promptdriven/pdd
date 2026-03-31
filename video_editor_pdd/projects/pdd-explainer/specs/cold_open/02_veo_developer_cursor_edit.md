[veo:]

# Section 0.2: Developer AI-Assisted Edit — Companion Clip

**Tool:** Veo
**Duration:** ~14s
**Timestamp:** 0:00 - 0:13

## Visual Description

A developer at a modern desk, working in a Cursor-style AI code editor. The screen shows a code file with a glowing inline suggestion appearing — the developer accepts it, and a clean diff highlight shows the change landing. The shot begins as a medium close-up on the developer's hands and screen, then gradually pulls back to reveal the broader workspace: multiple monitors showing sprawling codebases, diff markers everywhere, TODO comments visible in sidebars. The zoom-out reveals the single edit was just one tiny patch in an enormous, heavily-maintained codebase.

### Veo Prompt
```
Medium close-up of a developer's hands typing at a modern keyboard, sleek monitor showing a dark-themed code editor with glowing inline AI code suggestion. Developer accepts the suggestion, green diff highlight appears. Clean modern desk setup with ambient RGB lighting. Cinematic shallow depth of field, cool blue-white monitor glow on face. 4K.
```

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Framing: Medium close-up on hands and monitor, pulling to wide
- Color temperature: Cool — monitor glow, modern office blues
- Depth of field: Shallow initially, deepening on zoom-out

### Animation Sequence
1. **0-5s:** Developer typing. Cursor interface visible. AI suggestion appears inline.
2. **5-8s:** Developer accepts edit. Green diff highlight. Clean code change.
3. **8-14s:** Camera holds on the completed edit. (Zoom-out effect handled by split container.)

### Typography
- None — cinematic B-roll. Used as left panel in split screen (spec 01).

### Easing
- N/A (live-action footage)

## Narration Sync
> "If you use Cursor, or Copilot, or Claude Code... you're getting really good at patching."

Segments: `cold_open_001`, `cold_open_002`

- **0.00s**: Developer begins typing, editor visible
- **4.62s**: "you're getting really good at patching" — edit lands cleanly
- **8.92s**: Hold on completed edit

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "developer_cursor_edit",
  "durationSeconds": 14,
  "usedIn": "01_split_screen_darning (left panel)",
  "characters": [
    {
      "id": "developer",
      "label": "Developer",
      "referencePrompt": "Young developer, late 20s, casual hoodie, modern desk setup with ultrawide monitor, dark-themed code editor, ambient RGB lighting"
    }
  ]
}
```

---
