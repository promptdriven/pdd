[veo:]

# Section 0.4: Developer Codebase Zoom-Out — Cold Open Accumulation Reveal

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 0:06 - 0:14

## Visual Description

The developer from spec 02 continues at their workstation, but the camera begins pulling back to reveal the wider context. As we zoom out, the single monitor becomes one of many. Code is visible on multiple screens — diffs, PRs, terminal windows, TODO markers. The visual shifts from "productive individual completing a clean edit" to "one person swimming in a sea of accumulated patches." The codebase is massive. Files everywhere. Diff markers. The weight of all that careful repair work is visible.

### Veo Prompt
```
Wide dolly-back shot revealing a software developer at their workstation as part of a large open-plan tech office. Camera pulls back steadily from medium shot to wide. Multiple monitors visible showing code editors, terminal windows, and diff views with highlighted changes. Cool blue-white overhead lighting. The developer is now a small figure surrounded by screens full of code. Modern tech office aesthetic. Cinematic 4K, steady smooth dolly-back movement, the mood shifts from focused productivity to systemic overwhelm.
```

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Framing: Starts medium, pulls to wide
- Color temperature: Cool blue-white, increasingly clinical at wide angle
- Depth of field: Deepens as camera pulls back

### Animation Sequence
1. **0-3s:** Camera starts medium on developer, begins pulling back.
2. **3-6s:** More of the office revealed. Multiple screens with code, diffs, TODO comments visible.
3. **6-8s:** Wide shot. Developer is a small figure among many workstations and screens.

### Typography
- None — cinematic B-roll. (Floating code comments may be composited as Remotion overlays.)

### Easing
- N/A (live-action footage)

## Narration Sync
> "But here's what your great-grandmother could have told you about that."

Segment: `cold_open_003`

- **9.42s**: Zoom-out in progress — "But here's what your great-grandmother"
- **13.46s**: Wide shot established, accumulated patches visible

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "developer_codebase_zoomout_co",
  "durationSeconds": 8,
  "usedIn": "01_split_developer_grandmother (left panel)",
  "camera": {
    "framing": "medium_to_wide",
    "movement": "dolly_back",
    "dof": "deepening",
    "angle": "eye_level"
  },
  "characters": [
    {
      "id": "developer_protagonist",
      "label": "Developer",
      "referencePrompt": "Software developer, early 30s, focused expression, modern office setting, cool monitor glow on face"
    }
  ]
}
```

---
