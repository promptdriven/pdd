[veo:part2_paradigm_shift_veo_04] Prompt-to-Code Generation Flow — The Modern Mold

# Section 2.8: Veo Background — Prompt Transforms into Code

**Tool:** Veo
**Duration:** ~30s (Act E)
**Timestamp:** 2:45 - 3:15

## Visual Description
A cinematic visualization of the PDD paradigm connection. The shot opens on a single line of glowing prompt text floating in a dark void — clean, luminous white characters on black, representing a natural language specification. The text begins to fragment: individual words and phrases break apart, dissolving into streams of luminous code tokens — curly braces, function keywords, variable names — flowing downward and rightward like a waterfall of light. The code tokens arrange themselves into structured blocks, indented and formatted, glowing in cool blue. From the edges of the code blocks, thin barrier lines extend outward — test assertions rendered as glowing green constraint walls, locking the behavior in place. The final frame shows the complete triad: prompt above (golden glow), code in the middle (blue), test barriers on the edges (green) — the modern "mold, plastic, and quality checks."

## Technical Specifications

### Canvas
- Resolution: 3840x2160 (4K), downscaled to 1920x1080 for composition
- Aspect ratio: 16:9
- Output: `veo/part2_paradigm_shift_veo_04.mp4`
- Frame chain: crossfade from `veo/part2_paradigm_shift_veo_03.mp4`

### Visual Elements
- Environment: pure dark void (#000000 → #0F172A)
- Prompt text: single line of natural language, luminous white/gold (#FBBF24)
  - Example: "Create a user authentication service with JWT tokens"
  - Monospaced font rendering, floating at top third
- Code fragments: streaming tokens in cool blue (#3B82F6 → #60A5FA)
  - Curly braces, keywords (function, return, const), variable names
  - Particle-like behavior — each token follows a gravity-like path
- Code blocks: structured indented code in center frame
  - Syntax coloring: keywords blue, strings green, brackets white
  - Glow effect on each block border
- Test barriers: green (#22C55E) geometric lines extending from code edges
  - Styled as constraint walls / guardrails
  - Subtle pulse animation suggesting active enforcement
- Color coding triad:
  - Prompt (top): #FBBF24 → #F97316 (golden/orange = mold)
  - Code (center): #3B82F6 → #60A5FA (blue = plastic)
  - Tests (edges): #22C55E → #4ADE80 (green = quality check)

### Camera Motion
- Phase 1 (0-10s): Static, centered on prompt text
- Phase 2 (10-22s): Slow crane-down following code waterfall
- Phase 3 (22-30s): Pull-back to reveal complete triad, slight push-in to center
- Final frame: hold with gentle floating motion

### Veo Prompt
```
Cinematic 4K visualization in pure dark void. A single line of glowing golden text
(natural language prompt) floats at top. Text fragments dissolve into streams of blue
luminous code tokens flowing downward like a code waterfall. Tokens arrange into
structured blue code blocks with syntax coloring. Green geometric barrier lines extend
from code edges as test constraints. Final composition: golden prompt above, blue code
center, green test barriers at edges. Abstract, clean, futuristic. Camera follows the
flow downward then pulls back. 16:9, film grain, shallow DOF. No real text overlays.
```

### Color Grading
- Shadows: pure black with navy lift
- Midtones: neutral, clean
- Highlights: warm gold (prompt), cool blue (code), vivid green (tests)
- Film grain: minimal, clean digital aesthetic
- Bloom: moderate on text elements

## Narration Sync
> "The prompt is your mold. Code is plastic. Tests lock the behavior. We've seen this before — we just didn't recognize it."

Prompt glows on "the prompt is your mold." Code waterfall flows on "code is plastic." Test barriers appear on "tests lock the behavior." Pull-back reveals full triad on "we've seen this before."

## Composition Notes
- **Background layer** for Act E
- Crossfade from 06_veo_chip_design (20 frames)
- Prompt-mold visualization overlay (10_prompt_mold_visualization.md) composited on top
- Fade-out to black at end (30 frames) — section close
- Subtitle track (11_subtitle_track.md) runs over entire duration

## Data Points
```json
{
  "output": "veo/part2_paradigm_shift_veo_04.mp4",
  "duration_seconds": 30,
  "total_frames_at_30fps": 900,
  "camera_motion": "static_to_crane_down_to_pullback",
  "shot_type": "abstract_visualization",
  "triad_colors": {
    "prompt": "#FBBF24",
    "code": "#3B82F6",
    "tests": "#22C55E"
  },
  "phases": [
    {"name": "prompt_display", "start": "0:00", "end": "0:10", "camera": "static"},
    {"name": "code_waterfall", "start": "0:10", "end": "0:22", "camera": "crane_down"},
    {"name": "triad_reveal", "start": "0:22", "end": "0:30", "camera": "pullback"}
  ],
  "usage_windows": [
    {"act": "E", "start": "2:45", "end": "3:15"}
  ]
}
```

---
