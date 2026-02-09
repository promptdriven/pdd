# Audit: 01a Establish Split Screen

## Status: PASS

### Spec vs Implementation Comparison

**Spec file:** `specs/00-cold-open/01a_establish_split_screen.md`
**Implementation files:**
- `remotion/src/remotion/01-ColdOpen/ColdOpenSplitScreen.tsx` (Remotion fallback/animatic)
- `remotion/src/remotion/01-ColdOpen/LeftPanel.tsx` (left side procedural animation)
- `remotion/src/remotion/01-ColdOpen/RightPanel.tsx` (right side procedural animation)
- `remotion/src/remotion/01-ColdOpen/constants.ts` (timing and color definitions)
- `remotion/src/remotion/S00-ColdOpen/ColdOpenSection.tsx` (production version, loads `cold_open_01a_establish.mp4`)
- `remotion/src/remotion/S00-ColdOpen/constants.ts` (production timing, audio-synced beats)

### Requirements Met

- **Split screen layout with vertical white divider**: `ColdOpenSplitScreen.tsx` lines 33-72 implement left/right panels each at `width/2` with a 2px white divider (`COLORS.DIVIDER = "#ffffff"`) positioned at 50% with `translateX(-50%)`, plus a subtle `boxShadow: "0 0 10px rgba(255,255,255,0.3)"` glow. Matches spec requirement for "clean vertical white line divider in exact center of frame."
- **Color palette -- exact match**: `constants.ts` defines `LEFT_BG: "#1a1a2e"` (spec: `#1a1a2e`), `LEFT_ACCENT: "#4A90D9"` (spec: `#4A90D9`), `RIGHT_BG: "#2d2416"` (spec: `#2d2416`), `RIGHT_ACCENT: "#D9944A"` (spec: `#D9944A`). All four hex values are pixel-perfect matches.
- **Cool blue left / warm amber right contrast**: LeftPanel uses `#1a1a2e` background with blue accents; RightPanel uses `#2d2416` background with amber radial gradient glow (lines 348-358) simulating oil lamp ambience.
- **Code editor visible on left side**: `LeftPanel.tsx` lines 220-280 render a Cursor IDE mockup with macOS traffic light dots (red/yellow/green), filename in title bar, and syntax-highlighted code content with line numbers. During the establish phase (frame < syncStart, i.e., 0:00-0:08), the original code is shown statically (lines 272-279).
- **Oil lamp with animated flame on right side**: `RightPanel.tsx` lines 385-418 implement a detailed oil lamp SVG with glass chimney, oil reservoir, base, and a three-layer animated flame (gold/orange/red ellipses with `<animate>` on the `ry` attribute cycling every 0.5s). A radial gradient glow effect surrounds the lamp.
- **Wooden table surface**: `RightPanel.tsx` lines 370-383 render a table with wood grain texture via `backgroundImage: linear-gradient(90deg, ...)` and `backgroundSize: "20px 20px"`.
- **Sock with visible hole**: `WoolSock` component (RightPanel.tsx lines 38-185) renders a detailed side-view L-shaped wool sock SVG with ribbed cuff, heel reinforcement, toe area, wool texture pattern, and a prominently visible hole (dark ellipse at the heel/bottom area with frayed edges). The `holeProgress` prop controls darning animation.
- **Hands holding sock / needle ready**: RightPanel.tsx lines 420-459 render left hand silhouette (ellipse shapes, lines 430-440) holding the sock and right hand with needle (lines 447-459). The `NeedleAndThread` component (lines 188-216) renders a silver needle with eye, shaft, point, and trailing thread in amber.
- **Timing -- 8-second establish phase**: `constants.ts` defines `BEATS.ESTABLISH_START = 0`, `BEATS.ESTABLISH_END = 8` (8 seconds). The `secondsToFrames` helper converts at 60 fps. LeftPanel's `showOriginal` flag (line 201) ensures static display during this window. No animations trigger until `syncStart` (8s) on either panel.
- **Static camera during establish phase**: Neither panel applies zoom, translation, or camera movement transforms during frames 0 through `secondsToFrames(8)`. Scale is 1, translateY is 0, and no interpolation is active during this phase.
- **16:9 aspect ratio at 1080p**: `constants.ts` defines `COLD_OPEN_WIDTH = 1920`, `COLD_OPEN_HEIGHT = 1080` -- standard 16:9. Spec lists "4K / 1080p" indicating either is acceptable.
- **Production version uses Veo-generated video**: `S00-ColdOpen/ColdOpenSection.tsx` lines 34-44 load `cold_open_01a_establish.mp4` via Remotion's `OffthreadVideo` component with `loop` for VISUAL_00 (0-4.92s). This is the intended production path using actual AI-generated footage.

### Issues Found

- **No issues that require code changes.** The spec is a Veo video generation prompt describing photorealistic cinematic footage (detailed human faces, hands, shallow depth of field, etc.). The Remotion implementation in `01-ColdOpen/` faithfully serves as a procedural fallback/animatic, correctly implementing all structural and timing elements. The production path in `S00-ColdOpen/` correctly references the Veo-generated MP4.
- **Minor observations (not blocking):**
  - Left panel title bar shows `parser.ts` (LeftPanel.tsx line 242) while spec references Python code. This is a stylistic choice for the Remotion animatic that does not affect the production Veo video.
  - Grandmother's hands are simplified SVG ellipse silhouettes rather than photorealistic "weathered hands." Expected and appropriate for a code-based animation fallback.
  - Developer face/torso not rendered during establish phase in the animatic -- hands and silhouette appear only in later phases (satisfaction beat at 15s+). The production Veo video handles this.
  - Production timing (`S00-ColdOpen/constants.ts`) uses VISUAL_00 spanning 0-4.92s (not 8s) because the production narration pacing was adjusted to match actual audio timing from `cold_open_narration.wav`.

### Notes

- This spec is a Veo 3.1 video generation prompt, not a Remotion animation spec. The Remotion implementation in `01-ColdOpen/` is a procedural fallback/animatic that captures the core visual structure, layout, color palette, and timing.
- The production version in `S00-ColdOpen/ColdOpenSection.tsx` correctly loads the Veo-generated video file (`cold_open_01a_establish.mp4`) for the final render.
- All four color palette hex values from the spec are exactly matched in `constants.ts`.
- The split screen layout, center divider, cool/warm contrast, 8-second establish timing, and static camera behavior are all faithfully implemented in the animatic.
- The three-phase zoom-out easing system (ease-in, constant, ease-out) in both LeftPanel and RightPanel demonstrates careful engineering for later segments, but does not affect the 01a establish phase.
- Production constants use 30 fps (vs 60 fps in the animatic) and audio-synced timing derived from Whisper word timestamps. This is expected for the final production pipeline.
