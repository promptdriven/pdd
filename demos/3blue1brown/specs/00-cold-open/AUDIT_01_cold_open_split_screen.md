# Audit: Cold Open Split Screen

## Status: PASS

---

### Requirements Met

1. **Veo video assets exist and are referenced correctly**: Both required Veo assets are present in the public directory:
   - `remotion/public/cold_open_01a_establish.mp4` (3.7 MB) -- used for Visual 0 (the "establish" beat)
   - `remotion/public/cold_open_01f_modern_sock_toss.mp4` (3.7 MB) -- used for Visual 2 (the "modern sock toss" transition)
   - Additionally, `cold_open_01d_zoom_out.mp4` (11.4 MB) exists for Visual 1.

2. **OffthreadVideo wrapped in Sequence with correct frame ranges**: All three Veo clips in `ColdOpenSection.tsx` follow the correct Remotion pattern:
   - Visual 0: `<Sequence from={BEATS.VISUAL_00_START}>` (frame 0) wrapping `<OffthreadVideo loop src={staticFile("cold_open_01a_establish.mp4")} />` -- plays from 0.0s to 4.92s (148 frames at 30fps)
   - Visual 1: `<Sequence from={BEATS.VISUAL_01_START}>` (frame 157) wrapping `<OffthreadVideo loop src={staticFile("cold_open_01d_zoom_out.mp4")} />` -- plays from 5.24s to 7.72s (75 frames)
   - Visual 2: `<Sequence from={BEATS.VISUAL_02_START}>` (frame 428) wrapping `<OffthreadVideo loop src={staticFile("cold_open_01f_modern_sock_toss.mp4")} />` -- plays from 14.26s to 18.5s (127 frames)

3. **Active visual switching logic is correct**: `ColdOpenSection.tsx:22-28` uses a reverse-scan loop to determine which visual is active: `for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) { if (frame >= VISUAL_SEQUENCE[i].start) { activeVisual = i; break; } }`. This means the previous visual continues rendering during inter-visual gaps (e.g., frames 148-157 between Visual 0 and Visual 1), preventing black frames. The `loop` attribute on OffthreadVideo ensures continuous playback even if the clip is shorter than its beat window.

4. **Narration audio correctly integrated**: `ColdOpenSection.tsx:33` uses `<Audio src={staticFile("cold_open_narration.wav")} />` at the top level, playing for the full section duration. The narration file `cold_open_narration.wav` (773 KB) exists and covers 16.1 seconds of audio synced to the Whisper-derived timestamps in `constants.ts`.

5. **Section duration and frame rate**: `constants.ts:15-17` defines `COLD_OPEN_FPS = 30`, `COLD_OPEN_DURATION_SECONDS = 54`, yielding 1620 total frames. This matches the section-level production timeline (54 seconds covering all 7 visuals from establish through title card). Registered correctly in `Root.tsx:1027-1036` using aliased imports.

6. **Resolution**: `constants.ts:18-19` sets `COLD_OPEN_WIDTH = 1920`, `COLD_OPEN_HEIGHT = 1080`. Matches the spec's "1080p minimum" requirement.

7. **BEATS timing constants are internally consistent**: All frame values in `constants.ts:24-64` are derived from `s2f()` (seconds-to-frames helper using `Math.round(seconds * 30)`). The VISUAL_SEQUENCE array at lines 67-75 correctly maps each BEATS range to its composition ID.

8. **HoldAccumulatedWeight component (Visual 1B)**: `HoldAccumulatedWeight.tsx` provides a 6-second contemplative hold on the split-screen zoomed-out state. It correctly implements:
   - Split-screen layout with `width / 2` panels
   - Left panel: file tree, TODO comments, dependency graph, developer silhouette, cursor blink, ambient warning icon cycling, new TODO fading in, subtle screen flicker
   - Right panel: mended items collection (22 items), wicker basket, oil lamp with animated flame, grandmother silhouette with breathing animation, completed sock with darning patch
   - Center divider: 2px white line with glow
   - Vignette overlay and desaturation filter (`saturate(85%)`)
   - All colors match the spec palette (LEFT_BG, RIGHT_BG, etc.)

9. **Spec's "transition to next scene" is implemented**: The spec calls for a "hard cut to modern day - person discovering hole in sock, shrugging, tossing it in trash, grabbing fresh pair from multi-pack." Visual 2 (`cold_open_01f_modern_sock_toss.mp4`) provides this exact transition, placed after the contemplative hold.

10. **Section-level pipeline correctly composites 7 visuals**: The VISUAL_SEQUENCE covers the full narrative arc: establish (Veo) -> zoom out (Veo) -> hold (Remotion) -> sock toss (Veo) -> code blinks (Remotion) -> code regeneration (Remotion) -> title card (Remotion). Each has appropriate Sequence wrapping and conditional rendering.

### Issues Found

1. **TODO/FIXME comment colors in HoldAccumulatedWeight use red, not muted gray** (Severity: LOW)
   `HoldAccumulatedWeight.tsx:329-330` renders TODO comments with `color: "#f87171"` and `backgroundColor: "rgba(248, 113, 113, 0.15)"`. The spec states TODO/Comments should use "Slightly muted color (#888)". The previous audit noted this was fixed in the `01-ColdOpen/LeftPanel.tsx`, but the `HoldAccumulatedWeight.tsx` (the production-path component that actually renders the hold beat) was not updated to match.
   **File**: `remotion/src/remotion/S00-ColdOpen/HoldAccumulatedWeight.tsx:329-330`

2. **Code lineHeight 1.8 in HoldAccumulatedWeight instead of spec's 1.5** (Severity: LOW)
   `HoldAccumulatedWeight.tsx:233` uses `lineHeight: 1.8` for code text. The spec specifies "Line height: 1.5". The previous audit noted this was fixed in `01-ColdOpen/LeftPanel.tsx`, but the production-path component was not updated.
   **File**: `remotion/src/remotion/S00-ColdOpen/HoldAccumulatedWeight.tsx:233`

3. **S00-ColdOpen section uses 30fps, not 60fps as spec recommends** (Severity: INFO)
   `constants.ts:15` sets `COLD_OPEN_FPS = 30`. The spec recommends "60fps for smooth zooms, can be 30fps for static portions." Since the section-level pipeline uses pre-rendered Veo clips rather than Remotion-animated zooms, 30fps is adequate. The standalone `01-ColdOpen` composition correctly uses 60fps for its animated zooms.
   **File**: `remotion/src/remotion/S00-ColdOpen/constants.ts:15`

4. **Duration is 54 seconds instead of spec's 38 seconds** (Severity: INFO)
   `constants.ts:16` sets `COLD_OPEN_DURATION_SECONDS = 54`. The spec covers only the split-screen portion (0:00-0:38). The additional 16 seconds accommodate Visuals 3, 3B, and 4 (code blinks, code regeneration, title card), which belong to subsequent specs in the Cold Open section. This is expected for a section-level assembly.
   **File**: `remotion/src/remotion/S00-ColdOpen/constants.ts:16`

### Notes

- **Architecture**: There are two parallel implementations. `01-ColdOpen/` is a standalone Remotion procedural animation that faithfully implements the spec's 38-second, 60fps, 5-beat structure with full SVG-based animation. `S00-ColdOpen/` is the production assembly pipeline that composites pre-rendered Veo video clips with Remotion components, synced to Whisper-derived audio timestamps at 30fps over 54 seconds. This audit focuses on the S00-ColdOpen production path and its Veo asset integration.

- **Inter-visual gaps**: Small timing gaps exist between visuals (e.g., 9 frames between Visual 0 end and Visual 1 start). The `activeVisual` logic gracefully handles these by continuing to render the previous visual, so there are no black frames.

- **Video looping**: All three Veo clips use `loop` on OffthreadVideo. This ensures continuous playback if a clip is shorter than its beat window, but could produce visual repetition if the clip is significantly shorter than its allocated time. For the current beat durations (4.9s, 2.5s, 4.2s), short Veo clips would loop visibly. This is worth monitoring during render review.

- **Previous audit fixes verified in 01-ColdOpen path**: The previous audit documented fixes for narrator text timing, Math.random() flickering, line height, TODO color, and developer hand visibility in the `01-ColdOpen/` components. These fixes apply to the standalone composition path. Two of those same issues (TODO color and line height) persist in the production-path `HoldAccumulatedWeight.tsx` but are LOW severity since they affect a 6-second contemplative hold where the visual difference is minor.

---

## Resolution Status
- **Status**: PASS
- **Rationale**: Both required Veo video assets exist and are correctly integrated into the Remotion composition. OffthreadVideo components are properly wrapped in Sequence elements with frame ranges derived from Whisper-synced BEATS constants. The activeVisual switching logic correctly handles inter-visual gaps. Audio is integrated at the section level. The two LOW-severity issues (TODO comment color and line height in HoldAccumulatedWeight) are cosmetic and do not affect functional correctness or the overall visual quality of the production pipeline.

## Re-Audit Update (2026-02-09)
- **Status**: PASS
- **Result**: Fresh audit of the S00-ColdOpen production pipeline confirms all Veo video assets (`cold_open_01a_establish.mp4`, `cold_open_01d_zoom_out.mp4`, `cold_open_01f_modern_sock_toss.mp4`) exist and are correctly integrated via OffthreadVideo wrapped in Sequence with proper frame ranges. The `HoldAccumulatedWeight` Remotion component provides a well-implemented 6-second contemplative hold with ambient animations. Two LOW-severity style inconsistencies found in HoldAccumulatedWeight (TODO color and line height) that were previously fixed in the standalone 01-ColdOpen path but not propagated to the production path. Overall integration is correct and functional.
