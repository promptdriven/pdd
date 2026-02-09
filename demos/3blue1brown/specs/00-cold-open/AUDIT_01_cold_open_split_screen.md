# Audit: Cold Open Split Screen

## Status: ISSUES FOUND

---

### Requirements Met

1. **Split screen layout**: `ColdOpenSplitScreen.tsx` (lines 32-58) divides the frame into left and right halves at 50% width, with a vertical divider at the center. The layout matches the spec's "clean vertical divide at center of frame."

2. **Center divider**: `ColdOpenSplitScreen.tsx` (line 66) renders a 2px white (`#ffffff`) divider line, matching the spec exactly ("Divider | #ffffff | Clean vertical line, 2px"). A subtle box-shadow glow is added for polish.

3. **Color palette**: `constants.ts` (lines 28-42) defines all colors matching the spec table exactly:
   - LEFT_BG: `#1a1a2e` (dark, cool workspace)
   - LEFT_ACCENT: `#4A90D9` (Cursor UI elements)
   - RIGHT_BG: `#2d2416` (warm, amber shadows)
   - RIGHT_ACCENT: `#D9944A` (lamplight, warmth)
   - CODE_NORMAL: `#e0e0e0`, CODE_ADDED: `#4ade80`, CODE_REMOVED: `#f87171`
   - DIVIDER: `#ffffff`

4. **Beat timings**: `constants.ts` (lines 11-22) defines BEATS matching the spec exactly:
   - Beat 1 Establish: 0-8s
   - Beat 2 Sync Completion: 8-15s
   - Beat 3 Satisfaction: 15-18s
   - Beat 4 Zoom Out: 18-32s
   - Beat 5 Hold: 32-38s

5. **Frame rate**: `constants.ts` (line 4) sets `COLD_OPEN_FPS = 60`, matching the spec's "60fps for smooth zooms" recommendation.

6. **Cursor IDE mockup**: `LeftPanel.tsx` (lines 220-417) implements a detailed IDE mockup with:
   - Dark theme title bar with traffic light buttons (lines 238-240)
   - File name display "parser.ts - Cursor" (line 242)
   - AI suggestion indicator with sparkle emoji (lines 245-260)
   - `JetBrains Mono` font family (line 266), matching spec's typography requirement
   - Font size 16 (line 267), within the spec's "approximately 14-16pt equivalent" range
   - Line height 1.8 (line 268) - close to spec's 1.5 but slightly larger

7. **Code diff visualization**: `LeftPanel.tsx` (lines 286-391) shows:
   - Red line with `rgba(248, 113, 113, 0.2)` background for removed code (line 290)
   - Green line for added code (line 314)
   - "-" and "+" diff markers (lines 307, 335)
   - Accept button with "Tab" shortcut indicator (lines 355-373)
   - Reject button (lines 374-388)
   - Matches spec: "Green for additions, red for removals, The characteristic 'Accept' button or Tab indicator"

8. **Code edit animation timing**: The diff appears at 0:08 (`syncStart`), red line fades out at ~0:12 (`acceptStart`), and success checkmark shows at 0:15 (`syncEnd`). This matches the spec's code edit animation timing of 0:08-0:10 fade in, 0:10-0:12 highlight, 0:12-0:14 replacement, 0:14-0:15 success.

9. **Success indicator**: `LeftPanel.tsx` (lines 395-416) renders a green circle with checkmark SVG and "Patched" text at frame 0:15. Matches spec's "Brief 'success' indicator (checkmark or green flash)."

10. **Vignette darkening**: `ColdOpenSplitScreen.tsx` (lines 15-18, 74-85) applies a radial gradient vignette that interpolates from opacity 0 to 0.4 during zoom out. Matches spec's "Slight vignette darkening on edges."

11. **Desaturation during zoom**: `ColdOpenSplitScreen.tsx` (lines 21-24, 29) applies CSS `saturate()` filter interpolating from 100% to 85% during zoom. Matches spec's "Colors slightly desaturate as scope increases."

12. **Three-phase zoom easing**: Both `LeftPanel.tsx` (lines 161-185) and `RightPanel.tsx` (lines 303-327) implement the spec's three-phase zoom curve:
    - Phase 1 (0:18-0:20): `Easing.in(Easing.cubic)` for slow ease-in
    - Phase 2 (0:20-0:28): Linear constant speed
    - Phase 3 (0:28-0:32): `Easing.out(Easing.cubic)` for deceleration
    Matches the spec: "0:18-0:20 Start zoom, slow ease-in / 0:20-0:28 Main zoom, constant speed / 0:28-0:32 Decelerate, ease-out to final frame."

13. **TODO/FIXME comments**: `LeftPanel.tsx` (lines 11-16) defines `TODO_COMMENTS` array with "// FIXME: memory leak", "// TODO: refactor this", "// temporary workaround", "// don't touch!" -- matching the spec's specified texts (`// FIXME`, `// temporary`, `// don't touch`). Rendered as floating overlays with rotation and staggered fade-in (lines 488-512).

14. **Expanded file tree**: `LeftPanel.tsx` (lines 18-106) programmatically generates 150+ files across 11 directories (components, utils, api, services, models, hooks, store, types, config, lib, pages), approximating the spec's "hundreds of files."

15. **Git blame color strips**: `LeftPanel.tsx` (lines 109-112) defines `FILE_BLAME_COLORS` with 10 distinct colors, rendered as 2px vertical bars beside files (lines 466-476). Matches spec's "Git blame colors showing patchwork history."

16. **Diff markers in file tree**: `LeftPanel.tsx` (lines 454-464) renders red/green dots next to files with `hasChanges=true`, approximating the spec's "diff markers visible throughout."

17. **Warning/flame icons**: `LeftPanel.tsx` (lines 478-480) renders fire emoji icons on files with `hasWarning=true` (~15% of files). Corresponds to spec's "occasional flicker of a lint warning."

18. **Developer hands on keyboard**: `LeftPanel.tsx` (lines 514-571) shows a keyboard SVG with hand silhouettes and a developer icon with subtle head-nod animation during the satisfaction beat (0:15-0:18). Addresses spec's "Developer's hands on keyboard" and "Subtle nod or satisfied posture shift."

19. **Dependency graph**: `LeftPanel.tsx` (lines 594-633) renders an SVG network graph with 9 nodes and intentionally crossing/tangled dependency lines in multiple colors, with dashed cross-connections. Matches spec's "dependency graph with tangled lines."

20. **Right side - warm ambient light**: `RightPanel.tsx` (lines 347-358) applies a radial gradient using `RIGHT_ACCENT` color to simulate lamplight. Matches spec's "amber/golden lamplight."

21. **Oil lamp**: `RightPanel.tsx` (lines 385-418) renders a detailed SVG oil lamp with base, reservoir, glass chimney, animated flame glow (with SVG `<animate>` element), and radial glow effect. Matches spec's "Oil lamp or early electric lamp casting warm light."

22. **Darning animation**: `RightPanel.tsx` implements:
    - `WoolSock` component (lines 38-185) with progressive hole repair via `holeProgress` prop
    - Frayed edges that fade as repair progresses (lines 120-135)
    - Woven darning stitches: vertical warp threads and horizontal weft threads appearing sequentially (lines 138-171)
    - `NeedleAndThread` component (lines 188-216) with animated needle oscillation
    - Scissors appearing at completion with rotation animation (lines 462-483)
    - Matches spec's darning animation: "Needle pulls thread through fabric, Cross-stitch pattern forming over hole, Thread tightens, closing gap, Final stitch completes, Thread is cut with small scissors."

23. **Sock inspection (satisfaction beat)**: `RightPanel.tsx` (lines 297-301, 337-338) implements sock lift and rotation during 0:15-0:18, with a "Mended" success indicator (lines 499-518). Matches spec's "Grandmother holds up sock briefly, inspecting."

24. **Mended items collection**: `RightPanel.tsx` (lines 12-35) defines 22 mended items (socks, shirts, trousers) with distinct icon components:
    - `SmallSockIcon` with patch marks (lines 219-233)
    - `SmallShirtIcon` with elbow patches (lines 236-249)
    - `SmallTrouserIcon` with knee patches (lines 252-265)
    Matches spec's "Socks with multiple patch areas, Shirts with elbow patches, Trousers with knee reinforcements."

25. **Wicker basket**: `RightPanel.tsx` (lines 543-566) renders an SVG basket with weave pattern and handle, appearing at zoom progress > 0.5. Matches spec's "Drawer opens or basket revealed."

26. **Grandmother silhouette**: `RightPanel.tsx` (lines 569-588) renders an SVG figure with head, hair bun, and body during zoom. Matches spec's "grandmother's hands resting, slightly tired" for the final frame.

27. **Narrator text**: `ColdOpenSplitScreen.tsx` (lines 87-118) displays the exact narrator line "But here's what your great-grandmother figured out sixty years ago." with Georgia serif font, italic style, and fade-in animation starting at frame 24s. Matches the spec's narrator line verbatim.

28. **Browser tabs**: `LeftPanel.tsx` (lines 636-673) shows multiple open file tabs during zoom, adding to the visual complexity of the zoomed-out developer view.

---

### Issues Found

1. **S00-ColdOpen section bypasses 01-ColdOpen Remotion animation (High)**
   - **Spec says**: Full animated split-screen scene with five beats, detailed procedural animation of developer and grandmother
   - **Implementation does**: `S00-ColdOpen/ColdOpenSection.tsx` uses `OffthreadVideo` components loading pre-rendered video files (`cold_open_01a_establish.mp4`, `cold_open_01d_zoom_out.mp4`, `cold_open_01f_modern_sock_toss.mp4`) instead of the Remotion-animated `ColdOpenSplitScreen` from `01-ColdOpen/`
   - **Impact**: The section-level composition (`S00-ColdOpen`) that would be used in the final render pipeline does not use the Remotion implementation at all. The `01-ColdOpen/ColdOpenSplitScreen` component exists as a standalone composition but is not referenced by `ColdOpenSection.tsx`.
   - **S00 constants differ significantly**: `S00-ColdOpen/constants.ts` uses 30fps (not 60fps), 19-second duration (not 38 seconds), completely different beat structure with 5 visual segments synced to Whisper-derived audio timestamps. This is a fundamentally different timeline than the spec.

2. **S00-ColdOpen narration content diverges from spec (Medium)**
   - **Spec says**: Narrator line is "But here's what your great-grandmother figured out sixty years ago." during Beat 5 (0:32-0:38)
   - **Implementation does**: `S00-ColdOpen/constants.ts` (lines 8-13) shows a different narration structure with 5 segments including "If you use cursor or clawed code or copilot" and "So why are we still patching?" -- content that does not appear in the spec for this animation
   - **Impact**: The section-level implementation has different narration content and timing than specified

3. **S00-ColdOpen includes content beyond spec scope (Low)**
   - **Spec says**: The split-screen animation covers 0:00-0:38 with transition to "modern day sock toss"
   - **Implementation does**: `ColdOpenSection.tsx` includes Visual 3 (code regeneration with `pdd generate` command) and Visual 4 (title card "Prompt-Driven Development") which are not part of this spec
   - **Impact**: The section composition bundles additional content from subsequent specs into one component

4. **Line height deviation (Low)**
   - **Spec says**: "Line height: 1.5" for code typography
   - **Implementation does**: `LeftPanel.tsx` line 268 sets `lineHeight: 1.8`
   - **Impact**: Code appears slightly more spaced out than specified

5. **Resolution at 1080p, not 4K (Low)**
   - **Spec says**: "Resolution: 4K (3840x2160) recommended, 1080p minimum"
   - **Implementation does**: `01-ColdOpen/constants.ts` line 7 sets `COLD_OPEN_WIDTH = 1920` and line 8 sets `COLD_OPEN_HEIGHT = 1080` with comment "1080p for now, can upgrade to 4K"
   - **Impact**: Uses the minimum acceptable resolution rather than the recommended 4K. Not a blocker since spec says "1080p minimum."

6. **Random values in render-time code (Low)**
   - **Implementation issue**: `LeftPanel.tsx` line 460 uses `Math.random()` to determine diff marker color (`Math.random() > 0.5 ? COLORS.CODE_ADDED : COLORS.CODE_REMOVED`), and the `generateFileTree` function (lines 27-28) uses `Math.random()` for `hasChanges` and `hasWarning` properties
   - **Impact**: The `generateFileTree` runs once at module load so is stable per render, but the diff marker color on line 460 will produce different colors on every frame, causing visual flickering. This is a rendering bug.

7. **Hands implementation is abstract (Low)**
   - **Spec says**: "Developer's hands on keyboard, face partially visible" (during Beat 1 establish) and "Elderly woman's hands holding darning egg and needle"
   - **Implementation does**: Developer hands are shown only during satisfaction beat (0:15-0:18, `LeftPanel.tsx` lines 515-571) as translucent blue ellipse silhouettes, not during the initial establish phase. Grandmother's hands are basic ellipse silhouettes (`RightPanel.tsx` lines 430-440)
   - **Impact**: Hands are present but simplified to abstract shapes rather than realistic representations. Developer hands appear only in satisfaction beat, not from Beat 1 as specified.

8. **No darning egg prop (Low)**
   - **Spec says**: "Darning egg prop" in asset requirements and "Elderly woman's hands holding darning egg and needle"
   - **Implementation does**: The sock is rendered flat without a visible darning egg underneath it
   - **Impact**: Missing a small period-specific detail from the spec

9. **Audio sync point not programmatically implemented (Low)**
   - **Spec says**: "Audio sync point: Soft 'click' or resolution tone as both complete" at 0:15
   - **Implementation does**: `ColdOpenSection.tsx` loads a single narration audio file (`cold_open_narration.wav`) but no programmatic sync point or sound effect is triggered at frame 0:15 in the `01-ColdOpen` Remotion components
   - **Impact**: Relies on the audio file having the correct sound at the right moment rather than being programmatically synchronized

---

### Notes

- There are two separate implementations: `01-ColdOpen/` contains a full Remotion procedural animation (`ColdOpenSplitScreen`) that closely follows the spec, while `S00-ColdOpen/` contains the section-level composition (`ColdOpenSection`) that uses pre-rendered Veo video files and has a completely different timeline (19 seconds at 30fps vs 38 seconds at 60fps). The `01-ColdOpen` implementation is thorough and matches most spec requirements, but the `S00-ColdOpen` section that would be used in the final render pipeline does not use it.
- The `01-ColdOpen/ColdOpenSplitScreen` component is well-implemented with detailed SVG artwork for the wool sock, oil lamp, needle/thread, scissors, mended garment icons, and wicker basket. The darning animation with progressive warp/weft thread appearance is a good approximation of the specified stitch-by-stitch repair.
- The `Math.random()` usage on `LeftPanel.tsx` line 460 for diff marker colors will cause frame-to-frame flickering in rendered video and should be replaced with a deterministic seed or pre-computed values.
- The previous audit's "Resolution Status: RESOLVED" claim was premature -- while many issues from the original audit were addressed in the `01-ColdOpen` implementation, the fundamental disconnect between the two implementation directories (`01-ColdOpen` vs `S00-ColdOpen`) remains the most significant issue, and several smaller deviations persist.
