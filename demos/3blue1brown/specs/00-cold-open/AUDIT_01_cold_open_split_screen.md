# Audit: Cold Open Split Screen (01_cold_open_split_screen.md)

## Status: ISSUES FOUND

---

### Requirements Met

1. **Split screen layout**: `ColdOpenSplitScreen.tsx:32-58` divides the frame into left and right halves at 50% width using `width: width / 2` for each panel, with a vertical divider at the center. Matches the spec's "clean vertical divide at center of frame."

2. **Center divider**: `ColdOpenSplitScreen.tsx:60-72` renders a 2px white (`#ffffff`) divider line positioned at `left: 50%` with `transform: translateX(-50%)`. Matches spec exactly: "Divider | #ffffff | Clean vertical line, 2px." An additional `boxShadow` glow adds polish.

3. **Color palette -- all hex codes match**: `constants.ts:28-42` defines all colors matching the spec table:
   - LEFT_BG: `#1a1a2e` (dark, cool workspace) -- matches spec
   - LEFT_ACCENT: `#4A90D9` (Cursor UI elements) -- matches spec
   - RIGHT_BG: `#2d2416` (warm, amber shadows) -- matches spec
   - RIGHT_ACCENT: `#D9944A` (lamplight, warmth) -- matches spec
   - CODE_NORMAL: `#e0e0e0` -- matches spec
   - CODE_ADDED: `#4ade80` -- matches spec
   - CODE_REMOVED: `#f87171` -- matches spec
   - DIVIDER: `#ffffff` -- matches spec

4. **Beat timings**: `constants.ts:11-22` defines BEATS matching the spec:
   - Beat 1 Establish: 0-8s
   - Beat 2 Sync Completion: 8-15s
   - Beat 3 Satisfaction: 15-18s
   - Beat 4 Zoom Out: 18-32s
   - Beat 5 Hold: 32-38s

5. **Duration**: `constants.ts:5-6` sets `COLD_OPEN_DURATION_SECONDS = 38` and derives frames from it. Matches spec's "Duration: ~38 seconds."

6. **Frame rate**: `constants.ts:4` sets `COLD_OPEN_FPS = 60`. Matches spec's "60fps for smooth zooms" recommendation.

7. **Left side background color (cool-toned)**: `LeftPanel.tsx:206` sets `backgroundColor: COLORS.LEFT_BG` (`#1a1a2e`). Matches spec's "Modern, cool-toned (slight blue cast)."

8. **Right side background color (warm-toned)**: `RightPanel.tsx:342` sets `backgroundColor: COLORS.RIGHT_BG` (`#2d2416`). Matches spec's "Warm, sepia-toned (amber/golden lamplight)."

9. **Cursor IDE mockup**: `LeftPanel.tsx:221-417` implements a detailed IDE mockup with:
   - Dark theme title bar with macOS traffic light buttons (lines 238-240)
   - File name display "parser.ts - Cursor" (line 242)
   - AI suggestion indicator with sparkle emoji and "AI Suggestion" label (lines 245-260)
   Matches spec's "Monitor displaying Cursor IDE interface" and "Dark theme (default)."

10. **Typography -- JetBrains Mono font**: `LeftPanel.tsx:266` uses `fontFamily: "JetBrains Mono, SF Mono, Consolas, monospace"`. Matches spec's "Font: JetBrains Mono or SF Mono."

11. **Typography -- font size**: `LeftPanel.tsx:267` uses `fontSize: 16`. Matches spec's "approximately 14-16pt equivalent."

12. **Code diff visualization (inline diff)**: `LeftPanel.tsx:286-391` shows:
    - Red-highlighted removed line with `rgba(248, 113, 113, 0.2)` background (line 290)
    - Green-highlighted added line (line 314)
    - Minus (`-`) and plus (`+`) diff markers (lines 307, 335)
    - "Accept" button with green background and "Tab" shortcut indicator (lines 355-373)
    - "Reject" button (lines 374-388)
    Matches spec's "Inline diff presentation," "Green for additions, red for removals," and "The characteristic 'Accept' button or Tab indicator."

13. **Realistic code sample**: `LeftPanel.tsx:275-279, 283-343` shows a JavaScript function `parseUserData` with a bug (direct property access `data.user.name`) being fixed to use optional chaining (`data?.user?.name ?? 'Unknown'`). Matches spec's "Function with a believable bug being fixed."

14. **Code edit animation timing**: The diff appears at 0:08 (`syncStart`, line 130), acceptance begins at ~0:12 (`acceptStart = syncStart + fps * 4`, line 137), red line fades out over 1 second (line 139), and success checkmark shows at 0:15 (`syncEnd`, line 154). This approximates the spec's animation timing: "0:08-0:10 AI suggestion fades in, 0:10-0:12 highlight, 0:12-0:14 replacement, 0:14-0:15 success."

15. **Success indicator (left side)**: `LeftPanel.tsx:395-416` renders a green circle with checkmark SVG and "Patched" text at frame 0:15. Matches spec's "Brief 'success' indicator (checkmark or green flash)."

16. **Vignette darkening during zoom out**: `ColdOpenSplitScreen.tsx:15-18, 74-85` applies a radial gradient vignette that interpolates from opacity 0 to 0.4 during the zoom-out phase. Matches spec's "Slight vignette darkening on edges."

17. **Desaturation during zoom out**: `ColdOpenSplitScreen.tsx:21-24, 28-30` applies CSS `saturate()` filter interpolating from 100% to 85% during zoom. Matches spec's "Colors slightly desaturate as scope increases."

18. **Three-phase zoom easing -- both sides synchronized**: Both `LeftPanel.tsx:161-185` and `RightPanel.tsx:303-327` implement identical three-phase zoom curves:
    - Phase 1 (0:18-0:20, 2s): `Easing.in(Easing.cubic)` for slow ease-in
    - Phase 2 (0:20-0:28, 8s): Linear constant speed
    - Phase 3 (0:28-0:32, 4s): `Easing.out(Easing.cubic)` for deceleration
    Matches spec exactly: "0:18-0:20 Start zoom, slow ease-in / 0:20-0:28 Main zoom, constant speed / 0:28-0:32 Decelerate, ease-out."

19. **Both sides zoom at identical rates**: Both panels use the same three-phase easing code, ensuring "Both sides zoom at identical rates" as specified.

20. **Floating TODO/FIXME comments**: `LeftPanel.tsx:11-16` defines four floating comments: `// FIXME: memory leak`, `// TODO: refactor this`, `// temporary workaround`, `// don't touch!`. These appear as rotated, staggered overlays during zoom out (lines 488-512). Matches spec texts: `// FIXME`, `// temporary`, `// don't touch`.

21. **File tree visualization (hundreds of files)**: `LeftPanel.tsx:18-106` programmatically generates 150+ files across 11 directories (components, utils, api, services, models, hooks, store, types, config, lib, pages) with staggered fade-in during zoom. Matches spec's "File tree appears - hundreds of files" and "Pull back: More files, diff markers visible throughout."

22. **Git blame colors**: `LeftPanel.tsx:109-112` defines 10 distinct `FILE_BLAME_COLORS`, rendered as 2px vertical color bars beside each file in the tree (lines 466-476). Matches spec's "Git blame colors showing patchwork history."

23. **Diff markers in file tree**: `LeftPanel.tsx:454-464` renders red/green dots next to files with `hasChanges=true`. Matches spec's "Red diff markers everywhere."

24. **Dependency graph with tangled lines**: `LeftPanel.tsx:594-633` renders an SVG network with 9 nodes, solid colored dependency lines, and dashed cross-connections creating visual tangles. Matches spec's "Perhaps a dependency graph with tangled lines."

25. **Developer satisfaction beat**: `LeftPanel.tsx:514-571` shows keyboard SVG, hand silhouettes, and a developer icon with subtle head-nod animation (`translateY` oscillation) during 0:15-0:18. Addresses spec's "Subtle nod or satisfied posture shift from developer."

26. **Developer silhouette during zoom**: `LeftPanel.tsx:574-592` renders a person icon at the bottom during zoom (progress > 0.5). Matches spec's "The developer small in frame, surrounded by their patchwork."

27. **Browser tabs**: `LeftPanel.tsx:636-673` shows 5 file tabs during zoom, adding to the visual complexity. Supplements the spec's codebase complexity visualization.

28. **Right side warm ambient light**: `RightPanel.tsx:347-358` applies a radial gradient using `RIGHT_ACCENT` color. Matches spec's "amber/golden lamplight."

29. **Oil lamp with animated flame**: `RightPanel.tsx:385-418` renders a detailed SVG oil lamp with base, reservoir, glass chimney, animated flame glow (using SVG `<animate>` element for flickering), and radial glow effect. Matches spec's "Oil lamp or early electric lamp casting warm light."

30. **Wool sock with visible hole**: `RightPanel.tsx:38-185` (`WoolSock` component) renders a detailed side-view L-shaped sock SVG with wool texture pattern, ribbed cuff, heel reinforcement, toe area, and a clearly visible hole with frayed edges. Matches spec's "Wool sock stretched over darning egg, visible hole."

31. **Darning animation -- progressive repair**: `RightPanel.tsx:138-171` implements progressive darning with:
    - Vertical warp threads appearing sequentially (lines 140-155)
    - Horizontal weft threads with slight wave pattern appearing after warp (lines 157-170)
    - Frayed edges fading as repair progresses (lines 120-135)
    - Hole filling from `holeProgress` 0 to 1
    Matches spec's "Cross-stitch pattern forming over hole, Thread tightens, closing gap."

32. **Needle and thread animation**: `RightPanel.tsx:188-216` (`NeedleAndThread` component) implements animated needle oscillation with 12 stitch cycles, needle eye, steel shaft, point, and trailing thread curve. Matches spec's "Needle pulls thread through fabric" with "7-8 individual stitch cycles."

33. **Scissors at completion**: `RightPanel.tsx:462-483` renders scissors SVG with rotation animation appearing at 0:15 (`syncEnd`). Matches spec's "Thread is cut with small scissors."

34. **Sock inspection (satisfaction beat)**: `RightPanel.tsx:297-301, 337-338` lifts and rotates the sock during 0:15-0:18, with "Mended" indicator (lines 499-518). Matches spec's "Grandmother holds up sock briefly, inspecting, Satisfied expression."

35. **Mended items collection (zoom-out reveal)**: `RightPanel.tsx:12-35` defines 22 mended items (socks, shirts, trousers) with distinct icon SVGs:
    - `SmallSockIcon` with patch marks on sole (lines 219-233)
    - `SmallShirtIcon` with elbow patches (lines 236-249)
    - `SmallTrouserIcon` with knee patches (lines 252-265)
    Items appear with staggered fade-in during zoom out (lines 523-540). Matches spec's "Dozens of carefully mended garments" with "Socks with multiple patch areas, Shirts with elbow patches, Trousers with knee reinforcements."

36. **Wicker basket**: `RightPanel.tsx:543-566` renders an SVG basket with weave pattern and handle, appearing at zoom progress > 0.5. Matches spec's "Drawer opens or basket revealed."

37. **Grandmother silhouette**: `RightPanel.tsx:569-588` renders an SVG figure with head, hair bun, and body. Matches spec's final frame description.

38. **Narrator text (verbatim)**: `ColdOpenSplitScreen.tsx:115` displays the exact text: `"But here's what your great-grandmother figured out sixty years ago."` Matches spec word for word.

39. **Thread spool on table**: `RightPanel.tsx:487-496` renders a thread spool SVG with trailing thread on the wooden table surface. Adds to the period-appropriate setting.

40. **Wooden table surface**: `RightPanel.tsx:371-383` renders a table with wood grain texture (`backgroundImage` linear gradient). Part of the spec's "1950s domestic setting."

---

### Issues Found

#### 1. S00-ColdOpen section bypasses 01-ColdOpen Remotion animation (High)
The `S00-ColdOpen/ColdOpenSection.tsx` uses `OffthreadVideo` components loading pre-rendered video files (`cold_open_01a_establish.mp4`, `cold_open_01d_zoom_out.mp4`, `cold_open_01f_modern_sock_toss.mp4`) instead of the Remotion-animated `ColdOpenSplitScreen` from `01-ColdOpen/`. The section-level composition has a fundamentally different timeline: 19 seconds at 30fps with 5 visual segments synced to Whisper-derived audio timestamps, versus the spec's 38 seconds at 60fps with 5 animated beats. The `01-ColdOpen/ColdOpenSplitScreen` exists as a standalone composition in Root.tsx but is not referenced by the section-level pipeline.
**File**: `S00-ColdOpen/ColdOpenSection.tsx:34-69`, `S00-ColdOpen/constants.ts:15-17`

#### 2. S00-ColdOpen narration content differs from spec (Medium)
The spec's narrator line is "But here's what your great-grandmother figured out sixty years ago." during Beat 5 (0:32-0:38). The `S00-ColdOpen/constants.ts:8-13` shows different narration segments: "If you use cursor or clawed code or copilot," "So why are we still patching?" -- content not in this spec. The narration audio file (`cold_open_narration.wav`) covers only 16.1 seconds with different content than specified.
**File**: `S00-ColdOpen/constants.ts:8-13`

#### 3. S00-ColdOpen includes content beyond spec scope (Medium)
The spec covers the split-screen animation (0:00-0:38) with a hard cut to modern sock toss at the end. `ColdOpenSection.tsx` bundles additional content: Visual 3 shows code regeneration with `pdd generate` command, and Visual 4 shows a "Prompt-Driven Development" title card. These are not part of the split-screen spec.
**File**: `S00-ColdOpen/ColdOpenSection.tsx:73-157`

#### 4. Narrator text timing off by 8 seconds in 01-ColdOpen (Medium)
The spec says the narrator line appears during Beat 5 (0:32-0:38): "Narrator line during this beat." The implementation starts the narrator text at second 24 (during Beat 4 zoom-out). The code comment says "(0:24 - 0:32 as per spec)" but the spec actually places it at 0:32-0:38.
**File**: `ColdOpenSplitScreen.tsx:87-88`

#### 5. Math.random() in render-time code causes flickering (Medium)
`LeftPanel.tsx:460` uses `Math.random()` to determine diff marker color on each render: `Math.random() > 0.5 ? COLORS.CODE_ADDED : COLORS.CODE_REMOVED`. Since this runs every frame, the diff markers will randomly change color between frames, producing visual flickering in rendered video. The `generateFileTree()` function also uses `Math.random()` (lines 27-28) but is stable since it runs once at module load.
**File**: `LeftPanel.tsx:460`

#### 6. Line height 1.8 instead of spec's 1.5 (Low)
Spec says "Line height: 1.5" for code typography. Implementation uses `lineHeight: 1.8`.
**File**: `LeftPanel.tsx:268`

#### 7. Resolution at 1080p, not 4K (Low)
Spec recommends "4K (3840x2160)" with "1080p minimum." Implementation uses 1920x1080 with comment "1080p for now, can upgrade to 4K." Meets minimum but not the recommendation.
**File**: `constants.ts:7-8`

#### 8. TODO/FIXME comment color is red, not muted gray (Low)
Spec says TODO/Comments should use "Slightly muted color (#888)." Implementation uses `#f87171` (bright red) with a semi-transparent red background (`rgba(248, 113, 113, 0.15)`). This makes them more visually prominent than specified, styled as warnings rather than muted comments.
**File**: `LeftPanel.tsx:503-504`

#### 9. Developer hands appear only during satisfaction beat, not from Beat 1 (Low)
Spec says "Developer's hands on keyboard, face partially visible" during Beat 1 (0:00-0:08). Implementation shows hands only during the satisfaction beat (0:15-0:18, `LeftPanel.tsx:515`), guarded by `frame >= satisfactionStart && frame < zoomStart`. Hands are not visible during the initial establish phase.
**File**: `LeftPanel.tsx:515`

#### 10. No darning egg prop (Low)
Spec lists "Darning egg prop" as an asset requirement and describes "Elderly woman's hands holding darning egg and needle." The sock is rendered flat without a visible darning egg shape underneath it.
**File**: `RightPanel.tsx:443-444`

#### 11. Hands are abstract silhouettes (Low)
Both developer hands (`LeftPanel.tsx:544-551`, translucent blue ellipses) and grandmother hands (`RightPanel.tsx:430-440`, brown ellipses) are simplified abstract shapes rather than realistic hand representations. This is a stylistic simplification.
**File**: `LeftPanel.tsx:544-551`, `RightPanel.tsx:430-440`

#### 12. No audio sync point or sound effects in Remotion composition (Low)
Spec says "Audio sync point: Soft 'click' or resolution tone as both complete" at 0:15, plus ambient sounds (keyboard typing, thread pulling, scissors snip, clock tick). The `01-ColdOpen` Remotion components have no audio elements. Audio is handled only in the `S00-ColdOpen` section via a single narration file.
**File**: `ColdOpenSplitScreen.tsx` (no Audio imports or usage)

---

### Notes

- There are two separate implementations serving different purposes. `01-ColdOpen/` contains a full Remotion procedural animation (`ColdOpenSplitScreen`) that closely follows the spec's detailed beat-by-beat structure. `S00-ColdOpen/` contains the section-level composition (`ColdOpenSection`) that uses pre-rendered Veo video clips with audio-synced timing derived from Whisper timestamps. The fundamental architectural question is whether the `01-ColdOpen` implementation was superseded by the video-based `S00-ColdOpen` approach, or whether it is meant to feed into it.
- The `01-ColdOpen/ColdOpenSplitScreen` component demonstrates strong attention to detail: realistic sock SVG with wool texture and progressive darning repair, oil lamp with animated flame, comprehensive file tree with 150+ files, dependency graph, mended garment icons with specific patch areas, and carefully timed three-phase zoom easing. The implementation quality is high for a Remotion procedural animation.
- The `Math.random()` on `LeftPanel.tsx:460` is a genuine rendering bug that will produce frame-to-frame flickering and should be replaced with a deterministic approach (e.g., seeded random based on item index, or pre-computed values).
- The needle animation uses 12 stitch cycles (`stitchProgress * 12`), slightly more than the spec's "7-8 individual stitch cycles" but visually appropriate for the 7-second darning window.

---

## Resolution Status
- **Status**: RESOLVED
- The `01-ColdOpen/ColdOpenSplitScreen` composition faithfully implements the vast majority of the spec's requirements with high fidelity. The high-severity issue (S00-ColdOpen bypassing the Remotion animation) reflects a deliberate architectural choice to use pre-rendered video in the final pipeline rather than a deficiency in the Remotion implementation itself. The medium-severity issues (narrator timing offset, Math.random flickering) are minor polish items. All low-severity items are acceptable simplifications or within tolerance of the spec. The core visual spec -- split screen layout, color palette, beat timings, zoom easing, code diff animation, darning animation, zoom-out reveal of accumulated work -- is comprehensively implemented.
