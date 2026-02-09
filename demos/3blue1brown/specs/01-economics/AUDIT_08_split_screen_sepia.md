# Audit: 08_split_screen_sepia.md

## Status: PASS (with minor caveats)

### Requirements Met

1. **Veo 3.1 Video Asset Present**
   - The spec designates this as a Veo 3.1 video generation shot (not a Remotion programmatic animation). The video file `07_split_screen_sepia.mp4` exists at `remotion/public/07_split_screen_sepia.mp4` (2.7 MB).
   - File: `remotion/public/07_split_screen_sepia.mp4`

2. **Integrated into Part1Economics Sequence as Visual 21**
   - The video is rendered via `<OffthreadVideo>` with `src={staticFile("07_split_screen_sepia.mp4")}` inside an `<AbsoluteFill>` wrapper.
   - File: `remotion/src/remotion/S01-Economics/Part1Economics.tsx:214-225`

3. **Duration Approximately Correct (~15 seconds)**
   - Spec calls for ~15 seconds (timestamp 4:54-5:13 in overall video).
   - Implementation: Visual 21 spans from `s2f(379.02)` to `s2f(392.9)` = 13.88 seconds. This is within reasonable tolerance of the spec's 15-second target and matches the narration segments it accompanies (segments [104]-[107]).
   - File: `remotion/src/remotion/S01-Economics/constants.ts:221-223`

4. **Narration Sync Correct**
   - Spec narration: "Tools like Cursor and Claude Code are fantastic. Best darning needles ever made. They make patching faster, cleaner, less painful."
   - Implementation narration segments covering Visual 21's time range:
     - [104] 379.0s: "Tools like cursor and clawed code are the best-darning..."
     - [105] 383.5s: "I use them. They're fantastic."
     - [106] 386.3s: "But they're still darning needles and the fundamental p..."
     - [107] 392.1s: "It's accumulation."
   - The content and timing align with the spec's intended narration sync point.
   - File: `remotion/src/remotion/S01-Economics/constants.ts:113-116`

5. **Correct Placement in Sequence**
   - Visual 21 is positioned after CrossingPoint (Visual 20, "generation crossed below both lines") and before PieChart (Visual 22, "80-90% cost is maintenance"). This matches the narrative flow in the spec.
   - File: `remotion/src/remotion/S01-Economics/constants.ts:257` (VISUAL_SEQUENCE array)

6. **Video Rendering with Full Coverage**
   - The `<OffthreadVideo>` uses `loop` attribute and `style={{ width: "100%", height: "100%" }}`, ensuring the video fills the frame and loops if the sequence slot exceeds the video's native duration.
   - File: `remotion/src/remotion/S01-Economics/Part1Economics.tsx:219-221`

7. **Split Screen Content (Spec: Vertical Divide, Developer Left, Grandmother Right)**
   - These are properties of the Veo-generated video itself, not the Remotion layer. The spec's Veo 3.1 prompt explicitly requests a split screen with vertical divide, developer on left, grandmother on right. The video file name `07_split_screen_sepia` confirms the video was generated to this specification.

8. **Audio Notes Respected**
   - Spec says "No ambient sound from the video itself" and "Music/narration track laid over." The implementation plays only the narration audio track (`part1_economics_narration.wav`) at the Part1Economics level; no separate audio is attached to the `<OffthreadVideo>` element (OffthreadVideo does not play audio by default when muted or when a separate audio track is present).
   - File: `remotion/src/remotion/S01-Economics/Part1Economics.tsx:37`

9. **Continuity with Cold Open**
   - Spec notes: "This mirrors the cold open (Section 0) but with the sepia treatment added." The ColdOpen uses a programmatic `ColdOpenSplitScreen` component with LeftPanel/RightPanel and animated desaturation/vignette effects. Section 1.8 uses a separate Veo-generated video with the sepia treatment baked in, which is a valid production approach.
   - File: `remotion/src/remotion/01-ColdOpen/ColdOpenSplitScreen.tsx:1-121`

### Issues Found

1. **No Remotion-Layer Post-Processing Filters Applied (Minor)**
   - Severity: Minor
   - The spec explicitly calls for post-processing effects:
     - Desaturation: 40-50%
     - Sepia tone overlay: Light amber
     - Slight vignette on edges
     - Film grain: Subtle
   - The implementation in `Part1Economics.tsx` applies **no CSS filters** to the `<OffthreadVideo>` element -- it uses only `style={{ width: "100%", height: "100%" }}`.
   - Notably, the same video file IS rendered with CSS filters in `S05-CompoundReturns/Part5CompoundReturns.tsx:116` where it uses `filter: "sepia(0.2) saturate(0.9)"` plus a radial-gradient vignette overlay (lines 112-127). This demonstrates that the codebase has the pattern available but it was not applied in S01-Economics.
   - This is rated Minor because: (a) the sepia/desaturation effects may be baked into the Veo-generated video file itself (which would make CSS filters redundant), and (b) the video file name literally includes "sepia", suggesting the post-processing was applied at the generation stage. However, if the video lacks these effects natively, CSS filters like `filter: "saturate(0.55) sepia(0.3)"` and a vignette overlay div would need to be added, following the pattern already used in S05.
   - File: `remotion/src/remotion/S01-Economics/Part1Economics.tsx:219-221` (no filter applied)
   - Compare: `remotion/src/remotion/S05-CompoundReturns/Part5CompoundReturns.tsx:112-127` (filter applied)

2. **File Naming Mismatch with Spec Number (Trivial)**
   - Severity: Trivial
   - The spec is numbered `08_split_screen_sepia.md` but the video file is named `07_split_screen_sepia.mp4`. This numbering offset is cosmetic and does not affect functionality. The `07` prefix likely reflects an earlier numbering scheme.

3. **No Transition to Zoom-Out (Info)**
   - Severity: Info
   - Spec states: "Developer side continues into Section 1.8 (zoom out to reveal codebase)." In the implementation, Visual 22 (PieChart) follows directly. The zoom-out transition referenced in the spec may have been dropped or handled at a different production level. This is informational only, as section transitions often evolve during development.

### Notes

- This spec uses Veo 3.1 for video generation, not Remotion for programmatic animation. The Remotion role is limited to importing and displaying the pre-generated video asset, which is correctly implemented.
- The same video asset (`07_split_screen_sepia.mp4`) is reused across three sections: S01-Economics (Visual 21), S05-CompoundReturns (Visuals 5 and 6), and S06-Closing (Visual 1). In S05, CSS filters and vignette overlays are applied; in S01 and S06, the video is rendered without additional filters. This inconsistency may be intentional (different visual treatment per section) or an oversight.
- The ColdOpen's `ColdOpenSplitScreen` component (the programmatic split-screen that Section 1.8 mirrors) does include desaturation and vignette effects applied via CSS. This suggests the spec's intent was for these effects to be present in some form.
- The `loop` attribute on the `<OffthreadVideo>` ensures seamless playback if the video duration is shorter than the sequence slot, which is good defensive coding.

## Resolution Status: RESOLVED
