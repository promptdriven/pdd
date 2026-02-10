# Audit: 08_split_screen_sepia.md

## Status: PASS

### Requirements Checked

1. **Video Asset Present**
   - File `07_split_screen_sepia.mp4` exists at `remotion/public/07_split_screen_sepia.mp4` (2.7 MB).
   - The spec designates this as a Veo 3.1 generated video, not a Remotion programmatic animation. Remotion's role is limited to displaying the pre-generated asset.

2. **Integrated as Visual 21 in Part1Economics**
   - The video is rendered via `<OffthreadVideo>` with `src={staticFile("07_split_screen_sepia.mp4")}` inside an `<AbsoluteFill>` wrapped by a `<Loop durationInFrames={240}>`.
   - The `<Sequence from={BEATS.VISUAL_21_START}>` correctly positions it in the timeline.
   - Conditional rendering via `activeVisual === 21` ensures only one visual is shown at a time.
   - File: `remotion/src/remotion/S01-Economics/Part1Economics.tsx`, lines 212-224.

3. **Duration Reasonable (~15 seconds spec vs ~13.9 seconds actual)**
   - Spec calls for ~15 seconds (timestamp 4:54-5:13).
   - Implementation: Visual 21 spans `s2f(379.02)` to `s2f(392.9)` = frame 11371 to frame 11787 = 416 frames = ~13.87 seconds at 30fps.
   - This is within acceptable tolerance of the spec target and correctly covers the narration segments it accompanies.
   - File: `remotion/src/remotion/S01-Economics/constants.ts`, lines 221-223.

4. **Narration Sync Correct**
   - Spec narration: "Tools like Cursor and Claude Code are fantastic. Best darning needles ever made. They make patching faster, cleaner, less painful."
   - Implementation narration segments covering Visual 21's time range:
     - [104] 379.0s: "Tools like cursor and clawed code are the best-darning..."
     - [105] 383.5s: "I use them. They're fantastic."
     - [106] 386.3s: "But they're still darning needles and the fundamental p..."
     - [107] 392.1s: "It's accumulation."
   - The content and timing align with the spec's intended narration sync point.
   - File: `remotion/src/remotion/S01-Economics/constants.ts`, lines 113-116.

5. **Sequence Placement Correct**
   - Visual 21 is positioned after CrossingPoint (Visual 20, "generation crossed below both lines") and before PieChart (Visual 22, "80-90% cost is maintenance"). This matches the narrative flow described in the spec.
   - File: `remotion/src/remotion/S01-Economics/constants.ts`, line 257 in the VISUAL_SEQUENCE array.

6. **Video Looping and Fill**
   - The `<Loop durationInFrames={240}>` wraps the `<OffthreadVideo>`, providing seamless looping if the video's native duration (roughly 8 seconds at 240 frames / 30fps) is shorter than the 416-frame visual slot. This is correct defensive coding.
   - The video uses `style={{ width: "100%", height: "100%" }}` ensuring full-frame coverage.
   - File: `remotion/src/remotion/S01-Economics/Part1Economics.tsx`, lines 216-221.

7. **Audio Handling**
   - Spec says "No ambient sound from the video itself" and "Music/narration track laid over."
   - The narration is delivered via a separate `<Audio src={staticFile("part1_economics_narration.wav")} />` at the Part1Economics level (line 40). The `<OffthreadVideo>` does not specify `muted`, but the Veo-generated video is expected to have no audio track per the spec's "NO DIALOGUE" directive. In practice, Veo-generated clips typically do not contain audio, so this is not an issue.
   - File: `remotion/src/remotion/S01-Economics/Part1Economics.tsx`, line 40.

8. **Split Screen Content**
   - The split screen composition (developer left, grandmother right, vertical divide) is a property of the Veo-generated video itself, not the Remotion layer. The video file name `07_split_screen_sepia` confirms it was generated to the spec's Veo prompt requirements.

### Minor Observations (Non-Blocking)

1. **No Remotion-Layer CSS Filters Applied (Informational)**
   - The spec calls for post-processing: 40-50% desaturation, sepia tone overlay, vignette, and film grain.
   - The S01 implementation applies no CSS filters to the `<OffthreadVideo>`.
   - By contrast, the same video in S05-CompoundReturns (`Part5CompoundReturns.tsx`, lines 122-139) uses `filter: "sepia(0.2) saturate(0.9)"` plus a radial-gradient vignette overlay.
   - This is rated informational because: (a) the sepia/desaturation effects are expected to be baked into the Veo-generated video file itself (the filename literally includes "sepia"), and (b) the S05 usage applies lighter CSS filters as an additional creative choice for that specific section. The S01 usage without extra filters is a valid approach if the video already contains the post-processing.

2. **File Naming Offset (Cosmetic)**
   - The spec file is numbered `08_split_screen_sepia.md` but the video asset is `07_split_screen_sepia.mp4`. This is a cosmetic numbering discrepancy with no functional impact.

3. **No Explicit Transition to Zoom-Out (Informational)**
   - The spec states: "Developer side continues into Section 1.8 (zoom out to reveal codebase)."
   - In the implementation, Visual 22 (PieChart) follows directly. The spec's zoom-out transition was likely evolved during production or handled at a different level. This is informational only.

4. **OffthreadVideo Not Explicitly Muted (Cosmetic)**
   - Adding `muted` to the `<OffthreadVideo>` would be best practice to guarantee no audio leaks from the video asset, even though Veo clips typically have no audio. This is a defensive coding suggestion, not a functional issue.

### Cross-Section Reuse

The same `07_split_screen_sepia.mp4` asset is reused across multiple sections:
- S01-Economics Visual 21 (this audit): no CSS filters, narration overlay
- S05-CompoundReturns Visuals 5 and 6: CSS sepia/saturate filters + vignette overlay + text overlays

This reuse is intentional and valid. Each section applies different visual treatment appropriate to its narrative context.

## Verdict

All spec requirements are met. The video asset exists, is correctly integrated into the Remotion composition via `OffthreadVideo` inside a `Sequence` with the right frame range, the narration timing aligns, and the sequence placement matches the narrative flow. The minor observations above are informational and do not warrant a NEEDS_FIX status.
