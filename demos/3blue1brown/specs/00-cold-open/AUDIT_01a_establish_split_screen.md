# Audit: Establish Split Screen

## Status: PASS

### Requirements Met

1. **Veo video asset exists and is correctly referenced**: The file `remotion/public/cold_open_01a_establish.mp4` exists on disk (3,730,833 bytes). In `ColdOpenSection.tsx` line 43, the asset is loaded via `staticFile("cold_open_01a_establish.mp4")`, which correctly resolves to the `remotion/public/` directory. The VISUAL_SEQUENCE entry at `constants.ts` line 68 maps this to `id: "veo:cold_open_01a_establish"`.

2. **OffthreadVideo correctly wrapped in Sequence**: `ColdOpenSection.tsx` lines 38-48 render the video inside a `<Sequence from={BEATS.VISUAL_00_START}>` (frame 0) containing an `<AbsoluteFill>` containing an `<OffthreadVideo>`. The `loop` prop is set, ensuring no black frame if the source clip is shorter than the visual window. The `style={{ width: "100%", height: "100%" }}` ensures the video fills the composition.

3. **Frame range is correct**: `VISUAL_00_START = s2f(0.0) = 0` and `VISUAL_00_END = s2f(4.92) = 148` at 30 fps. The `activeVisual === 0` condition keeps this video rendered from frame 0 until `VISUAL_01_START` (frame 157), providing seamless coverage with no gap or black flash. The 9-frame overlap (148-156) between VISUAL_00_END and VISUAL_01_START is handled by the `loop` prop.

4. **FPS and resolution match**: `constants.ts` defines `COLD_OPEN_FPS = 30`, `COLD_OPEN_WIDTH = 1920`, `COLD_OPEN_HEIGHT = 1080`. The Root composition at `Root.tsx` line 1028-1036 registers the ColdOpenSection with these exact values (aliased as `COLD_OPEN_SECTION_FPS`, `COLD_OPEN_SECTION_WIDTH`, `COLD_OPEN_SECTION_HEIGHT`). This matches the spec's 16:9 / 1080p requirement.

5. **Audio sync alignment**: The narration segment comment at `constants.ts` line 9 maps "If you use cursor or clawed code or copilot..." to 0.0s, and the VISUAL_00 window (0.0s-4.92s) covers this first narration beat. The Whisper-derived timestamps ensure the Veo establish clip plays during the correct narration.

6. **Conditional rendering pattern is correct**: The `activeVisual` variable is computed by iterating VISUAL_SEQUENCE in reverse and finding the last entry where `frame >= entry.start`. For VISUAL_00, `activeVisual === 0` is true when `frame >= 0` and `frame < 157` (VISUAL_01_START). This ensures exclusive rendering -- only one visual is mounted at a time, preventing overlapping video decodes.

7. **Spec duration (8 seconds) vs production duration (4.92 seconds)**: The spec calls for an 8-second establish segment. The production timing is compressed to 4.92 seconds to match actual narration pacing from the Whisper-derived audio timestamps. This is an intentional production decision, not a defect. The animatic in `01-ColdOpen/` retains the original 8-second timing.

8. **Composition structure is well-formed**: The component hierarchy is `<AbsoluteFill> -> <Sequence from=0> -> <AbsoluteFill> -> <OffthreadVideo>`. The outer AbsoluteFill provides the `backgroundColor: "#1a1a2e"` fallback. All Remotion primitives are correctly imported from "remotion" (line 1-11).

### Issues Found

1. **LOW -- Production duration shorter than spec's 8 seconds**: The spec defines an 8-second establish phase, but the production VISUAL_00 spans only 4.92 seconds (0-148 frames at 30fps). This is an intentional adjustment to match audio-synced narration timing. The Veo prompt was written for 8 seconds of content, so the video clip may be longer than needed, but the `loop` prop and frame range clamp prevent any issue. No action required.

2. **INFO -- Veo clip content cannot be programmatically verified**: The spec describes a split-screen with developer on left and grandmother darning on right. Since `cold_open_01a_establish.mp4` is a Veo-generated video, the actual visual content cannot be verified through code audit alone. Visual QA review of the rendered output is recommended to confirm the Veo clip matches the prompt description (split screen, white divider, cool/warm lighting contrast, static camera, both subjects in medium shot).

3. **INFO -- No startFrom prop on OffthreadVideo**: The `OffthreadVideo` does not use a `startFrom` prop, meaning playback begins at the start of the source clip. This is correct for scene 01a (the first visual), but worth noting that if the Veo clip has any leader/slate frames, they would be visible. Assumed not to be an issue for Veo-generated content.

### Notes

- This is a Veo scene, meaning the visual content is an AI-generated video file rather than a procedurally animated Remotion composition. The audit scope focuses on: (a) asset existence, (b) correct Remotion integration (Sequence, OffthreadVideo, frame ranges), and (c) timing alignment with narration audio.
- The animatic fallback in `01-ColdOpen/` (ColdOpenSplitScreen.tsx, LeftPanel.tsx, RightPanel.tsx) provides a procedural approximation of the spec for development/preview purposes. The previous audit covered this in detail. The production path in `S00-ColdOpen/ColdOpenSection.tsx` supersedes the animatic with Veo footage.
- The `activeVisual` switching pattern used throughout ColdOpenSection.tsx is a clean approach that prevents multiple videos from being decoded simultaneously. Each visual is conditionally mounted only during its active frame range.
- The `loop` prop on OffthreadVideo is a defensive choice -- if the Veo clip is shorter than 4.92 seconds (148 frames), it will seamlessly loop rather than showing a black frame. If the clip is longer, Remotion will only render the needed portion.
- The VISUAL_SEQUENCE array at `constants.ts` lines 67-75 serves as a clean mapping table between beat timings and visual IDs, making the production timeline easy to audit and adjust.

## Resolution Status
- **Status**: PASS
- **Rationale**: The Veo video asset exists, is correctly loaded via OffthreadVideo inside a properly configured Sequence, frame ranges align with audio-synced BEATS constants, FPS and resolution match the composition registration, and the conditional rendering logic ensures clean visual switching. The compressed timing (4.92s vs spec's 8s) is an intentional narration-pacing decision. No functional defects found.

## Re-Audit Update (2026-02-09)
- **Status**: PASS
- **Result**: Fresh audit confirms all Remotion integration points are correct. Video asset `cold_open_01a_establish.mp4` (3.73 MB) exists at the expected path. OffthreadVideo is properly wrapped in a Sequence starting at frame 0, with loop enabled. Frame range (0-148 at 30fps = 4.92s) aligns with BEATS.VISUAL_00_START/END. The activeVisual conditional rendering pattern correctly isolates this visual to its designated frame window. Root.tsx composition registration uses matching FPS (30), dimensions (1920x1080), and duration from constants. No issues requiring code changes were found.
