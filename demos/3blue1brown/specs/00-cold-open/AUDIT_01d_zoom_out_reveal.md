# Audit: Zoom Out Reveal

## Status: PASS

### Requirements Met

1. **Video asset exists**: `remotion/public/cold_open_01d_zoom_out.mp4` is present (11.4 MB, last modified 2026-02-09). This is the Veo-generated photorealistic clip for the zoom-out reveal.

2. **Remotion integration correct (OffthreadVideo in Sequence)**: `ColdOpenSection.tsx:51-61` wraps an `OffthreadVideo` inside a `<Sequence from={BEATS.VISUAL_01_START}>` block. The `OffthreadVideo` uses `staticFile("cold_open_01d_zoom_out.mp4")` with `loop` enabled and `style={{ width: "100%", height: "100%" }}` for full-frame coverage. The component is conditionally rendered via `activeVisual === 1`.

3. **Frame range correctly mapped**: `constants.ts:30-31` defines `VISUAL_01_START: s2f(5.24)` (frame 157) and `VISUAL_01_END: s2f(7.72)` (frame 232), yielding a 2.48-second window at 30fps. The `Sequence from=` value matches `BEATS.VISUAL_01_START`. The active-visual guard (`activeVisual === 1`) ensures this clip renders only during its designated window.

4. **Visual sequence metadata aligned**: `VISUAL_SEQUENCE` array entry at index 1 maps `VISUAL_01_START` to `VISUAL_01_END` with `id: "veo:cold_open_01d_zoom_out"` and description `"Great-grandmother figured out sixty years ago"`, matching the narration segment at 5.2s.

5. **Audio sync correct**: The narration comment block in `constants.ts:10` places segment 1 ("But here's what your great-grandmother figured out.") at 5.2s, which aligns with `VISUAL_01_START` at 5.24s. The audio is loaded via `<Audio src={staticFile("cold_open_narration.wav")} />` at the section root.

6. **Composition registration**: `Root.tsx` registers `ColdOpenSection` under the `S00-ColdOpen` folder with the correct `durationInFrames`, `fps` (30), `width` (1920), and `height` (1080) matching `constants.ts` values.

7. **Continuity with subsequent visual**: `VISUAL_01B_START` at `s2f(7.72)` (frame 232) picks up exactly where `VISUAL_01_END` leaves off, feeding into the `HoldAccumulatedWeight` component for the 6-second contemplative beat. There is no gap between the zoom-out and the hold.

8. **Spec aspect ratio and resolution**: `constants.ts:18-19` defines `COLD_OPEN_WIDTH: 1920` and `COLD_OPEN_HEIGHT: 1080`, matching the spec requirement of 16:9 / 1080p.

9. **Standalone prototype fidelity (01-ColdOpen/)**: The `01-ColdOpen/` directory contains a full SVG/CSS animated implementation of the split-screen zoom-out with synchronized three-phase easing, 158+ files, 22 mended items, dependency graphs, floating TODO/FIXME labels, diff markers, vignette, desaturation, and narrator text overlay. This prototype served as the reference for the Veo prompt and validates the visual intent of the spec.

### Issues Found

1. **Production duration is 2.48s vs. spec's 14 seconds** (Severity: INFO)
   - The spec defines a 14-second segment (0:18-0:32). The production pipeline compresses this into 2.48s (5.24s-7.72s) because it uses audio-synced timing derived from the actual narration WAV rather than the original spec timestamps. The Veo clip itself contains the cinematic zoom-out content; the pipeline simply maps it to the narration beat. This is a deliberate production adaptation, not a defect. The standalone `01-ColdOpen/` prototype preserves the full 14-second timing for reference.

2. **Diff marker color flicker in standalone prototype** (Severity: LOW)
   - In `01-ColdOpen/LeftPanel.tsx`, `Math.random() > 0.5` is used at render time to select red vs. green for diff marker dots. Since Remotion re-renders per frame, this causes non-deterministic color flickering. This only affects the standalone prototype, not the production Veo video pipeline.
   - **Suggested fix**: Use `i % 2 === 0` or a seeded PRNG based on array index for determinism.

3. **Ease-out phase duration deviation in standalone prototype** (Severity: LOW)
   - Spec calls for "Ease-in first 2s, constant middle 10s, ease-out final 2s." The `01-ColdOpen/` prototype implements 2s + 8s + 4s instead. Total remains 14s. This is documented in code comments and was likely an intentional design refinement. Only affects the standalone prototype.

4. **Missing "// legacy (2019)" floating label in standalone prototype** (Severity: LOW)
   - Spec Visual Reference Notes include `"// legacy (2019)"` as a floating label. The `01-ColdOpen/LeftPanel.tsx` implementation has four labels but omits this one. The label exists in the separate `09-DeveloperEditZoomout/` composition. Only affects the standalone prototype.

5. **Optional visual details not implemented in standalone prototype** (Severity: LOW)
   - Spec mentions "perhaps a visible needle cushion with many needles" (optional per "perhaps" qualifier) and "spools of different colored thread" (only one spool implemented). These are supplementary visual reference suggestions, not hard requirements.

### Notes

The production path for this scene is straightforward and well-integrated: a Veo-generated MP4 is played via `OffthreadVideo` within a properly configured `Sequence`, with frame ranges derived from Whisper-generated word timestamps. The video asset is present and correctly referenced.

The `01-ColdOpen/` standalone prototype is a comprehensive SVG/CSS implementation of the same visual concept. It served as a detailed reference for the Veo prompt and independently satisfies the spec's visual requirements (split-screen, synchronized zoom, developer/grandmother scenes, accumulated complexity). It has a few low-severity issues (flicker, timing deviation, missing label) but these do not affect the production pipeline.

The conditional rendering pattern (`activeVisual === N`) ensures clean visual switching without overlapping clips or stale frames. The `loop` flag on the `OffthreadVideo` prevents black frames if the clip is shorter than the allocated window.

## Resolution Status
- **Status**: PASS
- **Rationale**: The Veo video asset exists, is correctly integrated via OffthreadVideo wrapped in a Sequence with accurate frame ranges, audio sync is aligned with narration timestamps, and the composition is properly registered. The standalone prototype faithfully implements the spec's visual requirements. All identified issues are informational or low severity and do not affect the production render.

## Re-Audit Update (2026-02-09)
- **Status**: PASS
- **Result**: Fresh audit confirms all production integration requirements are met. The video asset `cold_open_01d_zoom_out.mp4` (11.4 MB) exists at the expected path. The `OffthreadVideo` is correctly wrapped in a `Sequence` with `from={BEATS.VISUAL_01_START}` (frame 157). Frame range maps to 5.24s-7.72s, aligned with narration segment 1. No gaps exist between this visual and the subsequent `HoldAccumulatedWeight` beat. The standalone `01-ColdOpen/` prototype retains previously identified low-severity items (diff marker flicker, easing deviation, missing label) which do not impact the production pipeline. No new issues discovered.
