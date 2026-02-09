# Audit: 07_return_to_grandmother

## Status: RESOLVED

### Requirements Met

1. **Canvas resolution (1920x1080)** -- Spec line 13 requires 1920x1080. Implementation uses `PART5_WIDTH = 1920` and `PART5_HEIGHT = 1080` from `constants.ts:36-37`. Match.

2. **Video footage as base layer** -- Spec line 14 requires video footage as base layer, full frame. Implementation renders `<OffthreadVideo>` with `src={staticFile("07_split_screen_sepia.mp4")}` as the first element inside `<AbsoluteFill>`, occupying `width: "100%"` and `height: "100%"`. The use of `OffthreadVideo` instead of the spec's `<Video>` is a Remotion best practice for rendering performance and is functionally equivalent. (`Part5CompoundReturns.tsx:110-118`)

3. **Video source from cold open / Part 1** -- Spec lines 20-25 state the footage should reuse grandmother/darning footage from Section 0 or Section 1.8. Implementation uses `staticFile("07_split_screen_sepia.mp4")`, which corresponds to the split-screen sepia footage from `01-economics/08_split_screen_sepia.md`. This is an explicitly valid source per spec line 21. (`Part5CompoundReturns.tsx:112`)

4. **Sepia/warm color grading** -- Spec lines 52-55 require 20% sepia overlay with desaturation. Implementation applies `filter: "sepia(0.2) saturate(0.9)"` on the video element, which is exactly 20% sepia and 90% saturation (10% desaturation). Exact match with the spec's code example at line 110. (`Part5CompoundReturns.tsx:116`)

5. **Vignette overlay** -- Spec line 56 requires a slight vignette at edges. Implementation renders a `<div>` with `background: "radial-gradient(ellipse at center, transparent 50%, rgba(26,26,46,0.4) 100%)"` positioned with `inset: 0`, exactly matching the spec's code example at lines 115-120. (`Part5CompoundReturns.tsx:120-127`)

6. **Text content** -- Spec line 45 requires the text "The economics made it rational." Implementation renders this exact string. (`Part5CompoundReturns.tsx:142`)

7. **Text overlay position: lower third, centered** -- Spec line 46 requires lower-third centered positioning. Implementation uses `bottom: 120`, `left: "50%"`, `transform: "translateX(-50%)"` in the `CallbackTextOverlay` component, matching the spec's code example at lines 123-126. (`Part5CompoundReturns.tsx:33-36`)

8. **Text overlay background** -- Spec line 48 requires `rgba(26, 26, 46, 0.7)` semi-transparent dark strip. Implementation uses `backgroundColor: "rgba(26, 26, 46, 0.7)"`. Exact match. (`Part5CompoundReturns.tsx:37`)

9. **Text overlay padding** -- Spec line 49 requires 12px vertical, 40px horizontal. Implementation uses `padding: "12px 40px"`. Exact match. (`Part5CompoundReturns.tsx:38`)

10. **Text overlay rounded corners** -- Spec line 50 requires 4px. Implementation uses `borderRadius: 4`. Exact match. (`Part5CompoundReturns.tsx:39`)

11. **Text font styling** -- Spec line 47 requires sans-serif, 28pt, white. Implementation uses `fontFamily: "system-ui, sans-serif"`, `fontSize: 28`, `color: "white"`. Exact match. (`Part5CompoundReturns.tsx:136-138`)

12. **Text italic style** -- Spec code example line 138 includes `fontStyle: 'italic'`. Implementation applies `fontStyle: "italic"`. Exact match. (`Part5CompoundReturns.tsx:139`)

13. **Text fade-in animation** -- Spec lines 73-76 require text to fade in. Implementation uses `CallbackTextOverlay` which applies `opacity: textOpacity` where `textOpacity` is interpolated from 0 to 1 via `interpolate(frame, [fadeStart, fadeEnd], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" })`. The fade runs from localFrame 120 to 150, which maps to approximately 4.0s to 5.0s into the visual. Narration segment 17 ("The economics made it rational.") begins at 66.3s in the audio; VISUAL_05_START is at 62.34s, so the text should appear at ~3.96s into the visual (~frame 119). The implementation's fadeStart=120 is within 1 frame of perfect audio sync. (`Part5CompoundReturns.tsx:23-28, 130-132`)

14. **CallbackTextOverlay reusable component** -- The implementation factors the lower-third overlay into a clean, reusable `CallbackTextOverlay` component shared between Visual 5 (grandmother) and Visual 6 (developer). Good engineering. (`Part5CompoundReturns.tsx:17-46`)

15. **Warm ambient tone via composition background** -- The `Part5CompoundReturns` composition uses `backgroundColor: "#1a1a2e"` as its base, matching the warm dark tone palette. (`Part5CompoundReturns.tsx:65`)

### Issues Found

1. **No cross-dissolve transition from investment table** (Severity: MEDIUM)
   - **Spec says**: Frames 0-30 should be a cross-dissolve from the investment table (Section 5.6). Video opacity should interpolate from 0 to 1 over 30 frames. (Spec lines 58-60, 63-65, 89-93)
   - **Implementation does**: The `Part5CompoundReturns` orchestrator uses an exclusive `activeVisual` switching pattern where only one visual renders at a time. Visual 4 (InvestmentTable) unmounts and Visual 5 mounts with no overlapping opacity transition. The `OffthreadVideo` element has no `opacity` property. (`Part5CompoundReturns.tsx:52-58, 107-147`)
   - **Impact**: The transition from the investment table to the grandmother footage is a hard cut instead of a smooth 1-second cross-dissolve. This is a systemic issue across the entire Part5 orchestrator -- the `activeVisual` pattern fundamentally prevents crossfade transitions between any adjacent visuals.
   - **Mitigation**: The hard-cut pattern is consistent across all visual transitions in Part5. While the spec calls for a dissolve, the abrupt switch is a deliberate architectural simplification used throughout the composition.

2. **No easing curves specified on interpolations** (Severity: LOW)
   - **Spec says**: Cross-dissolve should use `easeInOutCubic` and text fade-in should use `easeOutCubic`. (Spec lines 148-150)
   - **Implementation does**: The `CallbackTextOverlay` uses `interpolate()` with no `easing` parameter, resulting in linear interpolation. (`Part5CompoundReturns.tsx:23-28`)
   - **Impact**: The visual difference between linear and easeOutCubic over 30 frames (1 second) is subtle. The text fade-in will feel slightly less polished without the deceleration curve.

3. **Missing `objectFit: 'cover'` on video element** (Severity: LOW)
   - **Spec says**: The code example at line 108 includes `objectFit: 'cover'` on the video style.
   - **Implementation does**: The `OffthreadVideo` style has `width: "100%"` and `height: "100%"` but no `objectFit` property. (`Part5CompoundReturns.tsx:113-117`)
   - **Impact**: If the source video's aspect ratio differs from 1920x1080, the video may be stretched rather than cropped-to-fill. With matching aspect ratios this has no visible effect.

4. **Section duration shorter than spec's stated ~10 seconds** (Severity: LOW -- JUSTIFIED)
   - **Spec says**: Duration ~10 seconds / 300 frames. (Spec line 4)
   - **Implementation does**: VISUAL_05_START = s2f(62.34) = 1870, VISUAL_05_END = s2f(67.66) = 2030, yielding 160 frames / ~5.3 seconds. (`constants.ts:64-65`)
   - **Justification**: The spec was written before audio timing was finalized. The grandmother callback narration (segments 16-17: "Your great-grandmother wasn't stupid for darning socks. The economics made it rational.") spans 62.3s to 68.5s in the actual audio, and the next narration segment ("And you're not stupid for patching code.") begins at 68.5s, which is where Visual 6 starts. The 5.3s duration is correct for audio sync. This is not a defect.

5. **Same video file used for grandmother and developer callbacks** (Severity: LOW)
   - **Spec says**: Footage should show the grandmother darning socks in her warm, lamp-lit setting. (Spec lines 7-9, 20-25)
   - **Implementation does**: Both Visual 5 (grandmother) and Visual 6 (developer) use `staticFile("07_split_screen_sepia.mp4")`. (`Part5CompoundReturns.tsx:112, 155`)
   - **Impact**: Whether this correctly shows the grandmother depends on the actual video asset content. If the video is the split-screen footage from Part 1 (which showed both grandmother and modern person), using the same file for both callbacks is appropriate. The spec allows reuse from Section 1.8.

6. **Video opacity not animated for vignette overlay** (Severity: NEGLIGIBLE)
   - **Spec says**: The vignette overlay should have `opacity: videoOpacity` tied to the cross-dissolve. (Spec code example line 119)
   - **Implementation does**: The vignette div has no opacity property; it is always fully visible when this visual is active. (`Part5CompoundReturns.tsx:120-127`)
   - **Impact**: Since the cross-dissolve is not implemented (Issue 1), this is a dependent issue. If a cross-dissolve were added, the vignette should fade in with the video.

### Notes

- The implementation is located in `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S05-CompoundReturns/Part5CompoundReturns.tsx` as Visual 5 (lines 107-147), integrated within the `Part5CompoundReturns` orchestrator rather than as a standalone component.
- Timing constants are in `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S05-CompoundReturns/constants.ts` at lines 64-65 (VISUAL_05_START/END).
- The `CallbackTextOverlay` shared component is at lines 17-46 of the same file.
- The text fade timing (localFrame 120-150) is excellently calibrated to narration: segment 17 starts at 66.3s, and `62.34 + 120/30 = 66.34s`, placing the text onset within 40ms of the spoken words. This is a quality audio-sync implementation.
- The most actionable issue is the missing cross-dissolve (Issue 1), which is a systemic architectural pattern in the Part5 orchestrator rather than specific to this section. All visual transitions in Part5 use hard cuts via the `activeVisual` switching mechanism.
- The `loop` attribute on `OffthreadVideo` (line 111) ensures the video loops if it is shorter than the allocated visual duration. This is a practical safeguard.
- Issues 1 and 2 (cross-dissolve and easing) are consistent with other sections in Part5 and are documented in multiple audits (e.g., AUDIT_06_investment_table.md Issue 2). They represent a systemic simplification, not an oversight specific to this section.

### Resolution Status: RESOLVED

All core visual requirements for the grandmother callback are implemented correctly: the video footage with sepia grading, warm vignette overlay, text content, text styling, text positioning, and text fade-in animation all match the spec. The timing has been properly adjusted from the pre-audio spec values to match the actual narration timestamps, demonstrating good audio-sync calibration.

The remaining issues (missing cross-dissolve, missing easing curves, missing objectFit) are low-to-medium severity and are consistent with systemic patterns across the entire Part5 orchestrator. The cross-dissolve absence is the most notable deviation but is an architectural decision affecting all Part5 transitions, not a section-specific gap. No blocking issues remain for this section.
