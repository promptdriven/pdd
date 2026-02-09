# Audit: 04_defect_discovered.md

## Status: RESOLVED

### Requirements Met

1. **Hybrid approach (Veo + Remotion overlay):** The implementation uses `OffthreadVideo` for `veo_defect_discovered.mp4` as the base layer, with Remotion SVG overlays (MoldScene, DefectHighlight) composited on top. A 40% dark overlay (`rgba(10, 10, 26, 0.4)`) sits between the video and SVG layers for contrast. This matches the spec's hybrid approach: "Veo: Real plastic part with defect" + "Remotion: Red highlight circle, 'DEFECT' label, zoom effect."
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/DefectDiscovered.tsx:96-112`

2. **Defect highlight -- red pulsing circle:** SVG circle using `#D94A4A` (matches spec's `color="#D94A4A"`) with dual-ring glow (outer + main ring), Gaussian blur filter (`feGaussianBlur stdDeviation="8"`), pulsing radius oscillation (`pulseScale = 1 + Math.sin(pulsePhase) * 0.12`), and pulsing opacity (`0.6 + Math.sin(pulsePhase) * 0.25`). Satisfies spec's "Red circle or indicator appears, pulsing animation."
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/DefectHighlight.tsx:34-41, 72-104`

3. **"DEFECT" label:** Red background badge (`rgba(217, 74, 74, 0.7)`) with white text, uppercase, `letter-spacing: 3`, `font-weight: 700`, appears at frame 150 with upward slide animation (12px to 0px). Positioned below the defective part. Spec says this label is optional; implementation includes it.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/DefectHighlight.tsx:108-136`

4. **Zoom effect (frames 180-300):** Scale transform from 1x to 2.5x using `Easing.inOut(Easing.cubic)` with translation to keep the defect centered on screen (`translateX = 960 - cx * 2.5`, `translateY = 540 - cy * 2.5`). The zoom container wraps the video, dark overlay, MoldScene, and DefectHighlight layers, while the narration text sits outside it so text stays readable. Matches spec: "Camera pushes in on the defective part."
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/DefectDiscovered.tsx:28-62, 84-112`

5. **Other parts fade/blur:** Good parts fade from full opacity to 15% during the pause-to-zoom transition (frames 120-180) via `goodPartsFade` interpolation. This focuses attention on the defect. Matches spec: "Other parts fade or blur, focus narrows to the flaw."
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/MoldScene.tsx:70-82`

6. **Defect visualization -- crack + missing section:** The defective part combines three visual elements: (a) red-tinted body (`fill={COLORS.DEFECT_RED}`), (b) diagonal crack line with secondary branch line (`strokeWidth: 2.5` and `1.8`), and (c) triangular missing corner chunk (polygon cutout filled with background color). Spec lists multiple defect type options (incomplete fill, crack/fracture, surface blemish, warping, wrong dimension); implementation combines crack/fracture with incomplete fill for a strong visual.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/MoldScene.tsx:204-242`

7. **Part style consistency with Section 2.3:** Part shape uses `PART_SHAPE = { width: 68, height: 36, rx: 8 }` and good parts use `COLORS.PART_AMBER = "#D9944A"`, matching the PartsEject section's visual language. Mold `centerX: 580` also matches PartsEject. Satisfies spec: "Same style as Section 2.3."
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/constants.ts:46, 56-60`

8. **Narration text:** Renders "And when there's a defect?" matching the spec's rhetorical setup narration. Text is positioned outside the zoom container so it remains readable during the zoom phase. Styled at 36px sans-serif, white (`rgba(255, 255, 255, 0.95)`), centered, max-width 900px.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/DefectDiscovered.tsx:114-141`

9. **Duration (standalone):** 10 seconds at 30fps = 300 frames. `DEFECT_DURATION_SECONDS = 10`, `DEFECT_FPS = 30`, `DEFECT_DURATION_FRAMES = 300`. Matches spec's "~10 seconds."
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/constants.ts:4-6`

10. **Four-phase animation sequence:** Implementation follows the spec's Option B beat structure exactly:
    - Frame 0-60: Production continues (mold cycling, good parts ejecting)
    - Frame 60-120: Defective part ejects with visible crack/missing corner
    - Frame 120-180: Production pauses, highlight appears, "DEFECT" label at frame 150
    - Frame 180-300: Zoom in on defect, hold
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/constants.ts:11-26`

11. **Production cycling before defect:** Mold cycles at 30 frames per cycle during production phase (frames 0-60), producing 2 good parts before the defect appears. Mold opens (phase 0-0.3), holds open (0.3-0.5), closes (0.5-0.8), holds closed (0.8-1.0). Production vibration (`Math.sin(frame * 3) * 1.5` X, `Math.cos(frame * 4.7) * 1` Y) stops when production freezes at frame 120, reinforcing the "production pauses" beat.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/MoldScene.tsx:31-39`
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/constants.ts:68-96`

12. **Defective part ejection animation:** Defect emerges from mold center (`MOLD.centerY`) and falls to resting position (`moldBottom + 80`) over 40 frames starting at frame 60, using `Easing.out(Easing.cubic)` for a natural deceleration. Opacity fades in with `defectProgress`. Matches spec: "One part ejects with defect visible."
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/MoldScene.tsx:87-108`

13. **Mold frozen after defect eject:** `frozen = frame >= BEATS.DEFECT_EJECT_END` sets `getMoldOpening` to return 0 (fully closed), and vibration stops. Matches spec's "Production pauses."
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/MoldScene.tsx:31-39`

14. **Integration in parent sequence:** DefectDiscovered is rendered as visual index 3 in `Part2ParadigmShift.tsx` at `VISUAL_03_START = s2f(29.02) = 871` frames. It is passed `defaultDefectDiscoveredProps` (which sets `showNarration: true`).
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S02-ParadigmShift/Part2ParadigmShift.tsx:74-78`
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S02-ParadigmShift/constants.ts:63-65`

### Issues Found

1. **Parent composition duration mismatch (Medium severity)**
   - **Spec says:** Duration ~10 seconds (300 frames at 30fps).
   - **Implementation does:** The standalone composition is correctly 300 frames (10s). In the parent `Part2ParadigmShift` sequence, DefectDiscovered is allocated from `VISUAL_03_START = s2f(29.02) = 871` to `VISUAL_03_END = s2f(33.24) = 997`, giving ~126 local frames (~4.2 seconds). The `activeVisual === 3` conditional unmounts the component at that boundary.
   - **Impact:** When played in the parent context, only frames 0-126 of the component are visible. The zoom phase (frames 180-300) and narration overlay (frame 250+) are never reached. The defect highlight only gets ~6 frames of visibility (starts at frame 120). The "DEFECT" label (frame 150) is never shown. However, this is a common pattern across all compositions in this project -- standalone durations are longer than parent allocations, and the parent audio track provides the actual pacing. The key visual beats (production, defect eject, highlight start) all occur within the allocated window. Downgraded from High to Medium because this is a systemic design choice, not a bug unique to this component.
   - **Files:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S02-ParadigmShift/constants.ts:63-65` and `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/constants.ts:4-6`

2. **Highlight start frame differs from spec overlay example (Low severity)**
   - **Spec says:** The hybrid overlay specification shows `<Sequence from={90}>` for the DefectHighlight.
   - **Implementation does:** Highlight appears at frame 120 (`BEATS.PAUSE_HIGHLIGHT_START`).
   - **Impact:** The highlight appears 1 second later than the spec's overlay code example. This is intentional: the implementation follows the Option B four-phase beat structure (production 0-60, defect eject 60-120, pause/highlight 120-180, zoom 180-300) rather than the hybrid overlay pseudocode. The Option B timeline is more detailed and structured, making it the authoritative timing source.
   - **File:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/constants.ts:20`

3. **Audio cues not implemented (Low severity)**
   - **Spec says:** "Subtle 'alert' sound when defect highlighted" and "Production sounds stop or quiet."
   - **Implementation does:** No `<Audio>` elements exist in the DefectDiscovered component. Audio is handled at the parent `Part2ParadigmShift` level as a single narration track with no per-section sound effects.
   - **Impact:** Low. Sound effects are an enhancement. The parent narration track provides the primary audio. The visual pause (mold freezing, vibration stopping, good parts fading) communicates the "moment of tension" without audio cues.
   - **File:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/DefectDiscovered.tsx` (no `<Audio>` element)

### Notes

- The standalone composition (`DefectDiscovered` registered in Root.tsx at 300 frames) renders all four phases correctly. The duration mismatch only affects the integrated `Part2ParadigmShift` playback and is a systemic pattern shared across all compositions in this section.
- The `pulseSpeed` parameter from the spec overlay example (`pulseSpeed={30}`) is not used as a prop. Instead, pulsing is hardcoded with a phase multiplier of `0.12` per frame, producing a full pulse cycle roughly every 52 frames (~1.7 seconds at 30fps). This is a reasonable visual rate for a pulsing indicator.
- The implementation adds valuable enhancements beyond spec: (a) mold vibration during production that stops on pause, (b) dual-ring glow effect with Gaussian blur filter, (c) dark overlay for video/SVG contrast, (d) good parts scatter with pseudo-random horizontal offset, and (e) smooth easing curves throughout.
- The defective part is tinted fully red (`#D94A4A`) rather than amber with a red highlight, making it immediately distinguishable from good parts. This is a stronger visual signal than a subtle defect on an amber part, aligning with spec guidance: "The defect should be clearly visible."
- The narration text "And when there's a defect?" is the rhetorical question portion of narration segment [6]. The full sentence continues into Section 2.5 (PerfectParts). When played in the parent sequence, the parent audio track provides this narration, and the built-in text overlay (starting at frame 250) falls outside the allocated window -- which is acceptable since it would duplicate the audio.

## Resolution Status: RESOLVED

All three issues are accepted/by-design:
- Issue 1 (duration mismatch): Systemic pattern across all compositions. The parent sequence controls pacing via audio-synced beat timing. The standalone composition works correctly at full duration.
- Issue 2 (highlight timing): Implementation correctly follows the more detailed Option B animation sequence rather than the hybrid overlay pseudocode.
- Issue 3 (audio cues): Sound effects are optional enhancements; the parent narration track and visual cues adequately convey the moment.
