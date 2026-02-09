# Audit: 04_defect_discovered.md

## Status: ISSUES FOUND

### Requirements Met

1. **Hybrid approach (Veo + Remotion overlay):** The implementation uses `OffthreadVideo` for `veo_defect_discovered.mp4` with Remotion SVG overlays (MoldScene, DefectHighlight) composited on top, matching the spec's hybrid approach.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/DefectDiscovered.tsx:96-112`

2. **Defect highlight -- red pulsing circle:** Red circle (`#D94A4A`) with pulsing animation (radius oscillation and opacity pulse) and Gaussian blur glow filter. Matches spec requirement for "Red circle or indicator appears, pulsing animation."
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/DefectHighlight.tsx:34-41, 82-104`

3. **"DEFECT" label:** Red badge with white text, uppercase, appears at frame 150 with upward slide animation. Spec says label is optional; implementation includes it.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/DefectHighlight.tsx:108-136`

4. **Zoom effect:** Scale transform from 1x to 2.5x with translate to keep defect centered on screen. Matches spec requirement for "Camera pushes in on the defective part."
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/DefectDiscovered.tsx:28-62`

5. **Other parts fade/blur:** Good parts fade to 15% opacity during zoom phase, focusing attention on the defect. Matches spec: "Other parts fade or blur, focus narrows to the flaw."
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/MoldScene.tsx:70-82`

6. **Defect visualization:** Implements crack lines (diagonal and branch) plus missing corner chunk (triangle cut-out). Spec lists multiple defect type options; implementation combines crack/fracture with incomplete fill, which is a good visual choice.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/MoldScene.tsx:213-242`

7. **Defect color -- red-tinted part:** The defective part itself is filled with `#D94A4A` (red) to distinguish it from good amber parts (`#D9944A`). This clearly communicates "something is wrong."
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/MoldScene.tsx:211`

8. **Narration text:** "And when there's a defect?" matches the spec's rhetorical setup narration. The narration is rendered outside the zoom container so text stays readable during zoom.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/DefectDiscovered.tsx:114-141`

9. **Duration (standalone):** 10 seconds / 300 frames at 30fps. Matches spec's "~10 seconds."
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/constants.ts:4-6`

10. **Mold position consistency:** `MOLD.centerX` is 580, matching PartsEject (Section 2.3). Ensures visual continuity between sections. Previously flagged and resolved.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/constants.ts:46`

11. **Dark overlay for contrast:** 40% opacity dark overlay (`rgba(10, 10, 26, 0.4)`) over video background improves visibility of SVG overlays against the Veo footage.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/DefectDiscovered.tsx:100-109`

12. **Production cycling before defect:** Shows 2 full mold cycles with good parts ejecting before the defect appears (frames 0-60), adding context and making the defect moment more impactful.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/MoldScene.tsx:48-67`

13. **Animation sequence structure:** Four-phase beat structure (production, defect eject, pause/highlight, zoom/hold) follows spec's Option B animation sequence timing.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/constants.ts:11-26`

### Issues Found

1. **Parent composition duration mismatch (High severity)**
   - **Spec says:** Duration ~10 seconds (300 frames at 30fps).
   - **Implementation does:** The standalone composition is correctly 300 frames (10s). However, in the parent `Part2ParadigmShift` sequence, DefectDiscovered is only allocated ~126 frames (~4.2 seconds): `VISUAL_03_START = s2f(29.02) = 871` to `VISUAL_03_END = s2f(33.24) = 997`.
   - **Impact:** When played in context, the composition only runs through frames 0-126. The zoom phase (frames 180-300) and narration overlay (frame 250+) are never reached. The defect highlight only gets 6 frames of visibility (starts at frame 120, cut off at ~126). The "DEFECT" label (frame 150) is never shown.
   - **Files:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S02-ParadigmShift/constants.ts:63-65` and `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/constants.ts:4-6`

2. **Highlight start frame differs from spec overlay example (Low severity)**
   - **Spec says:** The hybrid overlay specification shows `<Sequence from={90}>` for the DefectHighlight.
   - **Implementation does:** Highlight appears at frame 120 (`BEATS.PAUSE_HIGHLIGHT_START`).
   - **Impact:** The highlight appears 1 second later than the spec's overlay example suggests. This may be intentional to align with the four-phase beat structure (Option B timing), but deviates from the explicit hybrid overlay code in the spec.
   - **File:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/constants.ts:20`

3. **Audio cues not implemented (Low severity)**
   - **Spec says:** "Subtle 'alert' sound when defect highlighted" and "Production sounds stop or quiet."
   - **Implementation does:** No audio elements are present in the DefectDiscovered component. Audio is handled at the parent `Part2ParadigmShift` level as a single narration track with no per-section sound effects.
   - **File:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/15-DefectDiscovered/DefectDiscovered.tsx` (no `<Audio>` element)

### Notes

- The standalone composition (`DefectDiscovered` in Root.tsx) renders correctly at the full 300-frame / 10-second duration with all phases visible. The duration mismatch only affects the integrated `Part2ParadigmShift` playback.
- The parent S02 narration segment [6] covers "And when there's a defect, you don't patch individual parts..." from 29.0s to 33.9s. The component's narration overlay only shows "And when there's a defect?" (the rhetorical question portion), which is appropriate since the sentence continues into the next section (PerfectParts). When played in the parent sequence with `showNarration=true` (default), the narration text would appear at frame 250 relative to the component -- which is unreachable in the 126-frame window, so the built-in narration text is effectively invisible. This may be acceptable if the narration is handled entirely by the parent audio track.
- The `pulseSpeed` parameter from the spec overlay example (`pulseSpeed={30}`) is not directly used as a prop. Instead, pulsing is hardcoded with a phase multiplier of `0.12` per frame, producing a full pulse cycle roughly every 52 frames (~1.7 seconds). This is a reasonable visual rate.
- The implementation adds a useful enhancement: mold vibration during production (`Math.sin(frame * 3) * 1.5` for X, `Math.cos(frame * 4.7) * 1` for Y) that stops when production pauses, reinforcing the "something stopped" moment.
