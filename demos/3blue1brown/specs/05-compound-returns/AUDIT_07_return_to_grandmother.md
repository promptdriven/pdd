# Audit: 07_return_to_grandmother

## Status: ISSUES FOUND

### Requirements Met

1. **Video footage with sepia/warm grading** -- The implementation uses `OffthreadVideo` with `staticFile("07_split_screen_sepia.mp4")` and applies `filter: "sepia(0.2) saturate(0.9)"`, matching the spec's 20% sepia overlay and desaturation. (Spec lines 52-56, Implementation `Part5CompoundReturns.tsx` lines 110-118)

2. **Vignette overlay** -- A radial gradient vignette is applied: `radial-gradient(ellipse at center, transparent 50%, rgba(26,26,46,0.4) 100%)`, exactly matching the spec's code example. (Spec lines 114-120, Implementation lines 119-127)

3. **Text content** -- The text "The economics made it rational." is correctly rendered. (Spec line 45, Implementation line 142)

4. **Text overlay styling** -- The text overlay matches the spec precisely:
   - Background: `rgba(26, 26, 46, 0.7)` -- matches spec
   - Padding: `12px 40px` -- matches spec
   - Border radius: `4px` -- matches spec
   - Font: `system-ui, sans-serif`, 28px, white -- matches spec
   - Position: `bottom: 120`, centered via `left: 50%` + `translateX(-50%)` -- matches spec lower-third positioning
   (Spec lines 44-51, Implementation via `CallbackTextOverlay` lines 30-45 and text span lines 134-143)

5. **Text italic style** -- Implementation adds `fontStyle: "italic"` matching the spec's code example. (Spec line 138, Implementation line 139)

6. **Canvas resolution** -- Composition uses 1920x1080 as specified. (Spec line 13, constants.ts lines 36-37)

7. **CallbackTextOverlay reusable component** -- A clean, reusable `CallbackTextOverlay` component encapsulates the lower-third pattern, used by both Visual 5 (grandmother) and Visual 6 (developer). (Implementation lines 17-46)

### Issues Found

1. **No cross-dissolve transition from investment table**
   - **Spec says**: Frame 0-30 cross-dissolve from investment table; video opacity interpolates from 0 to 1 over 30 frames with `easeInOutCubic` easing. (Spec lines 58-60, 63-65, 89-93, 148-149)
   - **Implementation does**: The `activeVisual` switching mechanism performs a hard cut -- Visual 4 (InvestmentTable) is unmounted and Visual 5 is mounted with no overlapping opacity transition. The `OffthreadVideo` has no `opacity` property at all.
   - **Severity**: Medium -- Spec explicitly calls for a 1-second cross-dissolve but implementation uses an abrupt cut.

2. **Text fade-in timing differs from spec**
   - **Spec says**: Text fades in at frames 150-210 relative to section start (5-7 seconds in), matching narration of "The economics made it rational." (Spec lines 73-76, 95-98)
   - **Implementation does**: Text fades at local frames 120-150 (4-5 seconds into this visual segment). Since the visual segment itself is only ~5.3 seconds long, the text appears proportionally similar, but the absolute frame numbers differ from the spec's reference code.
   - **Severity**: Low -- The timing has been adjusted to match actual audio timestamps (narration segment 17 at 66.3s), which is a reasonable deviation from the pre-audio spec timings.

3. **No easing curves on text fade-in**
   - **Spec says**: Text fade-in should use `easeOutCubic` easing. (Spec line 150)
   - **Implementation does**: `CallbackTextOverlay` uses linear `interpolate` with no `easing` parameter specified. (Implementation lines 23-27)
   - **Severity**: Low -- The visual difference between linear and easeOutCubic over 30 frames (1 second) is subtle but specified.

4. **Section duration shorter than spec**
   - **Spec says**: ~10 seconds / 300 frames. (Spec line 4)
   - **Implementation does**: VISUAL_05_START at s2f(62.34) = 1870 frames, VISUAL_05_END at s2f(67.66) = 2030 frames, yielding ~160 frames / ~5.3 seconds. (constants.ts lines 64-65)
   - **Severity**: Low -- The duration was adjusted to match the actual narration timing. The grandmother callback narration (segments 16-17, "Your great-grandmother..." through "The economics made it rational.") spans approximately 62.3s to 68.5s in the audio, so 5.3 seconds is correct for the audio sync. The spec was written before audio timing was finalized.

5. **Video source naming**
   - **Spec says**: Footage should be from cold open (Section 0) or Part 1 grandmother darning socks footage, or newly generated Veo clip of grandmother's hands darning by lamplight. (Spec lines 20-40)
   - **Implementation does**: Uses `07_split_screen_sepia.mp4`, which is the same file used for Visual 6 (developer callback). The filename suggests split-screen sepia footage from section 1.8, which is one of the valid spec sources. However, using the same file for both the grandmother callback and developer callback may not match the spec's intent of showing distinct footage for each.
   - **Severity**: Low -- The spec allows reuse from Section 1.8, and the filename aligns with `01-economics/08_split_screen_sepia.md`. Whether the footage content correctly shows the grandmother (not the developer) depends on the actual video asset.

### Notes

- The implementation is located in `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S05-CompoundReturns/Part5CompoundReturns.tsx` as Visual 5 (lines 107-147), not as a standalone composition.
- The previous audit incorrectly marked this as "NOT IMPLEMENTED." The grandmother callback is fully implemented as part of the `Part5CompoundReturns` sequence composition.
- The `CallbackTextOverlay` component (lines 17-46) is a well-factored shared element used by both Visual 5 and Visual 6.
- Timing constants are in `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S05-CompoundReturns/constants.ts` -- VISUAL_05_START/END at lines 64-65.
- The most actionable issue is the missing cross-dissolve transition (Issue 1). The other issues are minor deviations, most of which result from adapting the spec to real audio timing.
