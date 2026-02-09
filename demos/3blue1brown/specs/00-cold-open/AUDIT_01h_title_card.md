# Audit: 01h Title Card

## Status: RESOLVED

## Spec Summary
Title card (~10 seconds, 1:50-2:00): "Prompt-Driven Development" fades in over dimmed regenerated code from previous scene. Code remains visible but recedes. Title is centered, clean, and authoritative. No narration -- a silent beat. Includes vignette framing, subtle blue glow behind title, editor chrome fade-out, and a 6-second contemplative hold.

## Implementation Locations
The title card is implemented as **VISUAL_04** within `S00-ColdOpen/ColdOpenSection.tsx` (lines 117-157). Timing constants are in `S00-ColdOpen/constants.ts` (lines 42-43). No standalone TitleCard component exists. The `01-ColdOpen/` directory contains an alternative split-screen composition that does not include a title card. The `50-FadeToBlack/FadeToBlack.tsx` contains a separate closing title card for the end of the video (not this spec).

**Files reviewed:**
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/ColdOpenSection.tsx` (primary implementation, VISUAL_04 at lines 117-157)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/constants.ts` (timing at lines 42-43)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/index.ts` (exports)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/01-ColdOpen/ColdOpenSplitScreen.tsx` (alternative composition, no title card)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/01-ColdOpen/LeftPanel.tsx` (alternative composition panels)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/01-ColdOpen/RightPanel.tsx` (alternative composition panels)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/01-ColdOpen/constants.ts` (alternative timing)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/50-FadeToBlack/FadeToBlack.tsx` (separate closing title card, not this spec)

### Requirements Met

1. **Title text content**: "Prompt-Driven Development" is correctly displayed (ColdOpenSection.tsx:152).

2. **Font family**: `Inter, system-ui, sans-serif` (ColdOpenSection.tsx:144). Spec says "Inter (or system sans-serif fallback)". Match.

3. **Font weight**: 600 (semi-bold) (ColdOpenSection.tsx:146). Spec says 600. Match.

4. **Font size**: 72px (ColdOpenSection.tsx:145). Spec says ~72px. Match.

5. **Text color**: `#F8F4F0` (ColdOpenSection.tsx:147). Spec says `#F8F4F0` (warm white). Match.

6. **Letter-spacing**: `0.02em` (ColdOpenSection.tsx:148). Spec says 0.02em. Match.

7. **Title fade-in with upward drift**: Title fades from opacity 0 to 1 while translateY moves from +20px to 0px (ColdOpenSection.tsx:140, 143). Spec says "Fade in with slight upward drift (20px translate-Y, settles to 0)". Match on animation concept.

8. **Blue glow color present**: Text-shadow includes `rgba(74, 144, 217, 0.15)` (ColdOpenSection.tsx:150). The color #4A90D9 = rgb(74, 144, 217) matches the spec's glow color, and 0.15 matches the spec's target glow opacity.

9. **Dimmed code backdrop from previous scene**: The clean regenerated code from VISUAL_03 is displayed behind the title at reduced opacity (ColdOpenSection.tsx:122-131). The code content on line 130 is identical to the clean code in VISUAL_03 at line 98, maintaining visual continuity.

10. **No narration**: This visual has no narration overlay. The spec says "No narration. This is a silent beat -- a title card." The narration audio from the cold open track ("So why are we still patching?") plays during this visual, but no additional narration is added. Match.

11. **Canvas resolution**: 1920x1080 (constants.ts:18-19). Match.

12. **Center alignment**: Title is centered using flexbox with `alignItems: "center"` and `justifyContent: "center"` (ColdOpenSection.tsx:138-139). Spec says centered horizontally and vertically. Match.

13. **Title fade-in easing**: `interpolate` with default linear easing between frames 0-60 relative to VISUAL_04_START (ColdOpenSection.tsx:140). Spec says `easeOutCubic`. Partial match -- the animation exists but uses the wrong easing curve.

### Issues Found

#### Issue 1: Duration is drastically shorter than spec (HIGH)
- **Spec says**: ~10 seconds (timestamp 1:50-2:00). Frame 0-60 for code dim, frame 30-90 for title fade, frame 90-270 for hold, frame 270-300 for transition prep.
- **Implementation does**: VISUAL_04 runs from s2f(14.1) to s2f(15.96), which is frames 423-479 at 30fps -- only 1.87 seconds total (constants.ts:42-43). The entire cold open section is 19 seconds (constants.ts:16-17), whereas the spec's cold open extends to 2:00.
- **Impact**: The title card, described as the "poster frame" of the entire video, has no time to register with the viewer before the section ends.

#### Issue 2: No hold period -- "pure stillness" is absent (HIGH)
- **Spec says**: Frames 90-270 (3-9s) should be a 6-second static hold. "No animation -- pure stillness. This is the moment the viewer reads and absorbs the title. The silence (no narration) gives the title weight."
- **Implementation does**: Title fades in over frames 0-60 relative to VISUAL_04_START (2 seconds at 30fps), leaving only ~0.13 seconds before the section ends. No contemplative hold exists.
- **Impact**: The deliberate rhetorical pause between "So why are we still patching?" and the title "Prompt-Driven Development" is lost. The spec describes this silence as giving both the question and the answer room to breathe.

#### Issue 3: Code dimming is static, not animated (MEDIUM)
- **Spec says**: Code opacity animates from 1.0 to 0.15 over the first 2 seconds using `easeInOutCubic`, creating a "crossfade from code to title backdrop."
- **Implementation does**: Code backdrop is a static `opacity: 0.25` (ColdOpenSection.tsx:127) with no animation. The opacity value is also slightly different (0.25 vs spec's 0.15 target).
- **Impact**: The choreographed crossfade where "title arrives as code recedes" is absent. The code is already dim when the visual starts.

#### Issue 4: No vignette overlay (MEDIUM)
- **Spec says**: "Soft radial vignette, darkening edges. Center bright, edges at ~85% darkness. Creates natural focus on the centered title." Vignette fades from 0 to target opacity over frames 0-60.
- **Implementation does**: No vignette overlay exists in VISUAL_04. The `01-ColdOpen/ColdOpenSplitScreen.tsx` does implement a radial-gradient vignette (line 82) for the split-screen composition, but it is not present in the title card.
- **Impact**: The spec's "natural focus on the centered title" through vignette framing is absent.

#### Issue 5: No editor chrome or terminal fade-out transition (MEDIUM)
- **Spec says**: "Editor chrome (top bar, gutter) fades out" (opacity 1.0 to 0.0 over frames 0-45). "Terminal snippet in bottom-right fades out completely (opacity to 0)" over frames 0-30. "Cursor stops blinking and disappears."
- **Implementation does**: VISUAL_03 shows a terminal indicator (`$ pdd generate user_parser` at ColdOpenSection.tsx:111), but the activeVisual switching logic (lines 18-24) creates a hard cut between visuals. When VISUAL_04 begins, VISUAL_03 elements are instantly removed from the DOM rather than fading out. No editor chrome (top bar, line number gutter) exists in either visual to fade.
- **Impact**: The transition from code-regeneration scene to title card is abrupt rather than the spec's choreographed crossfade.

#### Issue 6: Glow implementation differs from spec (LOW)
- **Spec says**: Glow is a separate `<div>` behind the title text with `radial-gradient(ellipse at center, rgba(74,144,217,glowOpacity), transparent 70%)`, `filter: blur(20px)`, spanning `inset: -40px`. Bloom radius ~40px.
- **Implementation does**: Glow is a text-shadow property: `0 0 60px rgba(74, 144, 217, 0.15)` (ColdOpenSection.tsx:150). The bloom radius is 60px vs spec's 40px. The second shadow `0 0 40px rgba(0,0,0,0.8)` adds a dark drop shadow not in the spec.
- **Impact**: Visual result is similar -- faint blue glow behind text -- but technically differs. The text-shadow approach creates a tighter glow halo; the spec's radial-gradient approach creates a broader atmospheric bloom.

#### Issue 7: No separate glow fade-in animation (LOW)
- **Spec says**: Glow intensity animates independently from 0 to 0.15 over frames 45-90, starting after the title fade begins at frame 30.
- **Implementation does**: Glow is part of the text-shadow property, so it fades in coupled with the title's opacity (frames 0-60 of VISUAL_04). No separate animation timeline for the glow.
- **Impact**: The spec's effect of the glow "blooming gently" as a delayed accent after the title is already partly visible is lost.

#### Issue 8: Title fade-in timing does not overlap with code dimming (LOW)
- **Spec says**: Title fades in from frame 30 to 90 (1-3s), overlapping with code dimming (frames 0-60), so "title arrives as code recedes."
- **Implementation does**: Title fades in from frame 0 to 60 relative to VISUAL_04_START (ColdOpenSection.tsx:140). Since code dimming is absent entirely (Issue 3), there is no overlap choreography.
- **Impact**: The poetic crossfade described in the spec is missing.

#### Issue 9: Title vertical position is true center, not shifted above (LOW)
- **Spec says**: Title positioned at ~45% from top ("optionally shifted ~5% above true center for more visually balanced" composition). The reference code uses `top: '45%'` with `transform: translate(-50%, -50%)`.
- **Implementation does**: Title uses flexbox exact centering with `alignItems: "center"` and `justifyContent: "center"` (ColdOpenSection.tsx:138-139), which places it at 50% vertical. No upward offset.
- **Impact**: Minor visual weight difference. The spec notes this creates balance "with dimmed code below."

#### Issue 10: Title fade-in easing is linear, not easeOutCubic (LOW)
- **Spec says**: Title opacity uses `easeOutCubic` ("confident arrival"). Title Y drift uses `easeOutCubic` ("settles into place").
- **Implementation does**: Both `interpolate` calls (ColdOpenSection.tsx:140, 143) use Remotion's default linear interpolation -- no `easing` parameter is provided.
- **Impact**: The title arrival feels mechanical rather than the spec's "confident" settling motion. A minor kinetic quality difference.

#### Issue 11: Missing lineHeight: 1.2 on title text (LOW)
- **Spec says**: Title typography specifies `line-height: 1.2`.
- **Implementation does**: No `lineHeight` property is set on the `<h1>` element (ColdOpenSection.tsx:142-153). Browser default (typically ~1.2 for headings) likely produces an acceptable result, but it is not explicitly set.
- **Impact**: Negligible for a single-line title. Could matter if the title ever wraps to two lines.

#### Issue 12: Background color slight mismatch (LOW)
- **Spec says**: Background `#1E1E2E`.
- **Implementation does**: AbsoluteFill uses `#1a1a2e` (ColdOpenSection.tsx:120). The red channel differs by 4 units (0x1A vs 0x1E), making the implementation slightly darker.
- **Impact**: Minimal visual difference. The code backdrop panel inside does use `#1E1E2E` (ColdOpenSection.tsx:129), creating a subtle two-tone effect.

#### Issue 13: FPS difference affects frame number interpretation (LOW)
- **Spec says**: Frame numbers (e.g., "Frame 0-60" = 2 seconds, "Frame 30-90") imply 30fps.
- **Implementation does**: S00-ColdOpen runs at 30fps (constants.ts:15), which matches. However, the alternative `01-ColdOpen/` directory runs at 60fps (01-ColdOpen/constants.ts:4). If someone references the spec frame numbers against 01-ColdOpen, they would be off by 2x.
- **Impact**: Low -- only relevant if someone uses the wrong constants file.

### Notes

The title card implementation in `S00-ColdOpen/ColdOpenSection.tsx` VISUAL_04 captures the core visual design faithfully. The typography (Inter, 600 weight, 72px, #F8F4F0, 0.02em tracking), the blue glow effect (#4A90D9 at 0.15 opacity), the dimmed code backdrop, the upward drift animation, and the "Prompt-Driven Development" text are all present and closely aligned with the spec. If you pause the video at the right moment, the title card looks approximately correct.

**The primary gap is timing and pacing.** The spec envisions this as a 10-second contemplative beat -- the "poster frame" of the entire video. The spec describes a choreographed sequence: background code recedes over 2 seconds, the title arrives over 2 seconds, then the composition holds in silence for 6 seconds. This stillness is explicitly described as giving the rhetorical question ("So why are we still patching?") and the answer ("Prompt-Driven Development") room to breathe. The implementation compresses VISUAL_04 into under 2 seconds, barely enough for the title to finish fading in before the cold open section ends.

**The secondary gap is transition quality.** The spec describes overlapping animations where code dims, editor chrome fades, the terminal disappears, a vignette frames the composition, and the glow blooms -- all happening on staggered timelines. The implementation uses a hard cut between visual states (the `activeVisual` switching logic), so VISUAL_03 elements vanish instantly when VISUAL_04 begins. Within VISUAL_04 itself, the code backdrop is statically dimmed rather than animated.

**The tertiary gap is easing.** The spec defines specific easing for each element (easeInOutCubic for code dim, easeOutCubic for title, linear for vignette). The implementation uses Remotion's default linear interpolation throughout, losing the kinetic personality the spec describes.

## Resolution Status: RESOLVED

### Resolution Summary

All 13 issues have been fixed by extracting VISUAL_04 into a dedicated `TitleCardVisual` component within `ColdOpenSection.tsx` and updating the timing constants.

**Files modified:**
- `S00-ColdOpen/constants.ts` — VISUAL_04 now spans 10 seconds (s2f(43.78) to s2f(53.78), 300 frames at 30fps). Section duration extended to 54 seconds to accommodate.
- `S00-ColdOpen/ColdOpenSection.tsx` — VISUAL_04 block replaced with `TitleCardVisual` sub-component. `Easing` import added from Remotion.

**Issue-by-issue resolution:**

1. **Duration (HIGH)**: VISUAL_04_END extended from s2f(15.96) to s2f(53.78), giving the title card a full 10 seconds (300 frames). COLD_OPEN_DURATION_SECONDS updated accordingly.

2. **Hold period (HIGH)**: All animations complete by frame 90. Frames 90-270 (3-9s) are now pure stillness — all `interpolate` calls use `extrapolateRight: "clamp"`, so values hold at their final state. Frames 270-300 are transition prep with title at full opacity.

3. **Code dimming (MEDIUM)**: Code backdrop opacity now animates from 1.0 to 0.15 over frames 0-60 using `Easing.inOut(Easing.cubic)`, replacing the static `opacity: 0.25`.

4. **Vignette overlay (MEDIUM)**: Added a radial-gradient vignette div (`radial-gradient(ellipse at center, transparent 40%, rgba(0, 0, 0, 0.85) 100%)`) that fades from opacity 0 to 0.6 over frames 0-60 (linear easing per spec).

5. **Editor chrome & terminal fade-out (MEDIUM)**: Added editor top bar (with traffic-light dots and filename) and line number gutter, both fading out over frames 0-45 with `Easing.out(Easing.cubic)`. Added terminal snippet (with `$ pdd generate`, progress, and done messages) fading out over frames 0-30.

6. **Glow implementation (LOW)**: Replaced text-shadow glow with a separate `<div>` using `radial-gradient(ellipse at center, rgba(74, 144, 217, glowOpacity), transparent 70%)`, `filter: blur(20px)`, and `inset: -40`. Bloom radius now matches spec's ~40px. Removed the dark drop shadow (`0 0 40px rgba(0,0,0,0.8)`).

7. **Separate glow animation (LOW)**: Glow opacity now animates independently from 0 to 0.15 over frames 45-90 with `Easing.out(Easing.cubic)`, starting after the title fade begins at frame 30.

8. **Title fade-in timing overlap (LOW)**: Title now fades in from frame 30 to 90, overlapping with code dimming (frames 0-60). The crossfade where "title arrives as code recedes" is now properly choreographed.

9. **Title vertical position (LOW)**: Changed from flexbox centering (50%) to absolute positioning with `top: "45%"` and `transform: translate(-50%, -50%)`, placing the title ~5% above true center per spec.

10. **Easing (LOW)**: All interpolations now use spec-correct easing: `Easing.inOut(Easing.cubic)` for code dim, `Easing.out(Easing.cubic)` for title opacity/drift/glow/chrome/terminal, linear (default) for vignette.

11. **lineHeight (LOW)**: Added `lineHeight: 1.2` to the `<h1>` style.

12. **Background color (LOW)**: TitleCardVisual's AbsoluteFill now uses `#1E1E2E` (matching spec exactly). Note: the parent ColdOpenSection still uses `#1a1a2e` for other visuals — this is unrelated to the title card.

13. **FPS (LOW)**: S00-ColdOpen runs at 30fps (constants.ts:15), matching the spec's frame number convention. The alternative 01-ColdOpen directory is a separate composition and does not affect this implementation.
