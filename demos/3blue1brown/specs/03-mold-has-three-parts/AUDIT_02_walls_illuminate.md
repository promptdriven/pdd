# Audit: Walls Illuminate (Section 3.2)

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas and Resolution**: 1920x1080 at 30fps with dark background `#1a1a2e` (constants.ts lines 8-9, line 24). Matches spec exactly.

2. **Duration**: 15 seconds / 450 frames (constants.ts lines 5-7). Matches spec.

3. **Four Wall Segments**: All four walls (Top, Right, Bottom, Left) are rendered as distinct SVG rects with amber glow (WallsIlluminate.tsx lines 68-122). Each has clean sharp edges with `strokeWidth: 2` and rounded corners (`rx={8}`).

4. **Test Label Content**: All four spec-required labels are correctly defined (constants.ts lines 33-37):
   - Top: `"null -> None"` at frame 60
   - Right: `"empty string -> ''"` at frame 120
   - Bottom: `"handles unicode"` at frame 180
   - Left: `"latency < 100ms"` at frame 240

5. **Sequential Label Timing**: Labels appear at frames 60, 120, 180, 240 matching the spec's animation sequence (constants.ts lines 34-37). Each fades in over 30 frames.

6. **Label Typography**: Monospace font `"JetBrains Mono, monospace"` at 24px, color `#FFF8F0` with subtle drop shadow (WallsIlluminate.tsx lines 148-152). Matches spec typography section.

7. **Label Fade-In Easing**: Uses `Easing.out(Easing.cubic)` (line 134), matching spec's `easeOutCubic` requirement.

8. **Individual Wall Pulse**: Each wall pulses brighter when its corresponding label appears, using `Easing.inOut(Easing.sine)` (lines 36-51). Pulse is applied to both SVG fill opacity and drop-shadow radius on each wall rect. Matches spec's `easeInOutSine` requirement.

9. **Glow Effect**: Walls use `#D9944A` amber color with animated drop-shadow glow that intensifies during pulses (lines 74, 78, 88, 92, 102, 106, 116, 120). Core amber color matches spec.

10. **One Label Per Wall**: Labels are positioned outside their respective wall segments -- top/bottom centered horizontally, left/right centered vertically (lines 155-183). Matches spec's layout pattern.

11. **Label Dynamic Pulse Shadow**: Label text shadow includes a pulse component synchronized with the wall pulse (line 152: `0 0 ${10 + 10 * wallPulse}px`), providing visual feedback linking label appearance to wall activation.

12. **Integration into Section Composition**: WallsIlluminate is used as Visual 1 in Part3MoldThreeParts.tsx (lines 55-59), correctly sequenced after CrossSectionIntro.

### Issues Found

1. **Missing Connecting Lines from Labels to Wall Segments**
   - **Spec says**: "Connected to wall segments with subtle lines" (spec line 28) with line draw using `easeOutQuad` easing (spec line 133).
   - **Implementation**: No connecting lines are rendered between labels and their respective wall segments. The labels float near the walls without visual connectors.
   - **Severity**: Low -- The label proximity to walls makes the association clear, but the spec explicitly calls for subtle connecting lines with animated draw-in.

2. **Glow Opacity Exceeds Spec**
   - **Spec says**: Soft outer glow at 40% opacity (`#D9944A at 40% opacity`).
   - **Implementation**: Wall fill uses `rgba(217, 148, 74, ${0.2 + 0.5 * wallsGlow + pulse})`. At full glow (`wallsGlow = 1`) without pulse, fill opacity reaches 0.7 (70%). During a pulse, it can go even higher.
   - **Severity**: Low -- The visual effect is appropriate; the opacity is just higher than the specified 40%.

3. **No Per-Label Audio Clicks**
   - **Spec says**: "Soft 'click' as each label appears" and "Ambient hum from glowing walls" (spec lines 143-145).
   - **Implementation**: No audio is handled within the WallsIlluminate component. The parent Part3MoldThreeParts uses a shared narration track (`part3_mold_narration.wav`) but individual click sound effects for label appearance are absent.
   - **Severity**: Low -- Audio details are often handled at a higher composition level or in post-production.

4. **Mold Fades In Instead of Being Pre-Visible**
   - **Spec says**: Frame 0-60 shows "Mold visible from previous section" (spec lines 45-47), implying it should already be visible.
   - **Implementation**: Mold fades in from opacity 0 to 1 over frames 0-30 (lines 11-15). As a standalone component this is reasonable, but the spec envisions continuity from Section 3.1.
   - **Severity**: Low -- The parent section composition handles transitions between visuals, so this may be appropriate in context.

### Notes

- The previous audit identified high-severity issues (missing top wall, wrong label content, wrong label count). All of those have been fully resolved in the current implementation. The four walls, four labels, per-wall pulse animations, and correct typography are all now spec-compliant.
- The remaining issues are all low severity. The most notable gap is the missing connecting lines, which the spec explicitly describes but which are not implemented. The label-to-wall association is still visually clear due to proximity and positioning.
- The component adds a section title ("First: tests" / "The Constraints") and a bottom caption ("Tests define the boundaries. Code must fit within them.") that are not in the spec. These are acceptable additions that provide narration context without contradicting the spec.
- The `showLabels` prop allows the component to be reused without labels (e.g., by other compositions that reference the mold shape), which is a good design choice.
