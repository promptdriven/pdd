# Audit: 04_pdd_curve (PDD Curve -- Compounding Investment)

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas and background**: Resolution 1920x1080 with dark background `#1a1a2e` matches spec exactly. Constants in `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/46-CompoundCurvesGraph/constants.ts` lines 8-9 and line 13.

2. **PDD curve color and stroke**: Blue `#4A90D9` with stroke width 3px matches spec (line 22). Implementation at `CompoundCurvesGraph.tsx` lines 869-870 uses `COLORS.PDD_BLUE` and `strokeWidth={phase >= 5 ? 4 : 3}` -- correct for phase 4.

3. **Curve mathematical function**: Spec calls for exponential `y = a * (e^(bx) - 1)`, convex upward. Implementation at lines 38-41: `maxHeight * ((Math.exp(t * 2.5) - 1) / (Math.exp(2.5) - 1))` with `maxHeight = GRAPH.HEIGHT * 0.88` (~700px). Correct exponential form with proper normalization.

4. **Curve draw range**: Spec says frame 30-240 extending from ~8% to ~50% of X-axis. Implementation at lines 627-634: `interpolate(frame, [30, 240], [0.08, 0.5])`. Exact match.

5. **Curve draw easing**: Spec says `easeInQuad` (accelerating, mirrors exponential growth). Implementation at line 632: `Easing.in(Easing.quad)`. Exact match.

6. **Test dot count**: Spec says 6-8 dots visible by end. Implementation at lines 635-643: `interpolate(frame, [30, 240], [0, 8])`. 8 dots at end, within spec range.

7. **Test dot appearance**: Spec says small circles (8px radius), blue `#4A90D9` with white border. Implementation: `PDD_DOT_RADIUS = 8` (constants.ts line 55), `CurveDots` component at lines 286-289 renders `<circle r={radius} fill={color} stroke="#ffffff" strokeWidth={2} />`. Matches spec.

8. **Test dot spring animation**: Spec says `spring({ damping: 12, stiffness: 200 })`. Implementation at lines 278-285 uses exactly `damping: 12, stiffness: 200`. Exact match.

9. **Forward radial lines -- count and direction**: Spec says 2-3 faint lines project forward from each dot to right edge. Implementation: `ForwardRadials` at lines 390-415 renders 3 lines (offsets `[0, -15, 15]`) extending to `GRAPH.RIGHT`. Correct.

10. **Forward radial lines -- color and opacity**: Spec says light blue `#6AB0E9` at 30% opacity. Implementation uses `COLORS.PDD_GLOW` (which is `#6AB0E9`, constants.ts line 17) at `opacity * 0.3` (line 410). Matches spec.

11. **Forward radial line accumulation**: Spec says each new dot's radials overlay with previous, creating accumulating density. Implementation at lines 878-890 loops through all visible dots rendering `ForwardRadials` for each. Correct layering behavior.

12. **Blue glow on PDD curve**: Spec says subtle blue glow (feGaussianBlur, 4px). Implementation uses `glowId="pddGlow"` and `glowStd={glowStd}` (line 872-873) where `glowStd` defaults to 4 when phase < 5 (line 715). The glow filter at lines 224-234 applies `feGaussianBlur` with the given `stdDeviation`. Matches spec.

13. **Patching curve dimming**: Spec says patching curve remains at 60% opacity. Implementation at lines 652-658: `interpolate(frame, [0, 30], [1, 0.6])`. Applied to the patching group at line 776. Matches spec.

14. **Activation timing**: Spec says frame 0-30 the dormant segment brightens. Implementation at lines 620-626: `interpolate(frame, [0, 30], [0.5, 1])`. Correct frame range.

15. **Annotation text**: Spec says "constrains all future generations". Implementation at line 907: exact text match.

16. **Annotation position**: Spec says near dot #3. Implementation at lines 908-909 positions at `3 / (PDD_DOT_COUNT + 1)`. Correct (3rd dot).

17. **Annotation styling**: Spec says white at 80% opacity, italic, 18pt. Implementation at lines 911-912 uses `color="rgba(255,255,255,0.8)"` and `fontSize={17}`. The `Annotation` component at line 382 applies `fontStyle="italic"`. Close match (17pt vs 18pt is minor).

18. **Annotation timing**: Spec says frame 120-180. Implementation at lines 644-651: `interpolate(frame, [120, 180], [0, 1])` with `easeOutCubic`. Exact frame match.

19. **Annotation easing**: Spec says `easeOutCubic`. Implementation at line 649: `Easing.out(Easing.cubic)`. Exact match.

20. **Convex shape**: The exponential function naturally produces a convex (slope-increasing) curve, contrasting with the patching curve's logarithmic (concave) shape. Visually correct.

### Issues Found

1. **Phase 4 is never rendered standalone in orchestration -- annotation never appears**
   - **Spec says**: The PDD curve section (5.4) is a distinct ~10-second segment with its own animation sequence including the "constrains all future generations" annotation (lines 41-44, 85-88).
   - **Implementation does**: In `Part5CompoundReturns.tsx` line 95, Visual 3 renders `<CompoundCurvesGraph phase={5} />`, jumping directly from phase 3 to phase 5. Phase 4 is never used as a standalone phase. The annotation rendering at line 905 checks `phase === 4` (strict equality), so it is **never visible** when phase 5 is active.
   - **Impact**: The annotation "constrains all future generations" with its leader line -- a key visual element that explains the forward radial lines metaphor -- is completely absent from the rendered video.
   - **Severity**: HIGH. The annotation is called out in the spec as a critical visual element for narration sync ("constrains all future generations" near dot #3) and is part of an entire animation phase (frames 120-180).

2. **Activation pulse is simplified -- no traveling light pulse**
   - **Spec says**: Frame 0-30: "A pulse of light runs along the existing segment" and "The glow intensifies" (lines 75-76).
   - **Implementation does**: Simple opacity interpolation from 0.5 to 1.0 (lines 620-626). No traveling pulse animation.
   - **Severity**: Medium. The activation is a fade-in rather than a dramatic "pulse running along" the segment. The spec envisions a more cinematic activation moment.

3. **No radial line brightness pulse for annotated dot**
   - **Spec says**: "The forward radial lines from this dot pulse brighter briefly" when the annotation appears at frame 120-180 (line 86).
   - **Implementation does**: All radial lines are treated identically. No special pulsing for the dot associated with the annotation.
   - **Severity**: Low. Subtle visual emphasis is missing but does not block comprehension.

4. **Separate phase 4 timing not reflected in orchestration**
   - **Spec says**: Section 5.4 is ~10 seconds (frames 0-300 at 30fps) as a standalone animation segment.
   - **Implementation does**: Phase 4 logic exists in `CompoundCurvesGraph.tsx` (lines 619-658) but the orchestrator at `Part5CompoundReturns.tsx` skips from phase 3 (Visual 2) directly to phase 5 (Visual 3, starting at frame 1171 / 39.04s). The phase 4 animation timing has no dedicated window.
   - **Severity**: Medium. Phase 4 and 5 are merged, which compresses the PDD curve introduction. The narration sync at 39.04s ("When you add a test in PDD, the returns are different") is correctly timed, but the full phase 4 animation sequence (activation, curve draw, dots, annotation, hold) is collapsed into phase 5's animation.

5. **Annotation font size is 17pt instead of 18pt**
   - **Spec says**: 18pt (line 44).
   - **Implementation does**: `fontSize={17}` (line 912).
   - **Severity**: Very low. 1px difference.

### Notes

- The core Phase 4 animation logic in `CompoundCurvesGraph.tsx` is well-implemented and closely follows the spec: curve math, draw timing, easing, dot physics, radial lines, colors, and glow all match. The main problem is at the orchestration layer where phase 4 is skipped in favor of jumping to phase 5.
- The `phase === 4` check for annotation rendering (line 905) is the critical bug. If the orchestrator used phase 4, or if this check were changed to `phase >= 4`, the annotation would appear. However, in phase 5 the PDD curve extends beyond 50% (to 100%), so displaying the phase 4 annotation throughout phase 5 may not be the right fix either -- a timed fade-out would be more appropriate.
- The forward radial lines implementation is clean and matches the spec's "accumulating density" metaphor well.
- The patching curve correctly remains visible at 60% opacity for simultaneous comparison as the spec requires.
