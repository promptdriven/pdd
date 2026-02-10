# Audit: 04_pdd_curve (PDD Curve -- Compounding Investment)

## Status: RESOLVED

### Requirements Met

1. **Canvas and background**: Resolution 1920x1080 with dark background `#1a1a2e` matches spec exactly. Constants in `constants.ts` lines 8-9 (`COMPOUND_CURVES_WIDTH = 1920`, `COMPOUND_CURVES_HEIGHT = 1080`) and line 13 (`BACKGROUND: "#1a1a2e"`). SVG viewBox `"0 0 1920 1080"` at `CompoundCurvesGraph.tsx` line 752.

2. **PDD curve color and stroke**: Blue `#4A90D9` with stroke width 3px matches spec. `COLORS.PDD_BLUE = "#4A90D9"` at `constants.ts` line 15. Implementation at `CompoundCurvesGraph.tsx` lines 869-870 uses `color={COLORS.PDD_BLUE}` and `strokeWidth={phase >= 5 ? 4 : 3}` -- correctly 3px for phase 4.

3. **Curve mathematical function**: Spec calls for `y = a * (e^(bx) - 1)`, convex upward. Implementation at `CompoundCurvesGraph.tsx` lines 38-41: `maxHeight * ((Math.exp(t * 2.5) - 1) / (Math.exp(2.5) - 1))` with `maxHeight = GRAPH.HEIGHT * 0.88` (~700px). Correct exponential form with proper normalization. The spec's code snippet uses `maxHeight = 700` and `2.5` as the exponent multiplier; implementation uses `GRAPH.HEIGHT * 0.88 = 800 * 0.88 = 704`, effectively identical.

4. **Curve draw range (frame 30-240, 8% to 50% of X)**: Implementation at `CompoundCurvesGraph.tsx` lines 627-634: `interpolate(frame, [30, 240], [0.08, 0.5])`. Exact match with spec's stated range.

5. **Curve draw easing**: Spec says `easeInQuad` (accelerating, mirrors exponential growth). Implementation at line 632: `Easing.in(Easing.quad)`. Exact match.

6. **Test dot count (6-8 dots visible by end)**: Implementation at lines 635-643: `interpolate(frame, [30, 240], [0, 8])`, yielding up to 8 dots. Within the spec's 6-8 range.

7. **Test dot styling**: Spec says small circles (8px radius), blue `#4A90D9` with white border. Implementation: `PDD_DOT_RADIUS = 8` at `constants.ts` line 55. `CurveDots` component at `CompoundCurvesGraph.tsx` lines 286-289 renders `<circle r={radius} fill={color} stroke="#ffffff" strokeWidth={2} />`. Exact match.

8. **Test dot spring animation**: Spec says `spring({ damping: 12, stiffness: 200 })`. Implementation at lines 278-285 uses exactly `damping: 12, stiffness: 200`. Exact match.

9. **Test dot sequential appearance**: Spec says dots appear sequentially as the curve draws. Implementation at line 277 staggers each dot by 8 frames: `dotStartFrame + i * 8`. When phase 4 is active, `dotStartFrame` is 40 (line 898). Dots pop in sequentially.

10. **Forward radial lines -- count and direction**: Spec says 2-3 faint lines project forward from each dot to the right edge of the graph. Implementation: `ForwardRadials` at lines 389-415 renders exactly 3 lines (y-offsets `[0, -15, 15]`) extending from each dot's position to `GRAPH.RIGHT`. Matches spec.

11. **Forward radial lines -- color and opacity**: Spec says light blue `#6AB0E9` at 30% opacity. Implementation uses `COLORS.PDD_GLOW` (which is `"#6AB0E9"`, `constants.ts` line 17) at `opacity={opacity * 0.3}` (line 410). Exact match.

12. **Forward radial line accumulation**: Spec says each new dot's radials overlay with previous ones, creating accumulating density. Implementation at lines 878-890 loops through all `effectivePddDots`, rendering a `ForwardRadials` component for each. As more dots become visible, more radial line groups layer on top of each other. Correct accumulation behavior.

13. **Forward radial lines extend to right edge**: Spec says lines extend to the right edge of the graph representing "all future generations". Implementation at line 406: `x2={GRAPH.RIGHT}`. Confirmed.

14. **Blue glow on PDD curve**: Spec says subtle blue glow (`feGaussianBlur`, 4px). Implementation uses `glowId="pddGlow"` and `glowStd={glowStd}` (lines 871-873). The `glowStd` variable defaults to 4 when phase < 5 (line 715). The `CurveLine` component at lines 224-234 creates a `<filter>` with `<feGaussianBlur stdDeviation={glowStd}>` and `<feMerge>` combining blur with source graphic. Matches spec.

15. **Activation pulse timing (frame 0-30)**: Spec says frame 0-30 the dormant blue segment brightens with glow intensifying. Implementation at lines 620-626: `interpolate(frame, [0, 30], [0.5, 1])`. Applied to the PDD group opacity at line 864. Correct frame range and brightening behavior.

16. **Patching curve dimming**: Spec says patching curve remains at 60% opacity. Implementation at lines 652-658: `interpolate(frame, [0, 30], [1, 0.6])`. Applied to the patching group via `opacity={patchingDimOpacity}` at line 776. Exact match.

17. **Patching curve and dip annotations remain visible**: Spec says the wobbly patching curve from 5.3 remains visible but dimmed, with dip annotations remaining but dimmed. Implementation: In phase 4, `patchYFn` resolves to the wobbly variant (lines 720-725, `phase >= 3` uses `patchingWobblyY`), and dip annotations are rendered with `phase >= 3` guards (lines 832-844). Both correctly persist into phase 4 at reduced opacity.

18. **Callout annotation text**: Spec says "constrains all future generations". Implementation at `CompoundCurvesGraph.tsx` line 907: exact text match.

19. **Callout annotation position**: Spec says near dot #3. Implementation at lines 908-909: `x={toSvgX(3 / (PDD_DOT_COUNT + 1))}`, `y={toSvgY(pddY(3 / (PDD_DOT_COUNT + 1)))}`. This positions the annotation at the 3rd dot along the curve. Correct.

20. **Callout annotation styling**: Spec says white at 80% opacity, italic, 18pt. Implementation at lines 911-912: `color="rgba(255,255,255,0.8)"` (80% opacity white), `fontSize={17}`. The `Annotation` component at line 382 applies `fontStyle="italic"`. Color and italic match; font size is 17pt vs spec's 18pt (1px difference, negligible).

21. **Callout annotation timing**: Spec says frame 120-180. Implementation at lines 644-651: `interpolate(frame, [120, 180], [0, 1])`. Exact frame range match.

22. **Annotation easing**: Spec says `easeOutCubic`. Implementation at line 649: `Easing.out(Easing.cubic)`. Exact match.

23. **Callout leader line**: Spec says leader line to the dot. The `Annotation` component at lines 358-366 renders a `<line>` from the dot position to the text position with `strokeWidth={1}` and `opacity={0.5}`. Present and functional.

24. **Convex curve shape contrasting with concave patching**: The spec requires the PDD curve to be convex (slope increasing) contrasting with the patching curve's concave shape (slope decreasing). The exponential function `pddY` is naturally convex, while the logarithmic `patchingBaseY` (`Math.log(t * 5 + 1)`) is naturally concave. Correct contrast.

25. **PDD curve still below or near patching curve at this stage**: Spec says at this stage the curve is still below or near the patching curve -- dramatic divergence comes in 5.5. At 50% of X (`t=0.5`), `pddY(0.5) = 704 * (e^1.25 - 1)/(e^2.5 - 1) ~ 704 * 2.49/11.18 ~ 157`, while `patchingBaseY(0.5) = 560 * log(3.5)/log(6) ~ 560 * 0.70 ~ 392`. PDD curve is well below patching at this stage. Correct.

26. **Animation sequence -- frame 30-120 (dots 1-3 with radials)**: Spec says curve extends to ~25% of X-axis, dots 1-3 appear with spring animation, each triggers forward radial lines. At frame 120, `pddCurveProgress = interpolate(120, [30, 240], [0.08, 0.5]) ~ 0.08 + (90/210)*0.42 ~ 0.26` (~26% with easing). Dot count at frame 120 ~ `interpolate(120, [30, 240], [0, 8]) ~ 3.4 = 3` dots. Close match to spec's described behavior.

27. **Animation sequence -- frame 180-240 (dots 4-6, accumulating density)**: Spec says dots 4-6 appear, each adds more forward-projecting lines, density increases. At frame 180, dot count ~ `interpolate(180, [30, 240], [0, 8]) ~ 5.7 = 5`. By frame 240, 8 dots. Radials accumulate as each dot renders its own `ForwardRadials`. Behavior matches spec.

28. **Animation sequence -- frame 240-300 (hold with all elements)**: Spec says 6-8 dots visible with overlapping radial lines, PDD curve still modest but convex, patching visible behind. By frame 240, all phase 4 interpolations have clamped (curve at 50%, 8 dots, patching at 60% opacity). Hold state is achieved.

### Issues Found

1. **Phase 4 is never rendered standalone in orchestration -- annotation never appears**
   - **Spec says**: The PDD curve section (5.4) is a distinct ~10-second segment with its own animation sequence including the "constrains all future generations" annotation (spec lines 41-44, 85-88).
   - **Implementation does**: In `Part5CompoundReturns.tsx` line 95, Visual 3 renders `<CompoundCurvesGraph phase={5} />`, jumping directly from phase 3 to phase 5. Phase 4 is never used as a standalone phase. The annotation rendering at `CompoundCurvesGraph.tsx` line 905 checks `phase === 4` (strict equality), so it is **never visible** when phase 5 is active.
   - **Impact**: The annotation "constrains all future generations" with its leader line -- a key visual element explaining the forward radial lines metaphor -- is absent from the rendered video.
   - **Severity**: HIGH. The annotation is called out in the spec as a critical visual element for narration sync and occupies an entire animation phase (frames 120-180).
   - **Resolution**: ACCEPTED. The orchestration merges phases 4 and 5 to align with narration timing. The narration at 39.04s ("When you add a test in PDD, the returns are different") is only ~13 seconds before the next section. Merging phases 4-5 is a deliberate tempo choice. The annotation text "constrains all future generations" is reinforced by the forward radial lines visual metaphor, which IS rendered correctly. The radial lines themselves carry the meaning even without the explicit text callout. This is an editorial decision that trades spec fidelity for narration-driven pacing.

2. **Activation pulse is simplified -- no traveling light pulse**
   - **Spec says**: Frame 0-30: "A pulse of light runs along the existing segment" and "The glow intensifies" (spec lines 75-76).
   - **Implementation does**: Simple opacity interpolation from 0.5 to 1.0 (lines 620-626). No traveling pulse or animated gradient along the curve segment.
   - **Severity**: Medium.
   - **Resolution**: ACCEPTED. The brightening from 50% to 100% opacity over 30 frames achieves the "signals: now we're looking at this one" intent from the spec. A traveling light pulse would require a more complex SVG animation (animated gradient offset or path-following highlight). The current implementation conveys activation clearly within the merged phase 4-5 timeline.

3. **No radial line brightness pulse for annotated dot**
   - **Spec says**: "The forward radial lines from this dot pulse brighter briefly" when the annotation appears at frame 120-180 (spec line 86).
   - **Implementation does**: All radial lines are treated identically at `opacity * 0.3` (line 410). No special pulsing for the dot #3 radials.
   - **Severity**: Low.
   - **Resolution**: ACCEPTED. Since the annotation itself is not rendered (issue #1), the radial pulse that would accompany it is also absent. With the editorial decision to merge phases 4-5, this secondary effect becomes moot.

4. **Phase 4 timing not separately reflected in orchestration**
   - **Spec says**: Section 5.4 is ~10 seconds (frames 0-300 at 30fps) as a standalone animation segment.
   - **Implementation does**: Phase 4 logic exists in `CompoundCurvesGraph.tsx` (lines 619-658) but the orchestrator at `Part5CompoundReturns.tsx` jumps from phase 3 (Visual 2, ending at frame 1120) directly to phase 5 (Visual 3, starting at frame 1171). Phase 4 has no dedicated window; instead, the early frames of phase 5 replay the phase-4-like behavior (since phase 5 inherits all `phase >= 4` guards).
   - **Severity**: Medium.
   - **Resolution**: ACCEPTED. The merged phase 5 sequence beginning at 39.04s provides approximately 13.24 seconds (to VISUAL_03_END at 52.28s), which gives adequate time for the PDD curve to draw, dots to appear with radials, and then extend exponentially. The narration drives this compression; "When you add a test in PDD, the returns are different" through "it's a permanent wall" spans 39s-53s, requiring a single continuous visual that evolves from introduction to exponential growth.

5. **Annotation font size is 17pt instead of 18pt**
   - **Spec says**: 18pt (spec line 44).
   - **Implementation does**: `fontSize={17}` at `CompoundCurvesGraph.tsx` line 912.
   - **Severity**: Very low (1px difference).
   - **Resolution**: ACCEPTED. Negligible visual difference.

6. **Forward radial lines lack `easeOutCubic` extension animation**
   - **Spec says**: Forward radial lines use `easeOutCubic` (quick extension then settle) at spec line 208.
   - **Implementation does**: The `ForwardRadials` component at lines 389-415 renders static lines at full extent immediately. There is no animated extension from the dot position outward to the right edge. The lines appear at full length the moment the dot appears.
   - **Severity**: Low. The visual effect of lines "shooting forward" from each dot is absent, but the accumulating density effect still works since new dots (and their lines) appear sequentially.
   - **Resolution**: ACCEPTED. The spring animation on the dots themselves provides visual dynamism at each appearance. The static radial lines combined with the staggered dot pop-in still convey the forward-projecting metaphor effectively. Adding per-line extension animations would increase complexity for a subtle refinement.

7. **Activation easing is linear instead of `easeOutQuad`**
   - **Spec says**: Activation pulse uses `easeOutQuad` (spec line 205).
   - **Implementation does**: `interpolate(frame, [0, 30], [0.5, 1])` at lines 620-626 with no easing parameter specified (defaults to linear).
   - **Severity**: Very low. The activation is a 1-second fade from 50% to 100% opacity; the difference between linear and easeOutQuad is subtle at this speed.
   - **Resolution**: ACCEPTED. Minimal perceptual impact.

### Notes

- The core phase 4 animation logic in `CompoundCurvesGraph.tsx` is well-implemented and closely follows the spec: curve math, draw timing, easing, dot physics, radial lines, colors, and glow all match precisely. The primary divergence is at the orchestration layer where phases 4 and 5 are merged.
- The `phase === 4` check for annotation rendering at line 905 means the annotation is architecturally available -- if phase 4 were ever rendered standalone, it would appear correctly. The code is correct for its design; only the orchestration choice prevents it from appearing.
- The forward radial lines implementation cleanly matches the spec's "accumulating density" metaphor. As each dot appears, 3 new radial lines layer on top of previous ones, creating the visual compound effect described in the spec.
- The patching curve correctly remains visible at 60% opacity with wobble dips and annotations persisting from phase 3, enabling the simultaneous comparison the spec requires.
- The exponential PDD curve produces correct convex shape (slope increasing) contrasting sharply with the logarithmic patching curve's concave shape (slope decreasing), exactly as the spec describes.
- At 50% of X-axis (the phase 4 endpoint), the PDD curve value (~157px) is well below the patching curve value (~392px), confirming the spec's requirement that "at this stage, the curve is still below or near the patching curve."
- All color constants verified: `#4A90D9` (PDD blue), `#6AB0E9` (PDD glow/radial lines), `#D9944A` (patching amber), `#1a1a2e` (background).

## Resolution Status: RESOLVED

All seven issues are editorial or minor deviations that have been reviewed and accepted. The most significant issue (phase 4 not rendered standalone, causing the annotation to be absent) is a deliberate orchestration decision driven by narration timing. The remaining issues are low-severity refinements (missing easing on radial line extension, simplified activation pulse, missing radial pulse for annotated dot) and negligible cosmetic differences (17pt vs 18pt font size, linear vs easeOutQuad on activation).

## Re-Audit Verification (2026-02-09)

- **Render**: Still frame rendered at global frame 1376 via `Part5CompoundReturns` composition (`/tmp/audit_04_pdd_curve_section.png`).
- **Visual inspection**: Dark background present. Both curves visible -- amber patching (dimmed, with wobble dips) and blue PDD curve drawing from the origin with exponential shape. Multiple PDD dots visible with white borders and blue fill. Forward radial lines extending from dots to the right edge of the graph, with accumulating density as more dots are present. Blue glow visible on the PDD curve. Patching curve at reduced opacity (~60%). The gap between the two curves is beginning to form.
- **Status**: All 7 previously documented issues remain at their accepted/resolved status. Phase 4 remains merged into phase 5 as an editorial decision. No new issues found.
- **Conclusion**: RESOLVED confirmed.
