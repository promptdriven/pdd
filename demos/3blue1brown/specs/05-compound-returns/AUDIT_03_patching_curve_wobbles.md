# Audit: Patching Curve Wobbles (Section 5.3)

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas and background** -- Resolution 1920x1080 with dark #1a1a2e background. SVG viewBox matches spec, COLORS.BACKGROUND is "#1a1a2e" (`constants.ts` line 13).

2. **Wobble morph timing** -- Spec: frame 0-270 (0-9s). Implementation: `interpolate(frame, [0, 270], [0, 1])` (`CompoundCurvesGraph.tsx` line 572). Exact match.

3. **Wobble easing** -- Spec: `easeInOutQuad`. Implementation: `Easing.inOut(Easing.quad)` (line 575). Exact match.

4. **Dip positions** -- Spec: ~55%, ~70%, ~85% along X-axis. Implementation: `DIP_POSITIONS = [0.55, 0.70, 0.85]` (`constants.ts` line 58). Exact match.

5. **Dip count** -- Spec: 3-4 distinct dips. Implementation: 3 dips (DIP_POSITIONS has 3 entries). Within spec range.

6. **Dip depth** -- Spec: 10-20% of curve height at that point. Implementation: `DIP_MAGNITUDES = [60, 45, 50]` (`constants.ts` line 64). At dip positions the logarithmic base curve reaches roughly 400-500px, making the dips approximately 10-15% of curve height. Within spec range.

7. **Dip math (Gaussian)** -- Spec code reference uses Gaussian exponential dips. Implementation: `Math.exp(-Math.pow((t - pos) / DIP_SPREAD, 2))` with `DIP_SPREAD = 0.04` (lines 29-33, constants line 65). Matches spec's reference code.

8. **Dip labels** -- Spec: "new bug from patch", "regression", "merge conflict". Implementation: `DIP_LABELS = ["new bug from patch", "regression", "merge conflict"]` (`constants.ts` lines 59-63). Exact match.

9. **Dip annotation color** -- Spec: #E06040 red-tinted amber. Implementation: `COLORS.DIP_RED = "#E06040"` (`constants.ts` line 17), used at line 840. Exact match.

10. **Dip annotation timing** -- Spec: frame 60-90, 150-180, 240-270. Implementation: `[60, 90]`, `[150, 180]`, `[240, 270]` (lines 593-607). Exact match.

11. **Dip annotation icons** -- Spec: downward arrow for "new bug", circular revert for "regression", forking-paths for "merge conflict". Implementation: DipIcon component (lines 296-335) with types "arrow-down", "revert", "fork"; invoked at line 842 via `icon={["arrow-down", "revert", "fork"][i]}`. All three icon types implemented.

12. **Annotation italic style** -- Spec: annotations should be italic. Implementation: `fontStyle="italic"` on annotation text (line 382). Match.

13. **Leader lines** -- Spec: thin red-tinted leader lines connecting annotations to dip troughs. Implementation: leader line in Annotation component (lines 359-367) using the color prop set to COLORS.DIP_RED. Match.

14. **Flicker/shake effect** -- Spec: 1-2px lateral shake, 5-8 frames per dip. Implementation (lines 579-588): `Math.sin(frame * 3) * 1.5` yields +/-1.5px oscillation, duration 7 frames per dip. Applied as `transform={translate(...)}` on the patching curve group (line 776). Match.

15. **Flicker easing** -- Spec: linear sinusoidal (raw, unstable feel). Implementation: `Math.sin(frame * 3)` -- sinusoidal oscillation with no easing wrapper. Match.

16. **Cost callout "$1.52T"** -- Spec: 36pt bold red-amber #E06040. Implementation (lines 468-478): fontSize={36}, fontWeight="bold", fill={COLORS.DIP_RED}. Match.

17. **Cost callout position** -- Spec: upper-right area. Implementation: rect at x=1350, y=120, width=360 (lines 458-462). This places it in the upper-right quadrant. Match.

18. **Cost callout background card** -- Spec: subtle background card with dark border. Implementation (lines 458-466): rect with `fill="rgba(26, 26, 46, 0.85)"`, `stroke="rgba(255,255,255,0.15)"`. Match.

19. **Cost callout timing** -- Spec: frame 270-360 fade in. Implementation: `interpolate(frame, [270, 360], [0, 1])` (lines 611-612). Exact match.

20. **Cost callout easing** -- Spec: `easeOutCubic`. Implementation: `Easing.out(Easing.cubic)` (line 615). Exact match.

21. **PDD curve dormant** -- Spec: PDD starting segment visible with faint blue glow. In phase 3, effectivePddTo falls back to curveStartProgress (~0.08), and the PDD CurveLine renders with glowId="pddGlow" and glowStd (lines 865-873). Match.

22. **Dip recovery slope decreasing** -- Spec: recovery slope after each dip is shallower. The base logarithmic curve naturally has decreasing slope at later positions, so dips further along the curve inherently recover more slowly. Implicit match.

23. **Annotation easing** -- Spec: `easeOutCubic` for dip annotations. Implementation: `Easing.out(Easing.cubic)` (lines 596, 601, 606). Match. (Note: previous audit incorrectly flagged spec as requesting `easeOutQuad`; spec line 209 says `easeOutQuad` for "annotation fade" but dip appearance says `easeOutCubic` with slight bounce on line 208. Implementation uses cubic for dip annotations, which aligns with the dip appearance spec.)

### Issues Found

1. **Dip annotation fontSize slightly small** -- Spec says 16pt for annotations (line 36). Implementation passes `fontSize={15}` at the call site (line 841), overriding the Annotation component's default of 16.
   - Severity: Low
   - Location: `CompoundCurvesGraph.tsx` line 841
   - Spec reference: line 36 ("All annotations are small (16pt)")

2. **Cost callout subtitle fontSize** -- Spec says 18pt for the subtitle "annual US tech debt cost (CISQ)" (line 47). Implementation uses fontSize={16} (line 485).
   - Severity: Low
   - Location: `CompoundCurvesGraph.tsx` line 485
   - Spec reference: line 47 ("18pt, white at 70% opacity")

3. **Hold period truncated** -- Spec calls for frame 360-450 (12-15s) as a hold period with all elements visible. The Section 5 sequence allocates VISUAL_02 from frame 733 to frame 1120 globally (387 local frames). Since the cost callout finishes fading at frame 360, only ~27 local frames (0.9s) remain for the hold, versus the spec's 90 frames (3s).
   - Severity: Medium
   - Location: `S05-CompoundReturns/constants.ts` lines 52-53 (VISUAL_02_START/END)
   - Spec reference: lines 98-101 ("Frame 360-450 (12-15s): Hold on damaged curve")

4. **Flicker applied globally not per-dip segment** -- Spec says "at each dip, the curve segment briefly flickers." The implementation sums all flickerOffsets and applies a single `translate()` on the entire patching curve group (line 776: `flickerOffsets.reduce((a, b) => a + b, 0) / 3`). This means the entire curve shifts rather than just the segment near each dip point.
   - Severity: Low
   - Location: `CompoundCurvesGraph.tsx` line 776
   - Spec reference: lines 39-41 ("At each dip, the curve segment briefly flickers")

### Notes

- The phase system cleanly isolates phase 3 behavior. Phase 3 inherits the full patching curve from phase 2 and overlays wobble, dip annotations, flicker, and cost callout.
- All previously reported high-severity issues from the prior audit have been resolved: wobble timing now matches 0-270 frames, annotation timing matches spec exactly, flicker effect is implemented, and dip icons are present.
- The annotation easing discrepancy flagged in the prior audit (cubic vs quad) appears to be a misread of the spec; the spec lists multiple easing types for different elements, and `easeOutCubic` for dip appearance is consistent with the implementation's use of `Easing.out(Easing.cubic)` for dip annotations.
- The remaining issues are all low-to-medium severity: two font size mismatches of 1-2pt each, a truncated hold period, and a global-vs-local flicker application.
