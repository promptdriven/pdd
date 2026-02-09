# Audit: Patching Curve Wobbles (Section 5.3)

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas and background** -- Resolution 1920x1080 with dark #1a1a2e background. SVG viewBox is `"0 0 1920 1080"` (`CompoundCurvesGraph.tsx:746-747`), and `COLORS.BACKGROUND` is `"#1a1a2e"` (`constants.ts:13`). Exact match.

2. **Wobble morph progress range** -- Spec: frame 0-270, progress 0 to 1. Implementation: `interpolate(frame, [0, 270], [0, 1])` (`CompoundCurvesGraph.tsx:572`). Exact match.

3. **Wobble easing** -- Spec: `easeInOutQuad` (gradual degradation). Implementation: `Easing.inOut(Easing.quad)` (`CompoundCurvesGraph.tsx:575`). Exact match.

4. **Dip positions** -- Spec: ~55%, ~70%, ~85% along X-axis. Implementation: `DIP_POSITIONS = [0.55, 0.70, 0.85]` (`constants.ts:58`). Exact match.

5. **Dip count** -- Spec: 3-4 distinct dips along the latter half of the curve. Implementation: 3 dips defined in `DIP_POSITIONS`. Within spec range.

6. **Dip depth proportionality** -- Spec: dips are 10-20% of curve height at that point. Implementation: `DIP_MAGNITUDES = [60, 45, 50]` (`constants.ts:64`). At t=0.55 the base logarithmic curve `maxHeight * log(0.55*5+1)/log(6)` yields approximately 415px, making dip 1 about 14.5% of the curve height. At t=0.70 the base is ~450px, dip 2 is ~10%. At t=0.85 the base is ~480px, dip 3 is ~10.4%. All within the 10-20% spec range.

7. **Dip math (Gaussian)** -- Spec code shows `Math.exp(-Math.pow((t - 0.55) / 0.04, 2))`. Implementation: `Math.exp(-Math.pow((t - pos) / DIP_SPREAD, 2))` with `DIP_SPREAD = 0.04` (`CompoundCurvesGraph.tsx:29-33`, `constants.ts:65`). Exact match.

8. **Dip labels** -- Spec: "new bug from patch", "regression", "merge conflict". Implementation: `DIP_LABELS = ["new bug from patch", "regression", "merge conflict"]` (`constants.ts:59-63`). Exact match.

9. **Dip annotation color** -- Spec: red-tinted amber #E06040. Implementation: `COLORS.DIP_RED = "#E06040"` (`constants.ts:17`), passed as `color={COLORS.DIP_RED}` at line 840. Exact match.

10. **Dip annotation timing** -- Spec: annotations fade in at frame 60-90, 150-180, 240-270 respectively. Implementation: `interpolate(frame, [60, 90], [0, 1])`, `[150, 180]`, `[240, 270]` (`CompoundCurvesGraph.tsx:593-607`). Exact match.

11. **Dip annotation easing** -- Spec: `easeOutCubic` for dip appearance (line 208). Implementation: `Easing.out(Easing.cubic)` (`CompoundCurvesGraph.tsx:596, 601, 606`). Match.

12. **Dip annotation icons** -- Spec: small downward arrow icon for dip 1, circular revert icon for dip 2, forking-paths icon for dip 3. Implementation: `DipIcon` component (`CompoundCurvesGraph.tsx:296-335`) renders all three icon types ("arrow-down", "revert", "fork"), invoked at line 842 via `icon={["arrow-down", "revert", "fork"][i]}`. Match.

13. **Annotation italic style** -- Spec: all annotations are small, italic. Implementation: `fontStyle="italic"` on annotation text element (`CompoundCurvesGraph.tsx:382`). Match.

14. **Leader lines** -- Spec: thin red-tinted leader lines connect annotations to dip troughs. Implementation: `Annotation` component renders a leader `<line>` from the dip point to the annotation text (`CompoundCurvesGraph.tsx:359-367`), using the `color` prop set to `COLORS.DIP_RED`. Match.

15. **Flicker/shake duration** -- Spec: 5-8 frames per flicker. Implementation: `flickerEnd = flickerStart + 7`, giving 7 frames per dip flicker (`CompoundCurvesGraph.tsx:583`). Within spec range.

16. **Flicker magnitude** -- Spec: 1-2px lateral shake. Implementation: `Math.sin(frame * 3) * 1.5` yields +/-1.5px oscillation (`CompoundCurvesGraph.tsx:585`). Within spec range.

17. **Flicker easing** -- Spec: linear sinusoidal (raw, unstable feel). Implementation: bare `Math.sin(frame * 3)` with no easing wrapper. Match.

18. **Cost callout value text** -- Spec: "$1.52T" in 36pt, bold, red-amber #E06040. Implementation: `fontSize={36}`, `fontWeight="bold"`, `fill={COLORS.DIP_RED}` (`CompoundCurvesGraph.tsx:468-478`). Exact match.

19. **Cost callout subtitle text** -- Spec: "annual US tech debt cost (CISQ)". Implementation: text content matches exactly (`CompoundCurvesGraph.tsx:487`). Match.

20. **Cost callout position** -- Spec: upper-right. Implementation: `<rect>` at x=1350, y=120 (`CompoundCurvesGraph.tsx:459-460`), placing it firmly in the upper-right quadrant. Match.

21. **Cost callout background card** -- Spec: subtle background card with dark border. Implementation: rect with `fill="rgba(26, 26, 46, 0.85)"`, `stroke="rgba(255,255,255,0.15)"`, `rx={8}` rounded corners (`CompoundCurvesGraph.tsx:458-466`). Match.

22. **Cost callout timing** -- Spec: frame 270-360, after the third dip. Implementation: `interpolate(frame, [270, 360], [0, 1])` (`CompoundCurvesGraph.tsx:611-612`). The third dip annotation finishes fading at frame 270, so cost callout immediately follows. Exact match.

23. **Cost callout easing** -- Spec: `easeOutCubic`. Implementation: `Easing.out(Easing.cubic)` (`CompoundCurvesGraph.tsx:615`). Exact match.

24. **Dip recovery slope decreasing** -- Spec: between dips, the curve resumes climbing but at reduced slope. The base logarithmic curve has inherently decreasing slope at later positions, so dips further along the curve recover more slowly. Additionally the dips are cumulative via `dipTotal` which adds all active dip contributions. Implicit match.

25. **Background continues from 5.2** -- Spec: continues from Section 5.2 (full patching curve visible). The `Part5CompoundReturns` orchestrator renders `CompoundCurvesGraph` with `phase={3}` for VISUAL_02, which inherits patching curve rendering logic via `phase >= 2` checks (`CompoundCurvesGraph.tsx:527-567`). The curve draws progressively within the phase. Partially met (see Issue 5 for detail on initial state).

26. **PDD curve color** -- Spec: PDD in blue #4A90D9. Implementation: `COLORS.PDD_BLUE = "#4A90D9"` (`constants.ts:14`). Match.

27. **Patching curve color** -- Spec: amber. Implementation: `COLORS.PATCHING_AMBER = "#D9944A"` (`constants.ts:14`). Match.

### Issues Found

1. **Dip annotation fontSize slightly small** -- Spec says 16pt for annotations (spec line 36: "All annotations are small (16pt)"). Implementation passes `fontSize={15}` at the call site (`CompoundCurvesGraph.tsx:841`), overriding the Annotation component's default of 16.
   - Severity: Low
   - Location: `CompoundCurvesGraph.tsx:841`
   - Spec reference: spec line 36

2. **Cost callout subtitle fontSize undersized** -- Spec says 18pt for subtitle "annual US tech debt cost (CISQ)" (spec line 47). Implementation uses `fontSize={16}` (`CompoundCurvesGraph.tsx:485`).
   - Severity: Low
   - Location: `CompoundCurvesGraph.tsx:485`
   - Spec reference: spec line 47 ("18pt, white at 70% opacity")

3. **Hold period truncated** -- Spec calls for frame 360-450 (12-15s) as a dedicated hold period with all elements visible. The Section 5 orchestrator allocates VISUAL_02 from global frame 733 to 1120, yielding 387 local frames. Since the cost callout finishes fading at local frame 360, only 27 local frames (~0.9s) remain for the hold, versus the spec's 90 frames (3s).
   - Severity: Medium
   - Location: `S05-CompoundReturns/constants.ts:52-53` (VISUAL_02_START/END)
   - Spec reference: spec lines 98-101 ("Frame 360-450 (12-15s): Hold on damaged curve")

4. **Flicker applied globally, not per-dip segment** -- Spec says "at each dip, the curve segment briefly flickers or shakes laterally." The implementation sums all flicker offsets and applies a single `translate()` on the entire patching curve group (`CompoundCurvesGraph.tsx:776`: `flickerOffsets.reduce((a, b) => a + b, 0) / 3`). This means the entire curve and its dots shift laterally during a flicker, rather than just the curve segment near each dip point.
   - Severity: Low
   - Location: `CompoundCurvesGraph.tsx:776`
   - Spec reference: spec lines 39-41

5. **PDD curve not visible at start of phase 3** -- Spec says "PDD starting segment remains visible, unchanged" and "Faint blue glow continues" (spec lines 50-52). In the implementation, when phase=3, `effectivePddTo` falls through to `curveStartProgress` (`CompoundCurvesGraph.tsx:728-733`), which is computed as `interpolate(frame, [120, 210], [0, 0.08])` (line 518-523). At the start of phase 3 (local frame 0), `curveStartProgress = 0`, and the PDD curve is not rendered because the guard `effectivePddTo > 0` (line 863) fails. The PDD curve only begins to appear at local frame 120 and reaches full 0.08 extent at frame 210. The spec expects it to be visible from the very first frame of this section.
   - Severity: Medium
   - Location: `CompoundCurvesGraph.tsx:518-523, 728-733, 863`
   - Spec reference: spec lines 50-52 ("PDD starting segment remains visible, unchanged")

6. **Patching curve re-draws from partial extent at phase 3 start** -- Spec says "Continues from Section 5.2 (full patching curve visible with dots)". In the implementation, when phase=3, `patchCurveProgress` recalculates from `interpolate(frame, [0, 450], [0.08, 1])` (`CompoundCurvesGraph.tsx:527-534`). At local frame 0 of phase 3, the patching curve starts at only 8% progress. The spec expects the complete patching curve (drawn during 5.2) to already be fully visible, with only the wobble effect morphing onto it. Within the allocated 387 frames, the curve reaches ~0.87 progress and never actually draws to full extent.
   - Severity: Medium
   - Location: `CompoundCurvesGraph.tsx:527-534`
   - Spec reference: spec lines 16, 75-76 ("Continues from Section 5.2", "The smooth logarithmic curve from 5.2 progressively deforms")

7. **Patching curve dots re-animate from scratch in phase 3** -- Related to Issue 6: because `patchVisibleDots` is recomputed from the new local frame counter (`CompoundCurvesGraph.tsx:536-543`), the dots also pop in anew during phase 3. The spec implies they should already be present from Section 5.2.
   - Severity: Low
   - Location: `CompoundCurvesGraph.tsx:536-543`
   - Spec reference: spec line 16 ("Continues from Section 5.2 (full patching curve visible with dots)")

8. **Spec's animation sequence phase 1 (frame 0-90) expects first dip at the same time as wobble start** -- The spec says "First dip appears at ~55% mark" during frames 0-90, but the code's `dip1Active` logic is controlled by `wobbleAmount` (which is 0 at frame 0 and increases). Because `dip1Active` is not a separate boolean in phase 3 (unlike the spec's pseudo-code which uses `frame >= 30`), the dip depth scales with `wobbleAmount`. At frame 30 (when spec pseudo-code says dip1 activates), wobbleAmount is only ~0.11, making the dip barely visible. This is arguably a reasonable artistic choice but diverges from the spec pseudo-code behavior.
   - Severity: Low
   - Location: `CompoundCurvesGraph.tsx:26-35`
   - Spec reference: spec lines 117-119 (pseudo-code `dip1Active = frame >= 30`)

### Notes

- The phase system (`phase` prop with values 1-5) is the main architectural pattern. Each phase is rendered in its own `<Sequence>` within `Part5CompoundReturns.tsx`, which resets the local frame counter to 0. This reset causes Issues 5, 6, and 7 -- visual elements that should persist from previous phases re-animate or are absent at the start.
- Issues 5, 6, and 7 are all manifestations of the same root cause: the Sequence-per-phase architecture does not carry forward the final visual state of the previous phase. A possible fix would be to set initial values for phase 3 that match the final state of phase 2 (e.g., start `curveStartProgress` at 0.08 and `patchCurveProgress` at 1.0 when phase >= 3).
- The `DipIcon` component provides clean, simple SVG icons for all three annotation types (arrow-down, revert, fork). They are appropriately sized and match the spec's description.
- The `CostCallout` component is well-structured as a separate sub-component with proper positioning, styling, and text hierarchy.
- The wobble math is sound: Gaussian dip functions centered at the correct positions with appropriate spread and magnitude, scaled by the wobble progress amount.
- All previously reported high-severity issues from prior audits are resolved.

### Resolution Status

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 1 | Dip annotation fontSize 15 vs spec 16 | Low | UNRESOLVED |
| 2 | Cost subtitle fontSize 16 vs spec 18 | Low | UNRESOLVED |
| 3 | Hold period only ~0.9s vs spec 3s | Medium | UNRESOLVED |
| 4 | Flicker applied globally not per-dip | Low | UNRESOLVED |
| 5 | PDD curve invisible at phase 3 start | Medium | UNRESOLVED |
| 6 | Patching curve re-draws from 8% in phase 3 | Medium | UNRESOLVED |
| 7 | Patching dots re-animate in phase 3 | Low | UNRESOLVED |
| 8 | Dip activation scaled by wobble vs discrete | Low | UNRESOLVED |
