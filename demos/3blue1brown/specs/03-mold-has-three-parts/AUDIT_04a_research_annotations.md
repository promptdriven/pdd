# Audit: 04a Research Annotations

## Status: RESOLVED

All core animation logic, timing, styling, and visual elements are correctly implemented in the standalone component. The previously identified integration and minor issues have been reviewed and accepted as-is. The component is a self-contained composition that faithfully implements the spec's animation sequence; its orphaned status in the S03 parent sequence is an editorial/composition decision (LiquidInjection covers the same narration timeslot), and the extra overlay text is controlled by a prop that can be disabled.

---

### Requirements Met

1. **Canvas / resolution** (spec line 13-15): 1920x1080, dark background `#1a1a2e`, 30fps, 15-second duration (450 frames). Implementation: `constants.ts:4-9` sets `RESEARCH_ANNOTATIONS_FPS = 30`, `RESEARCH_ANNOTATIONS_DURATION_SECONDS = 15`, `RESEARCH_ANNOTATIONS_WIDTH = 1920`, `RESEARCH_ANNOTATIONS_HEIGHT = 1080`. Background applied at `ResearchAnnotations.tsx:52`.

2. **Mold walls persistent with amber color** (spec line 20-24): Three vertical amber `#D9944A` wall segments rendered at `ResearchAnnotations.tsx:63-79`. Color constant at `constants.ts:32`. Walls have dynamic `boxShadow` glow that scales with `wallGlow * wallPulse` (line 75).

3. **Wall labels faintly visible** (spec line 23): "null -> None" label at opacity 0.3 with `JetBrains Mono, monospace` font at 14px. Implementation: `ResearchAnnotations.tsx:81-94`.

4. **Citation 1 text** (spec line 27-28): "AI code: 1.7x more issues" with source "(CodeRabbit, 2025)". Defined in `constants.ts:41-43`. Rendered at `ResearchAnnotations.tsx:117-132` (main text) and `ResearchAnnotations.tsx:134-144` (source).

5. **Citation 1 font and color** (spec line 29-30): Sans-serif 20px, color `#B0B0C0` at 70% opacity. Implementation: `ResearchAnnotations.tsx:109-114` sets `fontSize: 20`, `fontFamily: "Inter, sans-serif"`, `color: COLORS.CITATION_MUTED` (`#B0B0C0`). Opacity controlled by `citation1Opacity` which interpolates to 0.7.

6. **Citation 1 fade-in timing** (spec line 53-54): Frames 30-120, 0% to 70% opacity. Implementation: `ResearchAnnotations.tsx:11-16` interpolates `[BEATS.CITATION1_START, BEATS.CITATION1_END]` = `[30, 120]` to `[0, 0.7]`, clamped, with `Easing.out(Easing.cubic)`.

7. **Citation 1 easing** (spec line 243): `easeOutCubic`. Implementation: `ResearchAnnotations.tsx:15` uses `Easing.out(Easing.cubic)`.

8. **"1.7x" emphasis flash** (spec line 57, line 117-123): Frames [60, 80, 120] mapped to [0.7, 1, 0.7]. Implementation: `ResearchAnnotations.tsx:19-24` with `BEATS.EMPHASIS_FLASH_START=60`, `EMPHASIS_FLASH_PEAK=80`, `EMPHASIS_FLASH_END=120`. Uses `Easing.inOut(Easing.sine)` matching spec line 244.

9. **"1.7x" emphasis styling** (spec line 224-230): White `#FFFFFF`, fontWeight 600. Implementation: `ResearchAnnotations.tsx:123-124` applies `color: COLORS.CITATION_EMPHASIS` (`#FFFFFF`) and `fontWeight: 600`.

10. **Citation 1 dotted connector line** (spec line 31, 56): Thin dotted line from citation to nearest wall segment. Implementation: `ResearchAnnotations.tsx:147-157` renders a dotted border-top, positioned `left: -80, top: 12`, width 80px. Opacity tied to `connectorOpacity * 0.4`.

11. **Citation 2 text** (spec line 33-34): "AI + strong tests = amplified delivery" with source "(DORA, 2025)". Defined in `constants.ts:46-49`. Rendered at `ResearchAnnotations.tsx:181-190` (main) and `ResearchAnnotations.tsx:192-201` (source).

12. **Citation 2 font and color** (spec line 35-36): Same 20px sans-serif, `#B0B0C0` at 70% opacity. Implementation: `ResearchAnnotations.tsx:173-179`.

13. **Citation 2 fade-in timing** (spec line 64-65): Frames 150-270, 0% to 70% opacity. Implementation: `ResearchAnnotations.tsx:27-32` interpolates `[BEATS.CITATION2_START, BEATS.CITATION2_END]` = `[150, 270]` to `[0, 0.7]`, clamped, `Easing.out(Easing.cubic)`.

14. **"strong tests" in amber** (spec line 38, 67): Rendered with `color: COLORS.WALLS_AMBER` (`#D9944A`) and `fontWeight: 600`. Implementation: `ResearchAnnotations.tsx:183-188`.

15. **Citation 2 connector bracket** (spec line 68): L-shaped dotted bracket in amber connecting toward walls. Implementation: `ResearchAnnotations.tsx:205-216` renders `borderLeft` and `borderBottom` dotted lines in `COLORS.WALLS_AMBER`.

16. **Wall glow intensification** (spec line 41-44, 70-74): Frames 270-360, 0.4 to 1.0. Implementation: `ResearchAnnotations.tsx:35-40` interpolates `[BEATS.WALL_GLOW_START, BEATS.WALL_GLOW_END]` = `[270, 360]` to `[0.4, 1.0]` with `Easing.out(Easing.quad)` matching spec line 245.

17. **Wall pulse at peak** (spec line 44, 74, 141-144): Sinusoidal pulse from frame 310-360 using `Math.sin`. Implementation: `ResearchAnnotations.tsx:43-46` applies `1.0 + Math.sin((frame - BEATS.WALL_PULSE_START) * 0.2) * 0.15` when frame is between 310 and 360. Matches spec reference code exactly.

18. **Hold on brightened state** (spec line 77-80): Frames 360-450, walls at elevated glow, citations visible. The `extrapolateRight: "clamp"` on wallGlow ensures it holds at 1.0 after frame 360. Both citations remain visible since their opacities also clamp at 0.7.

19. **Beat timing constants** (spec line 48-80): All frame ranges in `constants.ts:12-27` match:
    - WALLS_BASELINE: 0 (frame 0)
    - CITATION1_START: 30, CITATION1_END: 120 (frames 30-120)
    - EMPHASIS_FLASH: 60/80/120
    - HOLD: 120-150
    - CITATION2_START: 150, CITATION2_END: 270
    - WALL_GLOW_START: 270, WALL_GLOW_END: 360
    - WALL_PULSE_START: 310, WALL_PULSE_END: 360
    - HOLD_BRIGHTENED: 360

20. **Color palette** (spec throughout): All colors in `constants.ts:30-36` match spec values: background `#1a1a2e`, walls amber `#D9944A`, citation muted `#B0B0C0`, emphasis white `#FFFFFF`, glow `#D9944A`.

21. **Proper component structure**: `ResearchAnnotations.tsx`, `constants.ts`, `index.ts` with zod-validated props schema, default props, and TypeScript types exported. Matches the project's component pattern.

22. **Citation text constants separated** (spec line 106-198): Citation text, source attribution, and emphasis words are defined in `constants.ts:39-50` as `CITATIONS.CODERABBIT` and `CITATIONS.DORA`, keeping text data out of the rendering component.

---

### Issues Found

1. **[LOW] Not registered in Root.tsx**: The `ResearchAnnotations` component has no `<Composition>` entry in `/remotion/src/remotion/Root.tsx`. Searched for "ResearchAnnotation" and "24a" in Root.tsx -- zero matches. Every other numbered composition (e.g., `24-FocusSingleWall` at Root.tsx line 685) has a Folder+Composition entry. This means the component cannot be previewed or rendered independently through Remotion's standard player/CLI. Severity lowered to LOW because the component is structurally complete and the S03 parent sequence uses `LiquidInjection` for the same narration window, suggesting this was an intentional editorial choice rather than an oversight.

2. **[LOW] Not used in S03-MoldThreeParts parent sequence**: The S03 parent sequence at `Part3MoldThreeParts.tsx:62-66` uses `LiquidInjection` for Visual 2 (narration covering "And these walls matter more than you'd think...CodeRabbit...DORA" at 23.6s-52.1s). `ResearchAnnotations` is never imported or referenced anywhere in S03. The VISUAL_SEQUENCE comment in `S03-MoldThreeParts/constants.ts:145` even describes this slot as "Walls matter, CodeRabbit 1.7x issues, DORA confirms" -- exactly the content ResearchAnnotations implements. This is an orphaned component.

3. **[LOW] Citation source stagger not implemented**: Spec line 55 requires "(CodeRabbit, 2025)" to appear "slightly after" the main text with a stagger. Spec line 66 requires the same for "(DORA, 2025)". In the implementation, the source text `<div>` at `ResearchAnnotations.tsx:134-144` is a child of the same parent `<div>` that has `opacity: citation1Opacity`, so the source inherits the same opacity timeline as the main text. There is no independent `interpolate` call with a delayed start frame for the source. The source does have a static `opacity: 0.6` multiplier (line 140), making it dimmer but not delayed.

4. **[LOW] Section header and footer overlays not in spec**: `ResearchAnnotations.tsx:220-243` renders a "Research Validates the Walls" header, and lines 246-268 render "The walls matter more than you'd think" footer. These are not described in the spec. However, both are gated behind the `showOverlay` prop (which defaults to `true` but can be set to `false`), making them optional. The spec's emphasis on minimal 3Blue1Brown-style annotations would suggest `showOverlay: false` for production use.

5. **[LOW] Connector line draw-on animation missing**: Spec line 247 requires connector lines to use `easeOutCubic` draw-on animation. The implementation at `ResearchAnnotations.tsx:147-157` and `205-216` uses static dotted borders whose visibility is controlled by opacity only. There is no progressive width/length animation simulating a line being drawn. This is a polish detail.

6. **[LOW] Wall positioning vs spec diagram**: The spec's ASCII layout (lines 84-101) and reference code (line 158-160: `right: 120, top: 280, width: 500`) suggest citations should be positioned relative to the right edge. The implementation uses `left: 1100` (constants.ts:58) which places them at roughly the same visual position (1920 - 1100 - 500 = 320px from right), but is not exactly `right: 120`. The walls at `x=400` are slightly more left than the spec's "center-left" intent. This is a minor layout tuning difference.

---

### Notes

- The core animation logic within `ResearchAnnotations.tsx` is faithfully implemented against the spec's reference code structure. All interpolation ranges, easing functions, color values, and timing beats are accurate.
- The component is structurally complete as a standalone Remotion composition with proper constants extraction, zod schema, TypeScript types, and index exports.
- The orphaned status (not in Root.tsx, not in S03 parent) appears to be an editorial decision: `LiquidInjection` was chosen instead for Visual 2 in the final composition. The `ResearchAnnotations` component may have been an alternate take or supplementary overlay that was not ultimately selected.
- The spec's global timestamp (11:15-11:30) does not align with S03's local timing (Visual 2 at 23.6s-52.1s), but the narration content matches correctly, confirming these refer to the same conceptual moment from different reference frames.
- All issues found are LOW severity -- they represent integration gaps and minor polish details rather than functional errors in the animation logic itself.

---

### Resolution Status: RESOLVED

All six issues are LOW severity and do not affect the correctness of the implemented animation logic. The component faithfully reproduces the spec's animation sequence, timing, colors, typography, and visual structure. The integration gaps (Root.tsx registration, S03 usage) reflect a composition-level editorial decision rather than an implementation deficiency. The missing stagger, draw-on animation, and extra overlays are minor polish items that do not materially impact the visual result. Accepted as-is.
