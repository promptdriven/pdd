# Audit: 04a Research Annotations

## Status: ISSUES FOUND

### Requirements Met

1. **Standalone component created**: `ResearchAnnotations.tsx` exists at `/remotion/src/remotion/24a-ResearchAnnotations/` with proper file structure (ResearchAnnotations.tsx, constants.ts, index.ts).
2. **Canvas specs correct**: Resolution 1920x1080, background `#1a1a2e`, 30fps, 15-second duration (450 frames) -- all match spec.
3. **Citation 1 (CodeRabbit)**: Text "AI code: 1.7x more issues" with source "(CodeRabbit, 2025)" is implemented. Fade-in from frame 30 to 120 at 0-to-0.7 opacity matches spec exactly. Uses `easeOutCubic` as specified.
4. **"1.7x" emphasis flash**: Interpolation across frames [60, 80, 120] from [0.7, 1, 0.7] matches spec. Uses `easeInOutSine` as specified.
5. **Citation 2 (DORA)**: Text "AI + strong tests = amplified delivery" with source "(DORA, 2025)" is implemented. Fade-in from frame 150 to 270 at 0-to-0.7 opacity matches spec.
6. **"strong tests" in amber**: Rendered with `color: COLORS.WALLS_AMBER` (#D9944A) and `fontWeight: 600`, matching spec requirement for amber highlighting.
7. **Wall glow intensification**: Interpolation from frame 270 to 360, 0.4 to 1.0, using `easeOutQuad` -- matches spec.
8. **Wall pulse at peak**: Frame range 310-360 with `Math.sin((frame - 310) * 0.2) * 0.15` sinusoidal pulse matches spec.
9. **Mold wall segments**: Three vertical amber (#D9944A) wall segments with dynamic `boxShadow` glow that scales with `wallGlow * wallPulse`.
10. **Wall labels**: "null -> None" label at 0.3 opacity with monospace font, matching spec requirement for "faintly visible" labels.
11. **Citation text styling**: Font 20px, `Inter, sans-serif`, color `#B0B0C0`, lineHeight 1.5, letterSpacing 0.3 -- all match spec.
12. **Dotted connector lines**: Citation 1 has a dotted border-top connector line positioned to the left. Citation 2 has an L-shaped dotted bracket in amber connecting toward walls.
13. **Color constants**: All colors match spec -- background `#1a1a2e`, walls amber `#D9944A`, citation muted `#B0B0C0`, emphasis white `#FFFFFF`.
14. **Beat timings in constants.ts**: All beat frame numbers match the spec animation sequence (CITATION1_START=30, CITATION1_END=120, HOLD=120-150, CITATION2_START=150, CITATION2_END=270, WALL_GLOW_START=270, WALL_GLOW_END=360, WALL_PULSE_START=310, WALL_PULSE_END=360, HOLD_BRIGHTENED=360).

### Issues Found

1. **Not registered in Root.tsx**: The ResearchAnnotations component is not imported or registered as a `<Composition>` in `/remotion/src/remotion/Root.tsx`. Every other composition (01-ColdOpen through 45-BothGenerateFinal, plus all S0x sections) has a corresponding Folder+Composition entry in Root.tsx, but 24a-ResearchAnnotations is missing. This means it cannot be previewed or rendered through Remotion's standard workflow.

2. **Not used in S03-MoldThreeParts parent sequence**: The S03 sequence at `/remotion/src/remotion/S03-MoldThreeParts/Part3MoldThreeParts.tsx` does not import or reference `ResearchAnnotations`. The narration timeslot that should show research annotations (Visual 2, covering "And these walls matter more than you'd think" through "AI with strong tests amplifies delivery" at ~23.6s-52.1s) instead uses the `LiquidInjection` component. The ResearchAnnotations component is entirely orphaned -- it is never rendered in the actual video.

3. **Citation source stagger not implemented**: The spec requires "(CodeRabbit, 2025)" to appear "slightly after" the main citation text with staggered timing (likewise for DORA source). The implementation renders the source line at the same opacity as the parent citation div, meaning the source appears simultaneously with the main text rather than with a deliberate stagger delay.

4. **Section header overlay not in spec**: The component renders a "Research Validates the Walls" header at the top center (lines 221-243) and a "The walls matter more than you'd think" italicized footer (lines 246-268). Neither of these text overlays is described in the spec. The spec calls for only the two citations and the mold walls, with a deliberately muted annotation style ("never PowerPoint bullet points"). These extra text elements contradict the spec's emphasis on minimal, 3Blue1Brown-style annotations.

5. **Wall positioning differs from spec layout**: The spec's ASCII layout diagram shows walls positioned "center-left" with annotations on the right side. The implementation places walls centered around x=400 (left quarter) with citations at x=1100. While functionally similar, the spec suggests the walls should be more center-left (closer to x=500-600 range per the diagram proportions), and the spec shows `right: 120` for annotations (placing them relative to the right edge at ~x=1300), not at a fixed left offset of 1100.

6. **Connector line implementation simplified**: The spec describes a `ConnectorLine` component that "draws on" with `easeOutCubic` easing (an animated draw-on effect). The implementation uses a static dotted border that simply inherits the citation's opacity. There is no progressive line-drawing animation. Similarly, the spec describes a `ConnectorBracket` component for Citation 2 connecting "strong tests" to the wall structure; the implementation uses a static L-shaped border instead of an animated bracket.

### Notes

- The core animation logic within ResearchAnnotations.tsx is well-implemented and closely follows the spec's reference code structure. The interpolation ranges, easing functions, and color values are accurate.
- The critical gap is integration: the component is a fully-formed standalone piece that is never wired into either the Remotion composition registry (Root.tsx) or the S03 parent sequence. To fulfill the spec, the component would need to either replace `LiquidInjection` at Visual 2 in S03-MoldThreeParts, or be composited alongside it (if LiquidInjection is intended to provide the base mold wall visuals while ResearchAnnotations overlays annotations).
- The spec positions this sequence at timestamp 11:15-11:30 of the overall video, which does not align with the S03 constants where Visual 2 (the relevant slot) runs from 23.6s-52.1s of the Part 3 audio. This suggests a misalignment between the global video timestamp in the spec and the section-local timings, but the narration content ("And these walls matter more than you'd think...CodeRabbit...DORA") does map correctly to Visual 2's timeslot.
