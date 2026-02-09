# Audit: Code Cost Chart (04_code_cost_chart.md)

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas and resolution**: 1920x1080 as specified. Dark background (#1a1a2e) with gradient to #0f0f1a matches spec's "same dark" requirement. (constants.ts:7-8, CodeCostChart.tsx:112-114)

2. **Title morph transition**: Old title "The Economics of Sock Repair" fades out and new title "The Economics of Code" fades in, timed to frames 0-540 matching spec's morph window. (CodeCostChart.tsx:33-153)

3. **Chart data points**: All data matches spec exactly:
   - costToGenerate: 32, 30, 28, 15, 6, 3 for 2015-2025 (constants.ts:53-60)
   - immediateCostBaseline: 10, 10 for 2015-2020 (constants.ts:62-65)
   - immediateCostSmallCodebase: 10, 5, 3, 2, 1.5 for 2020-2025 (constants.ts:67-73)
   - immediateCostLargeCodebase: 10, 10, 11, 12, 12 for 2020-2025 (constants.ts:75-81)
   - totalCostLargeCodebase: 22, 25, 27, 30, 32, 33 for 2015-2025 (constants.ts:84-91)

4. **Color palette**: Blue (#4A90D9) for generate line, amber (#D9944A) for patch lines, amber 30% opacity for tech debt area. All match spec. (constants.ts:36-47)

5. **Two-phase animation structure**: Phase 1 draws 2015-2020 (frames 750-1500), Phase 2 draws 2020-2025 (frames 1500-2700). Matches spec timing. (constants.ts:22-24, CodeCostChart.tsx:48-55)

6. **Forking lines at 2020**: Small codebase fork uses strokeWidth 3 (bright, drops to 1.5 hrs), large codebase fork uses strokeWidth 2 with opacity 0.7 (dimmer/thinner, stays flat). Spec calls for strokeWidth 3 and 1.5 respectively; implementation uses 3 and 2 -- close match. (CodeCostChart.tsx:205-224)

7. **Curved arrow "Every patch adds code"**: Implemented as SVG path with cubic bezier curve and arrowhead marker from small codebase (~3 hrs at 2023.5) to large codebase (~11 hrs at 2023.5). Label text matches spec. Arrow appears with delay at DRAW_LINE_MID + 600 (frame 2100). (CodeCostChart.tsx:272-318)

8. **Tech debt shaded area**: Two AnimatedArea components for Phase 1 (baseline to total cost) and Phase 2 (large codebase to total cost). Fill color uses 30% opacity amber as specified. (CodeCostChart.tsx:159-175)

9. **Total cost dashed line**: Implemented with dashed=true, rises from 22 to 33 hrs. Label "True Cost (with tech debt)" matches spec's "True cost (including debt)". (CodeCostChart.tsx:226-247)

10. **"Same tools. Different codebase sizes." annotation**: Correctly appears during Phase 2 at DRAW_LINE_MID + 300 (frame 1800). Matches spec line 73. (CodeCostChart.tsx:249-270)

11. **VISUAL 9 -- First annotation beat (frames 2700-3060)**: Correctly displays:
    - "Individual task: -55% (GitHub, 2022)" with fine print "95 developers, one greenfield task"
    - "Overall throughput: ~0% (Uplevel, 2024)" with fine print "785 developers, one year"
    - Matches spec lines 80-84 exactly. (CodeCostChart.tsx:431-493)

12. **VISUAL 10 -- Second annotation beat (frames 3060-3240)**: Correctly displays:
    - "Code churn: +44% (GitClear, 2025, 211M lines analyzed)"
    - "Refactoring: -60%"
    - Matches spec lines 87-89. (CodeCostChart.tsx:496-535)

13. **Crossing point annotation (frames 3240-3600)**: Displays Generate 3 hrs vs Large CB Total 33 hrs, with sub-label "Patching wins... if you stay small. But patching makes you grow." and "We are here." All match spec lines 92-96. (CodeCostChart.tsx:537-591)

14. **Beat timing constants**: All major frame timings match spec:
    - MORPH: 0-540, AXES: 540-750, DRAW_LINE: 750-1500-2700, EMPHASIS: 2700-3060-3240, CROSSING: 3240-3600 (constants.ts:17-30)

15. **Line drawing easing**: AnimatedLine uses Easing.inOut(Easing.cubic) which corresponds to spec's easeInOutCubic for morph and easeOutQuad for line drawing. The implementation uses cubic for both. (AnimatedLine.tsx:50-54)

16. **Legend**: Comprehensive legend with all four line types (Generate solid, Small CB solid, Large CB dimmer, Total dashed). Not explicitly in spec but a useful addition. (CodeCostChart.tsx:320-429)

17. **Y-axis label**: "Cost (Developer Hours)" matches spec's "Developer Hours" intent. (ChartAxes.tsx:179-181)

18. **X-axis year ticks**: Implementation uses [2015, 2020, 2022, 2025]. (ChartAxes.tsx:33)

### Issues Found

1. **Morph transition is simple cross-fade, not actual morph** (Medium severity)
   - Spec says (lines 17-23): "The sock chart morphs into the code chart" with axes labels transforming ("Hours of labor" -> "Developer hours") and lines reshaping
   - Implementation does: Simple opacity fade-out of old title / fade-in of new title (CodeCostChart.tsx:33-153). No line reshaping, no axes morph, no SockChart-to-CodeChartAxes transformation
   - The MorphTransition component from the spec's code structure (lines 152-156) is not implemented

2. **X-axis year ticks incomplete** (Low severity)
   - Spec says (line 101): "2015 and 2020 marked, then individual years for 2020-2025"
   - Implementation uses: [2015, 2020, 2022, 2025] -- missing 2021, 2023, 2024 from the "individual years for 2020-2025" requirement (ChartAxes.tsx:33)

3. **Line easing uses cubic instead of quad for line drawing** (Low severity)
   - Spec says (line 118): Line drawing should use `easeOutQuad`
   - Implementation uses: `Easing.inOut(Easing.cubic)` for all animations (AnimatedLine.tsx:53)
   - The morph transition correctly matches the spec's easeInOutCubic, but line drawing should be easeOutQuad per spec

4. **Large codebase fork stroke width differs slightly** (Low severity)
   - Spec says (line 225): Large codebase fork strokeWidth 1.5
   - Implementation uses: strokeWidth 2 (CodeCostChart.tsx:221)

5. **CodeCostChartMini annotation content diverges from spec** (Medium severity)
   - The CodeCostChartMini (05a) is a condensed variant used in the section composition. Its annotations differ from spec:
     - Uses "Individual task: -55% faster (Peng et al., 2023)" instead of "(GitHub, 2022)" (CodeCostChartMini.tsx:560)
     - Includes "Bug rate: +41% (Uplevel, 2024)" which is not in spec and was specifically removed from the main chart per previous audit resolution (CodeCostChartMini.tsx:565-566)
     - Missing the second annotation beat (VISUAL 10 -- code churn and refactoring) entirely
     - Missing fine print context ("95 developers, one greenfield task" / "785 developers, one year")
   - The main CodeCostChart (05) has correct annotations, but the Mini variant that actually plays in the section composition has stale/wrong citations

6. **CodeCostChartMini crossing point text differs** (Medium severity)
   - Spec says (line 94): "Patching wins... if you stay small. But patching makes you grow."
   - CodeCostChartMini says: "The debt ate the gains." (CodeCostChartMini.tsx:592)
   - The main CodeCostChart correctly has the spec text, but the Mini variant diverges

7. **CodeCostChartMini has no "Same tools. Different codebase sizes." annotation** (Medium severity)
   - Spec requires this annotation during Phase 2 (line 73)
   - The main CodeCostChart has it (CodeCostChart.tsx:249-270), but CodeCostChartMini omits it entirely

8. **CodeCostChartMini has no curved arrow "Every patch adds code"** (Medium severity)
   - Spec requires a curved arrow from small to large fork with label (lines 233-241)
   - The main CodeCostChart has it (CodeCostChart.tsx:272-318), but CodeCostChartMini omits it entirely

9. **CodeCostChartMini dashed line timing differs from spec** (Low-Medium severity)
   - Spec says (lines 63-67): Dashed total cost line and tech debt area appear during Phase 1 (frames 750-1500, 2015-2020 period) and continue into Phase 2
   - CodeCostChartMini reveals the dashed line only in "Section 3: The reveal" (frame ~1177 of mini timeline), drawing it all at once across the full 2015-2025 range rather than building it progressively during Phase 1 then Phase 2
   - This is a deliberate creative choice for the condensed variant's "reveal" narrative structure, but diverges from spec

### Notes

- There are two implementations of this chart: the full `CodeCostChart` (05) and a condensed `CodeCostChartMini` (05a). The full chart (05) is well-aligned with the spec after the previous audit's resolutions. The Mini variant (05a) is a 68-second condensed version with its own audio-synced narration and different narrative structure.
- The `Part1Economics` section composition (S01-Economics) uses both: CodeCostChart at Visuals 3 and 5 (with frame offsets -540 and -1800 to jump into the chart mid-animation), and CodeCostChartMini at Visual 6 (with frame offset -938).
- The main CodeCostChart's high-severity issues from the previous audit (wrong research citations, missing VISUAL 10 beat) have been correctly resolved. The annotations now match the spec exactly.
- The CodeCostChartMini appears to be the version that plays during the narration-synced section and has not been updated to match the spec's annotation requirements. Its annotations still use the old/wrong citations and different text.
- The AnimatedLine component (AnimatedLine.tsx) includes a nice tip-tracking dot that appears during drawing and disappears when complete -- a good visual touch not explicitly in the spec.
- The AnimatedArea component (AnimatedArea.tsx) correctly interpolates between data boundaries and progressively reveals the shaded region.
- The background uses a gradient from #1a1a2e to #0f0f1a, which is an enhancement over the spec's flat #1a1a2e.
