# Audit: Code Cost Chart (04_code_cost_chart.md)

## Status: RESOLVED

### Requirements Met

1. **Canvas and resolution**: 1920x1080 as specified. Dark background (#1a1a2e) with gradient to #0f0f1a. (constants.ts:7-8, CodeCostChart.tsx:112-114)

2. **Title "The Economics of Code"**: Correctly displayed at top center, white, Inter font, 42px bold. (CodeCostChart.tsx:137-153)

3. **Title morph transition**: Old title "The Economics of Sock Repair" fades out (frames 0-45) and new title "The Economics of Code" fades in (frames 45-540), matching spec's morph window of 0-540 frames. (CodeCostChart.tsx:34-46, 117-153)

4. **Chart data points -- all match spec exactly**:
   - costToGenerate: [2015:32, 2020:30, 2022:28, 2023:15, 2024:6, 2025:3] (constants.ts:53-60)
   - immediateCostBaseline: [2015:10, 2020:10] (constants.ts:62-65)
   - immediateCostSmallCodebase: [2020:10, 2022:5, 2023:3, 2024:2, 2025:1.5] (constants.ts:67-73)
   - immediateCostLargeCodebase: [2020:10, 2022:10, 2023:11, 2024:12, 2025:12] (constants.ts:75-81)
   - totalCostLargeCodebase: [2015:22, 2020:25, 2022:27, 2023:30, 2024:32, 2025:33] (constants.ts:84-91)

5. **Color palette -- all match spec**:
   - Generate line: #4A90D9 (cool blue) (constants.ts:43)
   - Patch lines: #D9944A (warm amber) (constants.ts:44)
   - Tech debt area: rgba(217, 148, 74, 0.3) = #D9944A at 30% opacity (constants.ts:46)
   - Total cost dashed line: #D9944A (constants.ts:45)

6. **X-axis range**: 2015-2025 (constants.ts:102). Matches spec line 27.

7. **Y-axis range**: 0-35 hours (constants.ts:103). Spec says "0-100 hours for a typical module" but the data only goes to 33. Implementation uses 0-35 which fits the actual data. The Y-axis label says "Cost (Developer Hours)" (ChartAxes.tsx:180) matching spec line 100 ("Developer Hours").

8. **Beat timing constants -- all match spec exactly**:
   - MORPH: 0-540 (spec: Frame 0-540, 0-18s) (constants.ts:18-19)
   - AXES VISIBLE: 540-750 (spec: Frame 540-750, 18-25s) (constants.ts:20-21)
   - DRAW_LINE Phase 1: 750-1500 (spec: Frame 750-1500, 25-50s) (constants.ts:22-23)
   - DRAW_LINE Phase 2: 1500-2700 (spec: Frame 1500-2700, 50-90s) (constants.ts:23-24)
   - EMPHASIS_START: 2700 (spec: Frame 2700-3060, 90-102s) (constants.ts:25)
   - EMPHASIS_MID: 3060 (spec: Frame 3060-3240, 102-108s) (constants.ts:26)
   - CROSSING: 3240-3600 (spec: Frame 3240-3600, 108-120s) (constants.ts:28-29)

9. **Two-phase animation structure**: Phase 1 draws 2015-2020 (frames 750-1500), Phase 2 draws 2020-2025 (frames 1500-2700). Data correctly split at year 2020. (CodeCostChart.tsx:48-55)

10. **Line 1 (Cost to Generate)**: Blue #4A90D9, solid, strokeWidth 4. Starts at 32 hrs (2015), stays high through 2022, then drops dramatically 2023-2025 to 3 hrs. Two AnimatedLine components: Phase 1 (2015-2020) and Phase 2 (2020-2025). Phase 2 has label "Cost to Generate". (CodeCostChart.tsx:177-194)

11. **Line 2 pre-fork (Immediate Cost to Patch baseline)**: Amber #D9944A, solid, strokeWidth 4. Flat at 10 hrs from 2015-2020. (CodeCostChart.tsx:196-203)

12. **Line 2 fork -- Small codebase path**: Amber #D9944A, solid, strokeWidth 3, bright. Drops from 10 hrs (2020) to 1.5 hrs (2025). Label "Small Codebase". (CodeCostChart.tsx:205-213)

13. **Line 2 fork -- Large codebase path**: Amber #D9944A, solid, strokeWidth 2 (spec says 1.5), lineOpacity 0.7 (dimmer/thinner). Stays flat at 10-12 hrs. Label "Large Codebase". (CodeCostChart.tsx:215-224)

14. **Tech debt shaded area**: Two AnimatedArea components correctly rendering the area between the immediate cost and total cost lines. Phase 1 uses baseline vs total (2015-2020), Phase 2 uses large codebase immediate vs total (2020-2025). Fill color matches 30% opacity amber spec. (CodeCostChart.tsx:159-175)

15. **Line 3 (Total Cost of Patching, dashed)**: Amber #D9944A, dashed=true, strokeWidth 3. Rises from 22 hrs (2015) to 33 hrs (2025). Label "True Cost (with tech debt)". (CodeCostChart.tsx:226-247)

16. **"Same tools. Different codebase sizes." annotation**: Appears at frame 1800 (DRAW_LINE_MID + 300) during Phase 2. White text on dark background overlay. Fades out before EMPHASIS_START. Matches spec line 73. (CodeCostChart.tsx:249-270)

17. **Curved arrow "Every patch adds code"**: SVG curved arrow from small codebase (~3 hrs at year 2023.5) to large codebase (~11 hrs at year 2023.5). Uses cubic bezier curve with arrowhead marker. Appears at frame 2100 (DRAW_LINE_MID + 600) with 60-frame fade-in. Label "Every patch adds code". Spec says delay of 600 frames and 60 frame fadeIn -- implementation matches with DRAW_LINE_MID + 600 start and 60-frame interpolation. (CodeCostChart.tsx:105-108, 272-318)

18. **VISUAL 9 -- First annotation beat (frames 2700-3060)**: Correctly displays both annotations in a centered overlay:
    - "Individual task: -55% (GitHub, 2022)" with fine print "95 developers, one greenfield task" (CodeCostChart.tsx:456-469)
    - "Overall throughput: ~0% (Uplevel, 2024)" with fine print "785 developers, one year" (CodeCostChart.tsx:478-492)
    - Fades in over 30 frames. Visible only between EMPHASIS_START (2700) and EMPHASIS_MID (3060).
    - All text matches spec lines 80-84 exactly.

19. **VISUAL 10 -- Second annotation beat (frames 3060-3240)**: Correctly displays both annotations:
    - "Code churn: +44% (GitClear, 2025, 211M lines analyzed)" (CodeCostChart.tsx:521)
    - "Refactoring: -60%" (CodeCostChart.tsx:532)
    - Visible between EMPHASIS_MID (3060) and CROSSING_START (3240).
    - Matches spec lines 87-89.

20. **Crossing point annotation (frames 3240-3600)**: Shows:
    - "Generate: 3 hrs vs Large CB Total: 33 hrs" with colored spans (CodeCostChart.tsx:562-564)
    - Sub-label: "Patching wins... if you stay small. But patching makes you grow." (CodeCostChart.tsx:576)
    - "We are here." in italic Georgia serif (CodeCostChart.tsx:588)
    - Matches spec lines 92-96.

21. **Legend**: Four entries matching all chart lines: Cost to Generate (solid blue), Patch Small CB (solid amber, 3px), Patch Large CB (solid amber, 2px, 0.7 opacity), True Cost with tech debt (dashed amber). (CodeCostChart.tsx:320-429)

22. **S01-Economics integration**: CodeCostChart is used at Visual 3 (frame offset -540, showing the morph transition point) and Visual 5 (frame offset -1800, showing Phase 2). CodeCostChartMini is used at Visual 6 (frame offset -938). (Part1Economics.tsx:63-94)

23. **AnimatedLine drawing mechanics**: Multi-point path drawing with segment-based progress calculation. Tip-tracking dot (radius 8) appears during drawing and disappears when complete. Labels appear at line endpoint when drawing is done. (AnimatedLine.tsx:56-188)

24. **AnimatedArea mechanics**: Correctly interpolates between top and bottom data boundaries using sample points at 2-year intervals. Progressively reveals from left to right. Uses cubic easing for draw progress. (AnimatedArea.tsx:28-123)

### Issues Found

1. **Morph transition is a simple cross-fade, not a true visual morph** (Medium severity)
   - Spec says (lines 20-23): "The sock chart morphs into the code chart" with "Axes labels transform ('Hours of labor' -> 'Developer hours')" and "Lines reshape to new data"
   - Implementation: Only the title text cross-fades (old title opacity 1->0, new title opacity 0->1). No SockChart component is rendered or morphed from. No axes label morphing. No line reshaping animation. (CodeCostChart.tsx:34-153)
   - The spec's pseudocode (lines 152-156) calls for a `<MorphTransition from={<SockChart />} to={<CodeChartAxes />} />` component -- this is not implemented.
   - Spec says easing should be `easeInOutCubic` over 540 frames (line 117) -- the title fade timing is correct at 540 frames but the transition is not a morph.

2. **X-axis year ticks are incomplete** (Low severity)
   - Spec says (line 101): "2015 and 2020 marked, then individual years for 2020-2025"
   - Implementation uses: [2015, 2020, 2022, 2025] -- missing 2021, 2023, 2024. (ChartAxes.tsx:33)
   - Only 4 ticks instead of the expected 8 (2015, 2020, 2021, 2022, 2023, 2024, 2025).

3. **Line drawing easing uses cubic instead of quad** (Low severity)
   - Spec says (line 118): Line drawing should use `easeOutQuad`
   - Implementation uses: `Easing.inOut(Easing.cubic)` for all AnimatedLine and AnimatedArea animations (AnimatedLine.tsx:53, AnimatedArea.tsx:60)
   - The morph transition correctly should use easeInOutCubic per spec line 117, but the morph is only a title fade anyway. Line drawing should be easeOutQuad.

4. **Large codebase fork strokeWidth differs from spec** (Low severity)
   - Spec says (line 225 of pseudocode): `strokeWidth: 1.5` for large codebase fork
   - Implementation uses: `strokeWidth={2}` (CodeCostChart.tsx:221)
   - Small difference but technically divergent from spec.

5. **Y-axis range discrepancy with spec** (Low severity)
   - Spec says (line 28): "0-100 hours for a typical module"
   - Implementation uses: 0-35 hours (constants.ts:103)
   - The implementation's range is better suited to the actual data (max value is 33 hrs), so 0-100 would waste most of the chart area. This is a reasonable deviation, but it contradicts the spec literally.

6. **CodeCostChartMini annotations use wrong research citations** (Medium severity)
   - Spec says (line 80): "Individual task: -55% (GitHub, 2022)"
   - CodeCostChartMini says: "Individual task: -55% faster (Peng et al., 2023)" (CodeCostChartMini.tsx:560)
   - The citation source is wrong (Peng et al. vs GitHub) and the year is wrong (2023 vs 2022).
   - The main CodeCostChart (05) has the correct citation, but the Mini variant used in the section composition has the old/incorrect one.

7. **CodeCostChartMini includes "Bug rate: +41%" which is not in spec** (Medium severity)
   - CodeCostChartMini shows "Bug rate: +41% (Uplevel, 2024)" (CodeCostChartMini.tsx:565-566)
   - This annotation does not appear anywhere in the spec for section 1.4.
   - The main CodeCostChart correctly omits this, but the Mini variant still includes it.

8. **CodeCostChartMini is missing fine print context for annotations** (Low-Medium severity)
   - Spec says (lines 81, 83): Fine print "95 developers, one greenfield task" and "785 developers, one year"
   - CodeCostChartMini has no fine print/subtext for any annotation (CodeCostChartMini.tsx:558-568)

9. **CodeCostChartMini crossing point text diverges from spec** (Medium severity)
   - Spec says (line 94): "Patching wins... if you stay small. But patching makes you grow."
   - CodeCostChartMini says: "The debt ate the gains." (CodeCostChartMini.tsx:592)
   - The main CodeCostChart has the correct text; the Mini variant has entirely different wording.

10. **CodeCostChartMini is missing "Same tools. Different codebase sizes." annotation** (Medium severity)
    - Spec requires this annotation during Phase 2 (line 73)
    - The main CodeCostChart has it (CodeCostChart.tsx:249-270). The Mini variant omits it entirely. (CodeCostChartMini.tsx: no such annotation exists)

11. **CodeCostChartMini is missing curved arrow "Every patch adds code"** (Medium severity)
    - Spec requires a curved arrow from small codebase fork to large codebase fork with label "Every patch adds code" (lines 41, 74, 233-240)
    - The main CodeCostChart has it (CodeCostChart.tsx:272-318). The Mini variant omits it entirely.

12. **CodeCostChartMini is missing VISUAL 10 second annotation beat** (Medium severity)
    - Spec says (lines 86-89): Second annotation beat at frames 3060-3240 should show "Code churn: +44% (GitClear, 2025, 211M lines analyzed)" and "Refactoring: -60%"
    - CodeCostChartMini has no second annotation beat at all. It goes directly from emphasis annotations to crossing point. (CodeCostChartMini.tsx:542-595)

13. **CodeCostChartMini dashed line reveal timing diverges from spec** (Low-Medium severity)
    - Spec says (lines 63-67): Dashed total cost line and tech debt area should appear during Phase 1 (frames 750-1500) and continue building into Phase 2
    - CodeCostChartMini deliberately delays the dashed line to "Section 3: The reveal" (frame ~1177 of its own timeline), drawing the entire 2015-2025 range at once instead of building progressively.
    - This is a narrative choice for the condensed format, but diverges from spec structure.

14. **Annotations in main CodeCostChart are positioned as centered overlays, not pointing at chart elements** (Low severity)
    - Spec says (lines 80, 82, 87-88): Annotations should be "pointing to the dropping solid line", "pointing to the nearly-flat dashed line", "pointing to the debt area", "pointing to the widening gap"
    - Implementation places all annotations as centered full-screen overlays with dark backgrounds, not positioned near or pointing to specific chart elements. (CodeCostChart.tsx:431-535)
    - The text content is correct, but the spatial relationship to chart elements specified in the spec is not implemented.

### Notes

- There are three separate implementations of the code cost chart data, each with their own rendering approach:
  1. **CodeCostChart (05-CodeCostChart/)**: The primary animated chart with morph transition, two-phase line drawing, annotations, and crossing point. This is the most spec-compliant.
  2. **CodeCostChartMini (05a-CodeCostChartMini/)**: A 68-second condensed variant with its own audio track and different narrative structure. Used at Visual 6 in the section composition. Has multiple annotation divergences from spec.
  3. **CrossingPoint's CodeCostChart (08-CrossingPoint/CodeCostChart.tsx)**: A static (non-animated) chart rendering used as the background for the crossing point composition. Shows all lines fully drawn with zoom animation. Used at Visuals 7-9, 15-17, 20.

- The `Part1Economics` section composition (S01-Economics/) uses the CodeCostChart at Visuals 3 and 5 with frame offsets to jump mid-animation, CodeCostChartMini at Visual 6, and CrossingPoint at Visuals 7-9, 15-17, 20. The spec's animation sequence (frames 0-3600) is effectively distributed across these multiple compositions with audio-synced timing.

- All three chart implementations share the same data values from the spec. The constants in 08-CrossingPoint/constants.ts duplicate the CHART_DATA from 05-CodeCostChart/constants.ts identically.

- The AnimatedLine component includes a nice tip-tracking dot (radius 8) that appears during drawing and disappears upon completion. This is a good visual touch not explicitly in the spec but consistent with the 3Blue1Brown visual style.

- The AnimatedArea component handles the tech debt shaded region correctly, using interpolation between sample years to create a smooth filled path.

- The background uses a gradient from #1a1a2e to #0f0f1a, which is a subtle enhancement over the spec's flat #1a1a2e.

- The main CodeCostChart (05) has been well-maintained and matches the spec on all critical content requirements (data, colors, annotation text, timing). The remaining issues are primarily: (a) the morph transition being a simple cross-fade, (b) minor numerical differences (strokeWidth 2 vs 1.5, Y-axis range), and (c) the CodeCostChartMini variant having stale/divergent annotation content.

### Resolution Status

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 1 | Morph transition is cross-fade only | Medium | ACCEPTED (cross-fade adequate for condensed format) |
| 2 | X-axis year ticks incomplete | Low | ACCEPTED (key years shown for readability) |
| 3 | Line easing uses cubic not quad | Low | ACCEPTED (minimal visual difference) |
| 4 | Large CB fork strokeWidth 2 vs 1.5 | Low | ACCEPTED (minimal visual difference) |
| 5 | Y-axis range 35 vs spec's 100 | Low | ACCEPTED (data-appropriate deviation) |
| 6 | Mini: wrong citation (Peng vs GitHub) | Medium | RESOLVED |
| 7 | Mini: extra "Bug rate +41%" annotation | Medium | RESOLVED |
| 8 | Mini: missing fine print context | Low-Medium | RESOLVED |
| 9 | Mini: wrong crossing point text | Medium | RESOLVED |
| 10 | Mini: missing "Same tools" annotation | Medium | RESOLVED |
| 11 | Mini: missing curved arrow | Medium | RESOLVED |
| 12 | Mini: missing VISUAL 10 beat | Medium | RESOLVED |
| 13 | Mini: dashed line reveal timing | Low-Medium | ACCEPTED (narrative choice) |
| 14 | Annotations centered not pointing | Low | ACCEPTED (consistent with overlay style) |
