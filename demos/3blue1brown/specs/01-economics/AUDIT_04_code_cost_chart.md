# Audit: Code Cost Chart (04_code_cost_chart.md)

## Status: PASS

All previously identified issues have been resolved or accepted as intentional deviations. The main CodeCostChart and CodeCostChartMini are both fully functional and spec-compliant on all material requirements.

---

### Requirements Verified

1. **Canvas and resolution**: 1920x1080 as specified. Dark background (#1a1a2e) with gradient to #0f0f1a. Confirmed visually in rendered stills. (constants.ts:7-8, CodeCostChart.tsx:112-114)

2. **Title "The Economics of Code"**: Correctly displayed at top center, white, Inter font, 42px bold. Confirmed in frame 600 render. (CodeCostChart.tsx:137-153)

3. **Title morph transition**: Old title "The Economics of Sock Repair" fades out (frames 0-45) and new title "The Economics of Code" fades in (frames 45-540). Frame 20 render shows the old title in a dimmed state. Frame 600 render shows the new title fully visible. (CodeCostChart.tsx:34-46, 117-153)

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
   - All colors confirmed visually in renders: blue line at top, amber lines below, amber shaded area between immediate cost and total cost.

6. **X-axis range**: 2015-2025 (constants.ts:102). Matches spec.

7. **Y-axis range**: 0-35 hours (constants.ts:103). Spec says "0-100 hours for a typical module" but actual data maxes at 33 hrs. Using 0-35 is a data-appropriate deviation that makes the chart readable. Y-axis label "Cost (Developer Hours)" matches spec. Confirmed in frame 600 render.

8. **Beat timing constants -- all match spec exactly**:
   - MORPH: 0-540 (spec: Frame 0-540, 0-18s) (constants.ts:18-19)
   - AXES VISIBLE: 540-750 (spec: Frame 540-750, 18-25s) (constants.ts:20-21)
   - DRAW_LINE Phase 1: 750-1500 (spec: Frame 750-1500, 25-50s) (constants.ts:22-23)
   - DRAW_LINE Phase 2: 1500-2700 (spec: Frame 1500-2700, 50-90s) (constants.ts:23-24)
   - EMPHASIS_START: 2700 (spec: Frame 2700-3060, 90-102s) (constants.ts:25)
   - EMPHASIS_MID: 3060 (spec: Frame 3060-3240, 102-108s) (constants.ts:26)
   - CROSSING: 3240-3600 (spec: Frame 3240-3600, 108-120s) (constants.ts:28-29)

9. **Two-phase animation structure**: Phase 1 draws 2015-2020 (frames 750-1500), Phase 2 draws 2020-2025 (frames 1500-2700). Data correctly split at year 2020. Confirmed visually: frame 1200 shows lines drawn only to ~2020; frame 2100 shows fork extending to ~2023. (CodeCostChart.tsx:48-55)

10. **Line 1 (Cost to Generate)**: Blue #4A90D9, solid, strokeWidth 4. Starts at 32 hrs (2015), stays high through 2022, then drops dramatically 2023-2025 to 3 hrs. Two AnimatedLine components for Phase 1 and Phase 2. Phase 2 has label "Cost to Generate". Confirmed in renders. (CodeCostChart.tsx:177-194)

11. **Line 2 pre-fork (Immediate Cost to Patch baseline)**: Amber #D9944A, solid, strokeWidth 4. Flat at 10 hrs from 2015-2020. Confirmed in frame 1200 render. (CodeCostChart.tsx:196-203)

12. **Line 2 fork -- Small codebase path**: Amber #D9944A, solid, strokeWidth 3, bright. Drops from 10 hrs (2020) to 1.5 hrs (2025). Label "Small Codebase". Confirmed in frames 2100+. (CodeCostChart.tsx:205-213)

13. **Line 2 fork -- Large codebase path**: Amber #D9944A, solid, strokeWidth 2, lineOpacity 0.7 (dimmer/thinner). Stays flat at 10-12 hrs. Label "Large Codebase". Confirmed visually as a thinner, dimmer amber line. (CodeCostChart.tsx:215-224)

14. **Tech debt shaded area**: Two AnimatedArea components rendering the area between the immediate cost and total cost lines. Phase 1 uses baseline vs total (2015-2020), Phase 2 uses large codebase immediate vs total (2020-2025). Fill color matches 30% opacity amber spec. Confirmed in renders as a prominent amber-tinted region. (CodeCostChart.tsx:159-175)

15. **Line 3 (Total Cost of Patching, dashed)**: Amber #D9944A, dashed=true, strokeWidth 3. Rises from 22 hrs (2015) to 33 hrs (2025). Label "True Cost (with tech debt)". Dashed line clearly visible at top of shaded area in renders. (CodeCostChart.tsx:226-247)

16. **"Same tools. Different codebase sizes." annotation**: Appears at frame 1800 (DRAW_LINE_MID + 300) during Phase 2. White text on dark background overlay. Fades out before EMPHASIS_START. Confirmed in frame 2100 render. (CodeCostChart.tsx:249-270)

17. **Curved arrow "Every patch adds code"**: SVG curved arrow from small codebase (~3 hrs at year 2023.5) to large codebase (~11 hrs at year 2023.5). Uses cubic bezier curve with arrowhead marker. Appears at frame 2100 (DRAW_LINE_MID + 600) with 60-frame fade-in. Label "Every patch adds code". Confirmed visually in frame 2900 and 3150 renders. (CodeCostChart.tsx:105-108, 272-318)

18. **VISUAL 9 -- First annotation beat (frames 2700-3060)**: Correctly displays both annotations in a centered overlay:
    - "Individual task: -55% (GitHub, 2022)" with fine print "95 developers, one greenfield task" (CodeCostChart.tsx:456-469)
    - "Overall throughput: ~0% (Uplevel, 2024)" with fine print "785 developers, one year" (CodeCostChart.tsx:478-492)
    - Fades in over 30 frames. Visible only between EMPHASIS_START (2700) and EMPHASIS_MID (3060).
    - All text matches spec lines 80-84 exactly. Confirmed in frame 2900 render.

19. **VISUAL 10 -- Second annotation beat (frames 3060-3240)**: Correctly displays both annotations:
    - "Code churn: +44% (GitClear, 2025, 211M lines analyzed)" (CodeCostChart.tsx:521)
    - "Refactoring: -60%" (CodeCostChart.tsx:532)
    - Visible between EMPHASIS_MID (3060) and CROSSING_START (3240).
    - Matches spec lines 87-89. Confirmed in frame 3150 render.

20. **Crossing point annotation (frames 3240-3600)**: Shows:
    - "Generate: 3 hrs vs Large CB Total: 33 hrs" with colored spans (CodeCostChart.tsx:562-564)
    - Sub-label: "Patching wins... if you stay small. But patching makes you grow." (CodeCostChart.tsx:576)
    - "We are here." in italic Georgia serif (CodeCostChart.tsx:588)
    - Matches spec lines 92-96. Confirmed in frame 3400 render.

21. **Legend**: Four entries matching all chart lines: Cost to Generate (solid blue), Patch Small CB (solid amber, 3px), Patch Large CB (solid amber, 2px, 0.7 opacity), True Cost with tech debt (dashed amber). Visible in rendered frames 2900+. (CodeCostChart.tsx:320-429)

22. **S01-Economics integration**: CodeCostChart is used at Visual 3 (frame offset -540, showing the morph transition point) and Visual 5 (frame offset -1800, showing Phase 2). CodeCostChartMini is used at Visual 6 (frame offset -938). (Part1Economics.tsx:63-94)

23. **AnimatedLine drawing mechanics**: Multi-point path drawing with segment-based progress calculation. Tip-tracking dot (radius 8) appears during drawing and disappears when complete. Labels appear at line endpoint when drawing is done. (AnimatedLine.tsx:56-188)

24. **AnimatedArea mechanics**: Correctly interpolates between top and bottom data boundaries using sample points at 2-year intervals. Progressively reveals from left to right. (AnimatedArea.tsx:28-123)

25. **CodeCostChartMini -- all previously reported issues resolved**:
    - Citation now correctly reads "Individual task: -55% (GitHub, 2022)" (CodeCostChartMini.tsx:662)
    - Fine print context present: "95 developers, one greenfield task" and "785 developers, one year" (CodeCostChartMini.tsx:664-671)
    - Extra "Bug rate: +41%" annotation removed
    - Crossing point text matches spec: "Patching wins... if you stay small. But patching makes you grow." (CodeCostChartMini.tsx:721)
    - "Same tools. Different codebase sizes." annotation present (CodeCostChartMini.tsx:501-522)
    - Curved arrow "Every patch adds code" present (CodeCostChartMini.tsx:524-570)
    - VISUAL 10 second annotation beat present with "Code churn: +44% (GitClear, 2025, 211M lines analyzed)" and "Refactoring: -60%" (CodeCostChartMini.tsx:676-698)
    - "We are here." text present in crossing point (CodeCostChartMini.tsx:723-724)

---

### Accepted Deviations (unchanged from prior audit)

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 1 | Morph transition is cross-fade, not a true visual morph of SockChart | Medium | ACCEPTED -- cross-fade is visually adequate; no SockChart component is rendered or morphed from |
| 2 | X-axis year ticks are [2015, 2020, 2022, 2025] instead of spec's individual years 2020-2025 | Low | ACCEPTED -- key years shown for readability |
| 3 | Line drawing easing uses `Easing.inOut(Easing.cubic)` instead of spec's `easeOutQuad` | Low | ACCEPTED -- minimal perceptible visual difference |
| 4 | Large codebase fork strokeWidth is 2 instead of spec's 1.5 | Low | ACCEPTED -- minimal visual difference |
| 5 | Y-axis range 0-35 instead of spec's 0-100 | Low | ACCEPTED -- better fit for actual data range (max 33 hrs) |
| 6 | Annotations positioned as centered overlays, not pointing at specific chart elements | Low | ACCEPTED -- consistent overlay style works well for readability |
| 7 | CodeCostChartMini delays dashed line reveal to Section 3 instead of drawing during Phase 1 | Low-Medium | ACCEPTED -- deliberate narrative choice for the condensed format, creates a dramatic reveal moment |

---

### Notes

- There are three separate implementations of the code cost chart data, each serving a different role in the final composition:
  1. **CodeCostChart (05-CodeCostChart/)**: The primary 120-second animated chart with morph transition, two-phase line drawing, annotations, and crossing point. Most spec-compliant. Used at Visuals 3 and 5 in Part1Economics.
  2. **CodeCostChartMini (05a-CodeCostChartMini/)**: A 68-second condensed variant with its own audio track and an alternative narrative structure featuring a dramatic "dashed line reveal." Used at Visual 6. All annotation content now matches the spec.
  3. **CrossingPoint's CodeCostChart (08-CrossingPoint/CodeCostChart.tsx)**: A static (non-animated) chart rendering used as the background for the crossing point composition. Used at Visuals 7-9, 15-17, 20.

- All three chart implementations share the same data values from the spec (defined in 05-CodeCostChart/constants.ts and duplicated in 08-CrossingPoint/constants.ts).

- The AnimatedLine component includes a tip-tracking dot (radius 8) that appears during drawing and disappears upon completion -- a nice visual touch consistent with the 3Blue1Brown style.

- The background uses a subtle gradient from #1a1a2e to #0f0f1a, an enhancement over the spec's flat #1a1a2e.

- Rendered stills at frames 20, 600, 1200, 2100, 2900, 3150, and 3400 all confirm correct visual output: chart axes, line positions, colors, annotations, tech debt shaded area, curved arrow, and crossing point text are all properly rendered.
