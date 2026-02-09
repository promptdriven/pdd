# Audit: Investment Comparison Table (06_investment_table)

## Status: ISSUES FOUND

## Spec Summary
Compound curves graph dissolves into a 3-column investment comparison table with 3 data rows (Fix bug, Improve code, Document behavior). Patching column shows diminishing returns (amber), PDD column shows compound returns (blue) with glow effects and a column-wide pulse. Duration ~20 seconds. Rows animate in sequentially with slide and fade, PDD cells glow briefly after appearing, and a pulse runs down the PDD column before a final hold.

## Implementation Files
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/47-InvestmentTable/InvestmentTable.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/47-InvestmentTable/constants.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/47-InvestmentTable/index.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S05-CompoundReturns/Part5CompoundReturns.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S05-CompoundReturns/constants.ts`

### Requirements Met

1. **Canvas and resolution**: 1920x1080, dark background #1a1a2e. Constants match exactly (INVESTMENT_TABLE_WIDTH=1920, INVESTMENT_TABLE_HEIGHT=1080, COLORS.BACKGROUND="#1a1a2e").

2. **Table structure**: Three columns with correct widths -- Investment 25%, Return(Patching) 37.5%, Return(PDD) 37.5%. Header widths set inline at lines 242, 250, 261 of InvestmentTable.tsx.

3. **Table centering**: Table is absolutely positioned at left 50%, top 50% with translate(-50%, -50%), width 1200px. Matches spec requirement for horizontal and vertical centering.

4. **Row content**: All three rows match spec exactly:
   - Row 1: "Fix bug" | "One place, once" | "Impossible forever"
   - Row 2: "Improve code" | "One version" | "All future versions"
   - Row 3: "Document behavior" | "One snapshot" | "Living specification"
   Content defined in TABLE_ROWS constant (constants.ts lines 46-62).

5. **Header styling**: Bold, 26pt, system-ui sans-serif, white text, background #252545. All match (headerCellStyle lines 12-20, COLORS.HEADER_BG="#252545").

6. **Header underlines**: "Return (Patching)" has 3px solid amber (#D9944A) underline, "Return (PDD)" has 3px solid blue (#4A90D9) underline. Implemented via borderBottom on header cells (lines 251, 262).

7. **Cell text colors**: Investment column white at 90% opacity, Patching amber at 80%, PDD blue at 80%. Implementation: rgba(255,255,255,0.9), rgba(217,148,74,0.8), rgba(74,144,217,0.8) at lines 77, 90, 102. Exact match.

8. **PDD text weight**: Spec says fontWeight 600. Implementation line 103: fontWeight 600. Match.

9. **Row background alternation**: Row 1/3 dark (#1E1E2E), Row 2 lighter (#222242). Implementation alternates via rowIndex % 2 using COLORS.ROW_DARK and COLORS.ROW_ALT with correct hex values.

10. **Table border styling**: Thin borders rgba(255,255,255,0.15) between cells, outer border rgba(255,255,255,0.25), 8px border-radius, borderCollapse separate. All match via COLORS.BORDER, COLORS.BORDER_OUTER, and table style properties.

11. **Table fade-in**: Fades from 0 to 1 opacity over frames 0-45 (1.5s at 30fps) with easeOutCubic easing. Constants: TABLE_FADE_START=0, TABLE_FADE_END=45. Easing: Easing.out(Easing.cubic). Match.

12. **Row slide-in animation**: Each row slides in from translateX -30px to 0 with opacity 0 to 1. Implementation line 53: interpolate(progress, [0, 1], [-30, 0]). Line 68: opacity set to progress. Match.

13. **Row animation timing (internal)**: ROW1_START=45, ROW1_END=120; ROW2_START=150, ROW2_END=225; ROW3_START=270, ROW3_END=345. These match the spec's code example exactly (spec lines 139-141).

14. **Row easing**: Spec says easeOutCubic for row slide-in. Implementation uses Easing.out(Easing.cubic) on all three rows (lines 142, 152, 162). Match.

15. **PDD cell glow**: Brief blue glow pulse after each row appears. Glow intensity maxes at pddGlow * 0.2 = 20% opacity. Pulse timing centered around ROW_END for each row. Match with spec.

16. **PDD cell glow rendering**: Background color uses rgba(74, 144, 217, ...) with max of glow, pulse, and ambient. Box shadow provides inset glow effect. Correctly implemented.

17. **Column-wide pulse**: Frames 390-450 (spec code example uses 390-450; section heading says 390-480). Implementation PULSE_START=390, PULSE_END=450. Easing: Easing.inOut(Easing.quad). Pulse propagates through rows based on rowIndex/3 position with distance-based intensity. Match with spec code example.

18. **Patching column static**: Amber column has no glow, no pulse, no background animation. Only static color styling. Correctly implements the "diminishing returns = no energy" contrast.

19. **Ambient glow on PDD column during hold**: Implemented as interpolation from PULSE_END to HOLD_START, fading to 0.08 (8% opacity). Provides subtle persistent glow during final hold phase.

20. **Duration constants**: INVESTMENT_TABLE_DURATION_SECONDS=20, FPS=30, total 600 frames. Match.

### Issues Found

1. **Composition timing truncates most of the animation (HIGH)**
   - **Spec says**: ~20 seconds for the full investment table sequence including all 3 rows, column pulse, and hold phase (spec lines 5, 86-119).
   - **Implementation does**: In Part5CompoundReturns.tsx, the InvestmentTable (Visual 4) is only active from VISUAL_04_START=s2f(53.94)=frame 1618 to when Visual 5 starts at VISUAL_05_START=s2f(62.34)=frame 1870. This gives only 252 internal frames (~8.4 seconds). Row 3 starts at internal frame 270 (9 seconds), the column pulse at frame 390 (13 seconds), and hold at frame 480 (16 seconds) -- all beyond the 8.4-second window available.
   - **Impact**: Row 3 ("Document behavior" / "One snapshot" / "Living specification"), the column-wide pulse, and the hold phase are never displayed in the Part5 composition. Only Row 1 and Row 2 are visible. This cuts roughly 60% of the intended animation.

2. **Graph-to-table crossfade not implemented (MEDIUM)**
   - **Spec says**: "The compound curves graph fades to 0% opacity over 1.5 seconds. The table fades in from 0% simultaneously" (spec lines 22-23). The graph and table should dissolve into each other.
   - **Implementation does**: Part5CompoundReturns.tsx uses a hard visual cut via `activeVisual` switching. Visual 3 (CompoundCurvesGraph phase 5) ends at frame 1568 and Visual 4 (InvestmentTable) starts at frame 1618, with a 50-frame gap between them. There is no simultaneous rendering or crossfade.
   - **Impact**: The transition between the graph and table is an abrupt cut rather than the smooth dissolve described in the spec. The spec's atmospheric transition effect is lost.

3. **PDD glow missing easing (LOW)**
   - **Spec says**: PDD cell glow should use easeInOutQuad easing for smooth pulse (spec line 282).
   - **Implementation does**: The pddGlow interpolations (lines 167-183 of InvestmentTable.tsx) use default linear interpolation with no easing option specified.
   - **Impact**: The glow pulses are linear rather than having the smooth acceleration/deceleration of easeInOutQuad. Visual difference is subtle.

4. **Graph fade-out easing not applied (LOW)**
   - **Spec says**: Graph dissolve should use easeInQuad (spec line 279).
   - **Implementation does**: No graph fade-out is implemented within the InvestmentTable component. The graph fade-out would need to be handled at the composition level, where it is currently a hard cut instead.
   - **Impact**: Dependent on Issue 2 being resolved first. If a crossfade were added, the easeInQuad easing should be applied to the graph's opacity.

### Notes

- The InvestmentTable component itself is well-implemented and faithful to the spec when viewed in isolation. All colors, typography, animation mechanics, row content, timing constants, and visual effects match the spec precisely.
- The critical issue is at the orchestration level: the Part5CompoundReturns composition only gives the InvestmentTable ~8.4 seconds of screen time, but the component's internal animation requires the full 20 seconds to complete. This means Row 3, the column-wide pulse, and the hold phase are never seen.
- To resolve Issue 1, either: (a) extend the InvestmentTable's allocation in Part5 by adjusting VISUAL_04_END and VISUAL_05_START timing, or (b) compress the InvestmentTable's internal BEATS to fit within the available ~8.4 second window. Option (b) would require significant changes to the row animation timing but would preserve the Part5 narration sync.
- Issue 2 (crossfade) could be addressed by rendering both CompoundCurvesGraph and InvestmentTable simultaneously during a transition window, rather than using the exclusive `activeVisual` switching pattern.
- The `activeVisual` pattern in Part5CompoundReturns.tsx only renders one visual at a time, which fundamentally prevents crossfade transitions between any adjacent visuals.
