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

## Requirements Met

### Canvas and Resolution
1. **Resolution 1920x1080**: `INVESTMENT_TABLE_WIDTH = 1920`, `INVESTMENT_TABLE_HEIGHT = 1080` (`constants.ts` lines 8-9). Match.

2. **Background color #1a1a2e**: `COLORS.BACKGROUND = "#1a1a2e"` (`constants.ts` line 34), applied via `AbsoluteFill` at `InvestmentTable.tsx` line 214. Match.

3. **Table centered horizontally and vertically**: Table container uses `position: "absolute"`, `left: "50%"`, `top: "50%"`, `transform: "translate(-50%, -50%)"`, `width: 1200` (`InvestmentTable.tsx` lines 218-222). Match.

### Table Header Row
4. **Three columns with correct labels**: Headers render "Investment", "Return (Patching)", "Return (PDD)" (`InvestmentTable.tsx` lines 244, 255, 265). Match.

5. **Header background #252545**: `COLORS.HEADER_BG = "#252545"` (`constants.ts` line 35), applied at `InvestmentTable.tsx` line 236. Match.

6. **Header text: white, bold, 26pt, sans-serif**: `headerCellStyle` at lines 12-20 specifies `fontSize: 26`, `fontWeight: "bold"`, `fontFamily: "system-ui, sans-serif"`, `color: COLORS.LABEL_WHITE` (which is `"#ffffff"`). Match.

7. **Column widths 25% | 37.5% | 37.5%**: Set via inline `width` properties: `"25%"` (line 242), `"37.5%"` (line 250), `"37.5%"` (line 261). Match.

8. **Amber underline on "Return (Patching)"**: `borderBottom: '3px solid ${COLORS.PATCHING_AMBER}'` where `PATCHING_AMBER = "#D9944A"` (`InvestmentTable.tsx` line 251, `constants.ts` line 38). Match.

9. **Blue underline on "Return (PDD)"**: `borderBottom: '3px solid ${COLORS.PDD_BLUE}'` where `PDD_BLUE = "#4A90D9"` (`InvestmentTable.tsx` line 262, `constants.ts` line 39). Match.

### Row Content
10. **Row 1 content**: `"Fix bug"` | `"One place, once"` | `"Impossible forever"` (`constants.ts` lines 48-50). Match.

11. **Row 2 content**: `"Improve code"` | `"One version"` | `"All future versions"` (`constants.ts` lines 53-55). Match.

12. **Row 3 content**: `"Document behavior"` | `"One snapshot"` | `"Living specification"` (`constants.ts` lines 58-60). Match.

### Cell Text Colors and Typography
13. **Investment column: white at 90% opacity**: `color: 'rgba(255, 255, 255, 0.9)'` (`InvestmentTable.tsx` line 77). Match.

14. **Patching column: amber (#D9944A) at 80% opacity**: `color: 'rgba(217, 148, 74, 0.8)'` (`InvestmentTable.tsx` line 90). RGB values 217,148,74 correspond to #D9944A. Match.

15. **PDD column: blue (#4A90D9) at 80% opacity**: `color: 'rgba(74, 144, 217, 0.8)'` (`InvestmentTable.tsx` line 102). RGB values 74,144,217 correspond to #4A90D9. Match.

16. **Cell text: 24pt, sans-serif**: `bodyCellStyle` at lines 22-28 specifies `fontSize: 24`, `fontFamily: "system-ui, sans-serif"`. Match.

17. **PDD column fontWeight 600**: Applied at `InvestmentTable.tsx` line 103. Match.

### Row Background Alternation
18. **Row 1 and Row 3 dark (#1E1E2E)**: `COLORS.ROW_DARK = "#1E1E2E"` (`constants.ts` line 36). Applied when `rowIndex % 2 === 0` at `InvestmentTable.tsx` line 54 (rowIndex 0 and 2). Match.

19. **Row 2 lighter (#222242)**: `COLORS.ROW_ALT = "#222242"` (`constants.ts` line 37). Applied when `rowIndex % 2 !== 0` (rowIndex 1). Match.

### Table Border Styling
20. **Thin borders between cells: rgba(255, 255, 255, 0.15)**: `COLORS.BORDER = "rgba(255, 255, 255, 0.15)"` (`constants.ts` line 41). Used in `headerCellStyle` borderBottom (line 19), `bodyCellStyle` borderBottom (line 27), and inline patching column borderLeft/borderRight (lines 91-92). Match.

21. **Outer border: rgba(255, 255, 255, 0.25)**: `COLORS.BORDER_OUTER = "rgba(255, 255, 255, 0.25)"` (`constants.ts` line 42). Applied to the table at `InvestmentTable.tsx` line 232. Match.

22. **8px border-radius**: `borderRadius: 8` on the table element (`InvestmentTable.tsx` line 230). Match.

23. **borderCollapse: separate with borderSpacing: 0**: Applied at lines 228-229 for proper border-radius rendering. Match.

### Animation Timing (Internal BEATS)
24. **Table fade-in frames 0-45**: `BEATS.TABLE_FADE_START = 0`, `BEATS.TABLE_FADE_END = 45` (`constants.ts` lines 14-15). At 30fps this is 0-1.5s. Match.

25. **Row 1 slide-in frames 45-120**: `BEATS.ROW1_START = 45`, `BEATS.ROW1_END = 120` (`constants.ts` lines 17-18). Matches spec code example (lines 139). Match.

26. **Row 2 slide-in frames 150-225**: `BEATS.ROW2_START = 150`, `BEATS.ROW2_END = 225` (`constants.ts` lines 20-21). Matches spec code example (line 140). Match.

27. **Row 3 slide-in frames 270-345**: `BEATS.ROW3_START = 270`, `BEATS.ROW3_END = 345` (`constants.ts` lines 23-24). Matches spec code example (line 141). Match.

28. **Column-wide pulse frames 390-450**: `BEATS.PULSE_START = 390`, `BEATS.PULSE_END = 450` (`constants.ts` lines 26-27). Matches spec code example (lines 149-152). Match.

29. **Hold phase starts at frame 480**: `BEATS.HOLD_START = 480` (`constants.ts` line 29). Match.

30. **Duration 20 seconds / 600 frames at 30fps**: `INVESTMENT_TABLE_DURATION_SECONDS = 20`, `INVESTMENT_TABLE_FPS = 30`, yielding 600 frames (`constants.ts` lines 4-7). Match.

### Animation Mechanics
31. **Table fade-in easing: easeOutCubic**: `Easing.out(Easing.cubic)` at `InvestmentTable.tsx` line 131. Match.

32. **Row slide-in: translateX -30px to 0 with opacity 0 to 1**: `slideX = interpolate(progress, [0, 1], [-30, 0])` at line 53, `opacity: progress` at line 68. Match.

33. **Row slide-in easing: easeOutCubic**: All three row interpolations use `easing: Easing.out(Easing.cubic)` (lines 142, 152, 162). Match.

34. **PDD cell glow: brief pulse per row, max 20% opacity**: Glow values interpolate [0, 1, 0] centered around each ROW_END. Applied as `pddGlow * 0.2` in backgroundColor (line 104). Match.

35. **Column-wide pulse easing: easeInOutQuad**: `Easing.inOut(Easing.quad)` at line 194. Match.

36. **Column pulse propagation by row position**: `pulsePosition = rowIndex / 3`, pulse is active when `columnPulseProgress > pulsePosition && < pulsePosition + 0.5`, intensity varies with distance (lines 57-63). Provides the top-to-bottom sweep effect. Match.

37. **Patching column remains static**: No glow, pulse, or animated background on the patching column `<td>` (lines 87-95). Only static color styling. Match.

38. **Ambient glow during hold phase**: Interpolates from `PULSE_END` to `HOLD_START` reaching 0.08 opacity (lines 199-207). Applied as a minimum baseline in the PDD cell's backgroundColor and boxShadow via `Math.max(pddGlow * 0.2, pulseIntensity, ambientGlow)` (line 104). Match.

### Component Architecture
39. **Clean exports via index.ts**: `InvestmentTable` component and all constants properly exported (`index.ts` lines 1-9). Match.

40. **Props schema with Zod**: `InvestmentTableProps` uses `z.object({ showTable: z.boolean().default(true) })` with exported type and defaults (`constants.ts` lines 65-74). Clean.

41. **Integration in Part5CompoundReturns**: InvestmentTable is imported and rendered as Visual 4 with `<InvestmentTable showTable />` within a `<Sequence from={BEATS.VISUAL_04_START}>` (`Part5CompoundReturns.tsx` lines 100-104). Match.

## Issues Found

### 1. Composition timing truncates most of the animation (HIGH)

- **Spec says**: ~20 seconds for the full investment table sequence including all 3 rows, column pulse, and hold phase (spec lines 5, 86-118).
- **Implementation does**: In `Part5CompoundReturns.tsx`, the InvestmentTable is Visual 4, active from `VISUAL_04_START = s2f(53.94) = frame 1618` until Visual 5 starts at `VISUAL_05_START = s2f(62.34) = frame 1870`. This gives the component only 252 internal frames (~8.4 seconds at 30fps).
- **What gets cut**: The component's internal BEATS require 600 frames (20 seconds) to complete:
  - Row 1: frames 45-120 (visible, within 8.4s window)
  - Row 2: frames 150-225 (visible, within 8.4s window)
  - Row 3: frames 270-345 (starts at 9s -- BEYOND the 8.4s window)
  - Column pulse: frames 390-450 (13-15s -- BEYOND the window)
  - Hold phase: frames 480-600 (16-20s -- BEYOND the window)
- **Impact**: Row 3 ("Document behavior" / "One snapshot" / "Living specification"), the column-wide blue pulse, and the ambient hold phase are never displayed in the Part5 composition. Approximately 60% of the intended animation is invisible. The third data row is arguably the most important for the "living specification" message.
- **Files**: `S05-CompoundReturns/constants.ts` lines 60-61; `47-InvestmentTable/constants.ts` lines 23-29.

### 2. Graph-to-table crossfade not implemented (MEDIUM)

- **Spec says**: "The compound curves graph fades to 0% opacity over 1.5 seconds. The table fades in from 0% simultaneously" (spec lines 22-24). The graph and table should dissolve into each other.
- **Implementation does**: `Part5CompoundReturns.tsx` uses an exclusive `activeVisual` switching pattern (lines 52-58) where only one visual is rendered at a time. Visual 3 (CompoundCurvesGraph phase 5) ends at `VISUAL_03_END = frame 1568` and Visual 4 (InvestmentTable) begins at `VISUAL_04_START = frame 1618`. There is a 50-frame (~1.67s) gap between them, and no simultaneous rendering occurs.
- **Impact**: The transition is an abrupt cut (with a brief blank frame gap) rather than the smooth crossfade dissolve described in the spec. The atmospheric continuity between the mathematical graph and the summary table is lost. The spec's `graphOpacity` interpolation (spec lines 127-130) has no counterpart in the implementation.
- **Files**: `Part5CompoundReturns.tsx` lines 52-58, 93-104.

### 3. PDD glow pulses use linear interpolation instead of easeInOutQuad (LOW)

- **Spec says**: PDD cell glow should use `easeInOutQuad` easing for smooth pulse (spec line 282).
- **Implementation does**: The `pddGlow1/2/3` interpolations at `InvestmentTable.tsx` lines 167-183 use three-keyframe interpolation with no `easing` option, defaulting to linear.
- **Impact**: The glow pulses ramp linearly rather than with the smooth acceleration/deceleration of easeInOutQuad. The visual difference is subtle since the pulse is brief and at low opacity (20%), but the spec calls for a specific smooth feel.
- **Files**: `InvestmentTable.tsx` lines 167-183.

### 4. Graph fade-out easing not applied (LOW)

- **Spec says**: Graph dissolve should use `easeInQuad` (spec line 279).
- **Implementation does**: No graph fade-out is implemented within the InvestmentTable component. The spec's reference code includes a `graphOpacity` interpolation (spec lines 127-130) that should drive the graph's opacity from 1 to 0 over frames 0-45. Since the crossfade itself is not implemented (Issue 2), this easing has no surface to apply to.
- **Impact**: Dependent on Issue 2 being resolved. If a crossfade were added, the `easeInQuad` easing should be applied to the graph's outgoing opacity.
- **Files**: `InvestmentTable.tsx` (missing graphOpacity interpolation); `Part5CompoundReturns.tsx` (no crossfade rendering).

## Notes

- The InvestmentTable component itself is well-constructed and faithful to the spec when viewed in standalone mode. All colors, typography, timing constants, animation mechanics, row content, glow effects, column pulse, and ambient hold glow match the specification precisely.

- The critical issue is at the orchestration level: the `Part5CompoundReturns` composition only allocates ~8.4 seconds of screen time to the InvestmentTable, but the component's internal BEATS require the full 20 seconds. This means the third row, the column pulse, and the hold phase are never visible.

- To resolve Issue 1, there are two paths:
  - **(a) Compress internal BEATS**: Remap the InvestmentTable's timing constants to fit within ~8.4 seconds (252 frames). This would require shortening row animation gaps and reading pauses, but would preserve narration sync in Part5.
  - **(b) Extend allocation**: Adjust `VISUAL_04_END` and `VISUAL_05_START` in the Part5 constants to give the InvestmentTable more time. This would require re-syncing downstream visuals (grandmother callback, developer callback, CrossingPoint) with narration, which may not be feasible since those are driven by Whisper word timestamps.
  - Option (a) is more practical given the narration-driven beat structure. The narration lines "Every investment in the mold has compound returns. Every investment in patching has diminishing returns." span ~53.94s to ~62.34s (~8.4 seconds), which is the natural window for this visual.

- The `activeVisual` switching pattern in `Part5CompoundReturns.tsx` (lines 52-58) only renders one visual at a time. This architectural choice fundamentally prevents crossfade transitions between any adjacent visuals. Resolving Issue 2 would require rendering both the outgoing and incoming visuals simultaneously during a brief overlap window, or restructuring the visual switching approach.

- The InvestmentTable component includes `overflow: "hidden"` on the table (line 231), which correctly ensures the rounded border-radius clips cell content at corners.

- Column border separation is handled consistently: the patching column has explicit `borderLeft` and `borderRight` (lines 91-92, 252-253), while the investment and PDD columns rely on the header's bottom border and the cell bottom borders for visual separation. This produces clean vertical dividers.

## Resolution Status: UNRESOLVED
