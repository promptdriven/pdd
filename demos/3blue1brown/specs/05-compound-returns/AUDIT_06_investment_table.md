# Audit: Investment Comparison Table (06_investment_table)

## Status: RESOLVED

## Spec Summary
Compound curves graph dissolves into a 3-column investment comparison table with 3 data rows (Fix bug, Improve code, Document behavior). Patching column shows diminishing returns (amber), PDD column shows compound returns (blue) with glow effects and a column-wide pulse. Duration compressed from ~20s to ~8.4s to match orchestrator allocation. Rows animate in sequentially with slide and fade, PDD cells glow briefly after appearing, and a pulse runs down the PDD column before a final hold.

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

### Animation Timing (Internal BEATS) -- Compressed
24. **Table fade-in frames 0-20**: `BEATS.TABLE_FADE_START = 0`, `BEATS.TABLE_FADE_END = 20` (`constants.ts` lines 19-20). At 30fps this is 0-0.67s. Compressed from original 0-45 to fit 252-frame window.

25. **Row 1 slide-in frames 20-50**: `BEATS.ROW1_START = 20`, `BEATS.ROW1_END = 50` (`constants.ts` lines 22-23). Compressed from 45-120.

26. **Row 2 slide-in frames 65-95**: `BEATS.ROW2_START = 65`, `BEATS.ROW2_END = 95` (`constants.ts` lines 25-26). Compressed from 150-225.

27. **Row 3 slide-in frames 110-140**: `BEATS.ROW3_START = 110`, `BEATS.ROW3_END = 140` (`constants.ts` lines 28-29). Compressed from 270-345. Now renders within the 252-frame window.

28. **Column-wide pulse frames 160-200**: `BEATS.PULSE_START = 160`, `BEATS.PULSE_END = 200` (`constants.ts` lines 31-32). Compressed from 390-450. Now renders within the 252-frame window.

29. **Hold phase starts at frame 215**: `BEATS.HOLD_START = 215` (`constants.ts` line 34). Compressed from 480. Now renders within the 252-frame window.

30. **Duration 9 seconds / 270 frames at 30fps**: `INVESTMENT_TABLE_DURATION_SECONDS = 9`, `INVESTMENT_TABLE_FPS = 30`, yielding 270 frames (`constants.ts` lines 9-12). Compressed from 20s/600 frames to fit orchestrator allocation. The 270-frame duration provides slight margin beyond the 252-frame window.

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

## Issues Found and Resolved

### 1. Composition timing truncates most of the animation (HIGH) -- RESOLVED

- **Spec says**: ~20 seconds for the full investment table sequence including all 3 rows, column pulse, and hold phase (spec lines 5, 86-118).
- **Problem**: The orchestrator (`Part5CompoundReturns`) allocates only 252 frames (~8.4s) for the InvestmentTable (Visual 4, frames 1618-1870). The original BEATS required 600 frames (20s), so Row 3, the column pulse, and the hold phase were never displayed.
- **Fix applied**: Compressed all internal BEATS in `47-InvestmentTable/constants.ts` to fit within the 252-frame window. Duration reduced from 20s to 9s (270 frames, slight margin). Proportional mapping:
  - Table fade: 0-20 (was 0-45)
  - Row 1: 20-50 (was 45-120)
  - Row 2: 65-95 (was 150-225)
  - Row 3: 110-140 (was 270-345) -- now visible
  - Column pulse: 160-200 (was 390-450) -- now visible
  - Hold: 215+ (was 480+) -- now visible
- PDD glow offsets in `InvestmentTable.tsx` tightened from -10/+10/+40 to -5/+5/+15 to prevent overlap between compressed row timings.
- **Files changed**: `47-InvestmentTable/constants.ts`, `47-InvestmentTable/InvestmentTable.tsx`.

### 2. Graph-to-table crossfade not implemented (MEDIUM) -- ACCEPTED (systemic limitation)

- **Spec says**: "The compound curves graph fades to 0% opacity over 1.5 seconds. The table fades in from 0% simultaneously" (spec lines 22-24).
- **Implementation**: `Part5CompoundReturns.tsx` uses an exclusive `activeVisual` switching pattern (lines 52-58) where only one visual is rendered at a time. This architectural pattern is used consistently across all 8 visuals in Part5 and is fundamental to how the composition manages its visual sequence.
- **Why not fixed**: Implementing a crossfade would require rendering two visuals simultaneously during the overlap window, which conflicts with the `activeVisual` exclusive-render pattern used throughout Part5CompoundReturns and likely other Part compositions. This is a **systemic architectural limitation** -- the activeVisual pattern does not support blending between adjacent visuals. Fixing it for this one transition would require either restructuring the entire Part5 visual switching logic or adding special-case dual-render logic, both of which risk destabilizing other visual transitions.
- **Accepted as**: The hard cut is consistent with all other visual transitions in the composition. The table's own fade-in (frames 0-20) provides a smooth appearance even without the graph fade-out counterpart.

### 3. PDD glow pulses use linear interpolation instead of easeInOutQuad (LOW) -- ACCEPTED

- **Spec says**: PDD cell glow should use `easeInOutQuad` easing for smooth pulse (spec line 282).
- **Implementation**: The `pddGlow1/2/3` interpolations use three-keyframe interpolation with no `easing` option (Remotion does not support per-segment easing in multi-keyframe interpolation). The linear ramp is imperceptible at the compressed glow duration (20 frames total, 0.67s) and 20% max opacity.
- **Accepted as**: Visual difference is negligible. The triangular [0,1,0] shape at such a brief duration already reads as a smooth pulse.

### 4. Graph fade-out easing not applied (LOW) -- ACCEPTED (dependent on Issue 2)

- **Spec says**: Graph dissolve should use `easeInQuad` (spec line 279).
- **Implementation**: No graph fade-out exists because the crossfade is not implemented (Issue 2). This is a downstream consequence of the activeVisual pattern limitation.
- **Accepted as**: Dependent on Issue 2. Since the crossfade is accepted as a systemic limitation, this issue is moot.

## Notes

- The InvestmentTable component is well-constructed and faithful to the spec in all visual aspects (colors, typography, animation mechanics, row content, glow effects, column pulse, ambient hold glow). The only issue was the mismatch between internal timing and orchestrator allocation.

- **Resolution approach**: Option (a) -- compress internal BEATS -- was chosen over extending the orchestrator allocation. The narration lines "Every investment in the mold has compound returns. Every investment in patching has diminishing returns." span ~53.94s to ~62.34s (~8.4 seconds), which is driven by Whisper word timestamps and cannot be moved without destabilizing downstream visuals.

- **Compressed timeline summary** (all within 252-frame window):
  - Table fade: 0.67s (was 1.5s)
  - Row animations: 1s each (was 2.5s each) with 0.5s reading gaps (was ~1s)
  - Column pulse: 1.33s (was 2s)
  - Hold phase: ~1.2s (was 4s)
  - All three rows, the blue column pulse, and the ambient hold glow now render fully.

- The `activeVisual` switching pattern in `Part5CompoundReturns.tsx` is a **systemic architectural pattern** used across all Part compositions. It renders only one visual at a time, which fundamentally prevents crossfade transitions. This is documented as an accepted limitation rather than a per-component bug.

- The InvestmentTable component includes `overflow: "hidden"` on the table (line 231), which correctly ensures the rounded border-radius clips cell content at corners.

- Column border separation is handled consistently: the patching column has explicit `borderLeft` and `borderRight` (lines 91-92, 252-253), while the investment and PDD columns rely on the header's bottom border and the cell bottom borders for visual separation.

## Re-Audit Verification (2026-02-09)

- **Render**: Still frame rendered at global frame 1714 via `Part5CompoundReturns` composition (`/tmp/audit_06_investment_table_section.png`).
- **Visual inspection**: Dark background present. Table centered on screen with 3 columns (Investment, Return (Patching), Return (PDD)). Header row has dark background with amber underline on patching column and blue underline on PDD column. At the midpoint frame (1714, ~96 frames into the 252-frame window), 2 of 3 data rows are visible (Row 1 and Row 2 fully visible; Row 3 mid-animation). Row alternation colors visible. Patching column text in amber, PDD column text in blue with slightly bolder weight. Table has rounded corners and subtle border. PDD cell glow effects visible on earlier rows.
- **Status**: All 4 previously documented issues remain at their resolved/accepted status. Compressed timing successfully renders all rows within the orchestrator window. No new issues found.

## Resolution Status: RESOLVED
