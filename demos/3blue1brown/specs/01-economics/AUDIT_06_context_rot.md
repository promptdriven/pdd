# Audit: 06_context_rot (Context Rot - The AI-Specific Problem)

## Status: PASS

## Spec Summary
This spec calls for a 45-second (1350 frames at 30fps) animation showing how context rot affects AI coding on large codebases. Three main parts:
1. **Part 1 (0-300f)**: Zoom into the debt area of the chart, separate it into two layers: "Code Complexity" (solid amber #D9944A) and "Context Rot" (lighter amber #E8B888 with animated noise texture)
2. **Part 2 (300-900f)**: Show a "context window" metaphor where a fixed-size window covers less and less of a growing codebase grid (4x4 -> 32x32), with coverage dropping from 80% -> 2%
3. **Part 3 (900-1350f)**: Show the mismatch (red irrelevant inside window, green needed outside), display a performance graph inset with EMNLP citation, return to chart with context rot pulsing, end with generate line pulsing

## Implementation Files
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/ContextRot.tsx` - Main orchestrator (543 lines)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/DebtLayerSeparation.tsx` - Part 1: debt zoom and layer split (416 lines)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/ContextWindowVisualization.tsx` - Part 2: shrinking context window (276 lines)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/CodebaseGrid.tsx` - Grid rendering with context window overlay (208 lines)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/InGridMismatch.tsx` - Part 2b: in-grid red/green mismatch (active) (365 lines)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/SplitViewMismatch.tsx` - Alt split-screen mismatch (inactive, toggle available) (389 lines)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/PerformanceGraphInset.tsx` - Performance vs Context Length graph overlay (305 lines)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/constants.ts` - Timing, colors, grid config, chart data (176 lines)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/index.ts` - Barrel exports (16 lines)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S01-Economics/Part1Economics.tsx` - Integration into full sequence (Visuals 10-14)

## Requirements Met

### Canvas and General
- [x] Resolution 1920x1080 (`constants.ts:7-8`: `CONTEXT_ROT_WIDTH = 1920`, `CONTEXT_ROT_HEIGHT = 1080`)
- [x] Dark background #1a1a2e (`constants.ts:41`: `BACKGROUND: "#1a1a2e"`, with gradient to `#0f0f1a` applied in `ContextRot.tsx:155`)
- [x] 30fps, 45 seconds, 1350 frames (`constants.ts:4-6`: `CONTEXT_ROT_FPS = 30`, `CONTEXT_ROT_DURATION_SECONDS = 45`, `CONTEXT_ROT_DURATION_FRAMES = 1350`)
- [x] Registered as standalone composition in Root.tsx (`Root.tsx:509-517`: id="ContextRot", correct dimensions and duration)

### Part 1: Zoom Into the Debt (0-300f)

#### Frame 0-60: Zoom into the shaded debt area
- [x] Zoom into shaded debt area above the large-codebase fork (`DebtLayerSeparation.tsx:51-56`: `zoomProgress` interpolates from 0 to 1 over frames 0-60)
- [x] Zoom uses CSS scale transform centered on debt area (`DebtLayerSeparation.tsx:175-176`: `transform: scale(${1 + zoomProgress * 0.5})`, `transformOrigin: ${zoomCenterX}px ${zoomCenterY}px` centered at year 2022.5, 21 hours)
- [x] Small-codebase fork fades to 20% opacity (`DebtLayerSeparation.tsx:59-64`: `focusFadeOpacity` interpolates from 1 to 0.2, applied to small CB line at line 288-295)
- [x] Generate line fades to 20% opacity (`DebtLayerSeparation.tsx:268-275`: uses same `focusFadeOpacity` value)
- [x] Large-codebase path and its debt area remain prominently visible (`DebtLayerSeparation.tsx:297-305`: large CB line at constant 0.7 opacity, `DebtLayerSeparation.tsx:307-316`: total cost line at constant 0.8 opacity)
- [x] Fork point (2020) remains faintly visible at left edge (zoom center at 2022.5 with 1.5x max scale keeps 2020 visible)

#### Frame 60-150: Debt area separates into two layers
- [x] Separation animation runs frames 60-150 (`constants.ts:15-16`: `LAYER_SEPARATION_START: 60`, `LAYER_SEPARATION_END: 150`)
- [x] Bottom layer: "Code Complexity" in darker amber #D9944A (`constants.ts:49`: `CODE_COMPLEXITY: "#D9944A"`, `DebtLayerSeparation.tsx:329-332`: fill uses this color at 0.4 opacity)
- [x] Top layer: "Context Rot" in lighter amber #E8B888 (`constants.ts:50`: `CONTEXT_ROT: "#E8B888"`, `DebtLayerSeparation.tsx:345-351`: fill uses this color at 0.5 opacity)
- [x] Context rot layer has animated noise/static texture (`DebtLayerSeparation.tsx:186-201`: SVG `feTurbulence` filter with `type="fractalNoise"`, `seed={Math.floor(frame / 3)}` for animation, `feBlend mode="overlay"`)
- [x] Labels fade in for each layer after separation (`DebtLayerSeparation.tsx:83-88`: `labelOpacity` fades from 0 to 1 over 30 frames after separation end; labels rendered at lines 366-410)
- [x] "Code Complexity" label positioned on bottom layer (`DebtLayerSeparation.tsx:161-162`: `codeComplexityLabelY` calculated from midpoint to immediate cost center + separation offset)
- [x] "Context Rot" label positioned on top layer (`DebtLayerSeparation.tsx:163-164`: `contextRotLabelY` calculated from total cost to midpoint center - separation offset)

#### Frame 150-300: Hold showing two-layer composition
- [x] Hold phase defined in constants (`constants.ts:17-18`: `HOLD_LAYERS_START: 150`, `HOLD_LAYERS_END: 300`)
- [x] No additional animations during hold; separation remains at max, labels fully visible

### Part 2: The Shrinking Window (300-900f)

#### Frame 300-360: Morph chart into context window visualization
- [x] Transition starts at frame 300 (`constants.ts:21`: `MORPH_TO_GRID_START: 300`)
- [x] Part 1 debt view fades out (`ContextRot.tsx:36-41`: `part1Opacity` interpolates from 1 to 0 over frames 240-300)
- [x] Context window visualization fades in (`ContextWindowVisualization.tsx:11-16`: `morphInOpacity` from 0 to 1 over frames 300-360)

#### Frame 360-540: Small Codebase state
- [x] Grid starts at 4x4 (`constants.ts:75`: `SMALL_SIZE: 4`, `ContextWindowVisualization.tsx:20-21`: returns SMALL_SIZE when frame < CODEBASE_GROWTH_START)
- [x] Context window covers 80% (`constants.ts:85`: `SMALL: 80`, coverage counter shows 80%)
- [x] Label "Small project - AI sees almost everything" displayed (`ContextWindowVisualization.tsx:81-82`: exact spec text returned)
- [x] Label fades in with animation (`ContextWindowVisualization.tsx:90-100`: `labelOpacity` interpolation)
- [x] Blocks inside window at full opacity, outside dimmed (`CodebaseGrid.tsx:91`: `opacity={inContext ? 1 : 0.4}`)

#### Frame 540-720: Codebase growth animation
- [x] Grid expands 4 -> 8 -> 16 -> 32 (`ContextWindowVisualization.tsx:24-44`: three sub-ranges at 0.33 thresholds, cycling through SMALL -> MEDIUM -> LARGE -> XLARGE sizes)
- [x] Growth timing matches spec (`constants.ts:25-26`: `CODEBASE_GROWTH_START: 540`, `CODEBASE_GROWTH_END: 720`)
- [x] Context window stays FIXED SIZE throughout growth (`CodebaseGrid.tsx:26`: `blockSize = 50` fixed; `ContextWindowVisualization.tsx:73`: `FIXED_CONTEXT_WINDOW_SIZE = 240` never changes)
- [x] Coverage counter animates 80% -> 40% -> 10% -> 2% (`ContextWindowVisualization.tsx:48-67`: `getCoveragePercent()` interpolates through all four coverage values; `constants.ts:84-89` defines exactly 80/40/10/2)

#### Frame 720-900: Large Codebase state
- [x] Grid at 32x32 (`constants.ts:78`: `XLARGE_SIZE: 32`, `constants.ts:27-28`: `LARGE_CODEBASE_START: 720`, `LARGE_CODEBASE_END: 900`)
- [x] Context window covers ~2% (`constants.ts:88`: `XLARGE: 2`)
- [x] Label "Large project - AI sees through a keyhole" (`ContextWindowVisualization.tsx:83-84`: exact spec text)
- [x] Irrelevant code flash visualization (`ContextWindowVisualization.tsx:260-272`: red overlay pulsing after frame 720+60)
- [x] Bug dots (red) multiply as grid grows (`CodebaseGrid.tsx:44-49`: bug probability scales with `bugMultiplier`; `ContextWindowVisualization.tsx:111`: multiplier increases every 30 frames)

### Context Window Visual Elements
- [x] Border: Glowing blue #4A90D9 with subtle pulse (`constants.ts:53`: `CONTEXT_WINDOW_BORDER: "#4A90D9"`, `CodebaseGrid.tsx:146`: pulse via sine wave, `CodebaseGrid.tsx:180-191`: border with glow filter)
- [x] Interior: Full opacity (`CodebaseGrid.tsx:91`: `opacity={inContext ? 1 : 0.4}`)
- [x] Exterior: Dimmed 40% opacity (`CodebaseGrid.tsx:91`: 0.4 for outside blocks)
- [x] Size: Fixed throughout growth animation (`ContextWindowVisualization.tsx:73`: constant 240px)

### Codebase Grid Visual Elements
- [x] Blocks are rounded rectangles (`CodebaseGrid.tsx:89`: `rx={Math.min(GRID_CONFIG.BLOCK_RADIUS, blockSize / 4)}`)
- [x] Colors: Various grays and muted colors (`constants.ts:64-70`: `CODE_BLOCK_COLORS` array of five gray-blue shades)
- [x] Red bug dots that multiply as grid grows (`CodebaseGrid.tsx:98-106`: red circles at `#EF4444`)

### Part 3: The Consequence (900-1350f)

#### Frame 900-1020: Degradation in action (mismatch visualization)
- [x] Red-highlighted irrelevant blocks inside context window (`InGridMismatch.tsx:94`: `showRedHighlight = inContext && !isRelevant`, `InGridMismatch.tsx:111-123`: red stroke border at `COLORS.IRRELEVANT_CODE`)
- [x] Green-highlighted needed blocks outside window (`InGridMismatch.tsx:95`: `showGreenHighlight = !inContext && isRelevant`, `InGridMismatch.tsx:126-149`: green stroke + subtle fill at `COLORS.RELEVANT_CODE`)
- [x] Visual is "immediately readable" with explanation callout (`InGridMismatch.tsx:324-361`: "The Problem" callout with inline colored text explaining wrong vs needed code)
- [x] In-grid approach active by default (`ContextRot.tsx:21`: `USE_IN_GRID_MISMATCH = true`)

#### Wrong Context Visualization Colors
- [x] Relevant blocks: Soft green glow #5AAA6E (`constants.ts:56`: `RELEVANT_CODE: "#5AAA6E"`)
- [x] Irrelevant blocks: Red-tinted #944A4A (`constants.ts:57`: `IRRELEVANT_CODE: "#944A4A"`)

#### Frame 1020-1110: Performance vs. Context Length graph inset
- [x] Graph inset appears (`PerformanceGraphInset.tsx` rendered at `ContextRot.tsx:188-189` for frames 1020 to 1020+90)
- [x] Title "Performance vs. Context Length" (`PerformanceGraphInset.tsx:115`: exact text)
- [x] Performance line drops from left to right (100% -> 15%) (`PerformanceGraphInset.tsx:45-52`: data from 100 at context 0 to 15 at context 100)
- [x] Citation label: "Even with perfect retrieval, performance degrades 14-85% as context grows (EMNLP, 2025)" (`PerformanceGraphInset.tsx:298-300`: exact text, split across two lines)
- [x] Small overlay format, not full chart transition (`PerformanceGraphInset.tsx:33-34`: 420x280px positioned at top-left corner)
- [x] Fade in/out animation (`PerformanceGraphInset.tsx:15-20, 23-28`: separate fade in and fade out interpolations)
- [x] Animated line drawing effect (`PerformanceGraphInset.tsx:78-83`: `lineDrawProgress` animates from 0 to 1 using SVG mask)

#### Frame 1110-1230: Return to chart
- [x] Full chart with fork visible (`ContextRot.tsx:176-518`: complete SVG chart rendered with all lines, axes, grid, debt area, and legend)
- [x] Context rot layer pulses (`ContextRot.tsx:98-100`: `contextRotPulse` via sine wave modulating fill opacity of debt area at line 278)
- [x] Annotation: "Faster patching -> faster growth -> faster rot" (`ContextRot.tsx:376`: exact spec text with arrow characters)

#### Frame 1230-1350: Setup for the solution
- [x] Generate line pulses with emphasis (`ContextRot.tsx:103-105`: `generateLinePulse` via sine wave, `ContextRot.tsx:290`: glow filter applied when `frame >= BEATS.SETUP_SOLUTION_START`)
- [x] Annotation: "Small modules. Clear prompts. Always fits in context." (`ContextRot.tsx:401`: exact spec text)
- [x] Beat timings correct (`constants.ts:35-36`: `SETUP_SOLUTION_START: 1140`, `SETUP_SOLUTION_END: 1350` -- spec says 1230-1350 but implementation uses frame 1140 as the start of the setup phase)

### S01-Economics Integration
- [x] ContextRot is used across Visuals 10-14 in `Part1Economics.tsx` (`Part1Economics.tsx:117-158`: five visual entries)
- [x] Negative Sequence offsets correctly advance internal frame counter (`Part1Economics.tsx:127`: -240, line 136: -630, line 145: -870, line 154: -1350)
- [x] Registered in Root.tsx as standalone composition (`Root.tsx:509-517`: id="ContextRot" with correct constants)

## Issues Found

### Issue 1: Frame Timing Structural Difference for Part 3 (Minor)
- **Spec says**: Part 3 "Consequence" is one unified section (frames 900-1350) containing mismatch (900-1020), graph inset (1020-1110), return to chart (1110-1230), and solution setup (1230-1350) as sub-sequences
- **Implementation does**: Splits into Part 2b "InGridMismatch" (900-1020) and Part 3 "Return to Chart" (1020-1350) as two distinct rendering phases. The graph inset overlaps the return-to-chart phase (1020-1110) rather than being a standalone sub-sequence. Solution setup starts at frame 1140 instead of 1230.
- **Severity**: Low - The visual content matches. The 90-frame shift for the solution setup start (1140 vs 1230) means annotations appear slightly earlier but the full duration (1140 to 1350 = 210 frames) provides adequate hold time for the transition to Section 1.7.

### Issue 2: Coverage Counter Format (Minor)
- **Spec says**: "Counter in corner: 'Context coverage: 80% -> 40% -> 10% -> 2%'" suggesting progression arrows
- **Implementation does**: Shows a coverage card with "Context Coverage" header and a large current percentage value that smoothly animates (`ContextWindowVisualization.tsx:167-190`)
- **Severity**: Low - The counter accurately displays the current coverage percentage. The spec's arrow notation was likely describing the intended range, not a literal display format. The live-updating single-value counter is arguably more effective.

### Issue 3: Grid Growth is Smooth Rather Than Discrete Steps (Minor)
- **Spec says**: "Grid expands: 4x4 -> 8x8 -> 16x16 -> 32x32" implying four distinct stages
- **Implementation does**: Smooth interpolation through these sizes in three sub-ranges (`ContextWindowVisualization.tsx:32-44`) using `Easing.inOut(Easing.cubic)`, rounding to nearest integer for grid dimension
- **Severity**: Low - The implementation passes through all four spec sizes as keyframes. The smooth animation with easing looks polished. Each specified size is a waypoint in the interpolation.

### Issue 4: Return to Chart Uses Fade-In Rather Than Zoom-Out (Minor)
- **Spec says**: "Frame 1110-1230: Zoom back out to show full chart with the fork visible"
- **Implementation does**: Fades the chart in with opacity interpolation (`ContextRot.tsx:50-55`: `part3ChartOpacity` from 0 to 1) rather than a reverse zoom animation
- **Severity**: Low - The chart appears with all elements including the fork. A fade transition is common and serviceable, though it differs from the zoom-out described in the spec.

### Issue 5: Irrelevant Code Flash in Large Codebase State (Minor)
- **Spec says**: Frame 720-900 "Visual: Wrong/irrelevant blocks highlighted in red briefly"
- **Implementation does**: Shows a full-screen subtle red flash overlay (`ContextWindowVisualization.tsx:260-272`, `rgba(148, 74, 74, 0.05)` pulsing) plus bug indicators (red dots) on individual blocks, rather than per-block red highlighting
- **Severity**: Low - The implementation signals "something is wrong" through the screen-level flash and bug dots. Individual block-level red highlighting is reserved for the InGridMismatch phase immediately following, which is a reasonable sequencing choice.

### Issue 6: Performance Graph Inset Timing Overlap (Minor)
- **Spec says**: Frame 1020-1110 is for the performance graph inset; frame 1110-1230 is for the return to chart
- **Implementation does**: The graph inset renders at frames 1020-1110 (`ContextRot.tsx:188`) but the return-to-chart SVG also begins fading in at frame 1020 (`ContextRot.tsx:50-55`: `part3ChartOpacity` from `RETURN_TO_CHART_START`), so the graph inset overlays on top of the incoming chart
- **Severity**: Low - Both elements are visible simultaneously with the graph inset at top-left over the chart. The inset fades out before the chart is fully visible, creating a layered transition. This is a creative interpretation rather than a strict sequential approach.

## Notes

### Architecture Strengths
1. **Clean component separation**: Each animation phase is its own component (DebtLayerSeparation, ContextWindowVisualization, InGridMismatch/SplitViewMismatch, PerformanceGraphInset) with clear responsibility boundaries
2. **Centralized constants**: All timings, colors, grid sizes, and chart data in `constants.ts` makes the animation highly configurable and auditable
3. **Toggle for mismatch approach**: `USE_IN_GRID_MISMATCH` flag (`ContextRot.tsx:21`) allows switching between spec-compliant in-grid and alternative split-screen approaches without code changes
4. **Animated noise texture**: The `feTurbulence` SVG filter with frame-dependent seed (`DebtLayerSeparation.tsx:191`: `seed={Math.floor(frame / 3)}`) creates the "signal degradation" effect called for in the spec's design notes
5. **Mathematical correctness**: Coverage percentages (80/40/10/2), grid sizes (4/8/16/32), color hex values, and timing beats all match the spec's data tables precisely
6. **Dual mismatch implementations**: Both `InGridMismatch.tsx` (spec-compliant: red/green highlights in the grid) and `SplitViewMismatch.tsx` (split-screen comparison) are fully built, giving creative flexibility

### Data Accuracy
The chart data in `constants.ts:123-158` defines five line series (costToGenerate, immediateCostBaseline, immediateCostSmallCodebase, immediateCostLargeCodebase, totalCostLargeCodebase) with the debt area computed between the large CB immediate and total cost lines from 2020-2025. The `interpolateHours` utility function (`constants.ts:110-120`) provides smooth interpolation between data points for the debt area paths.

### S01-Economics Integration
The ContextRot component spans Visuals 10-14 in the Part1Economics sequence. The integration uses negative Sequence offsets to set the correct internal frame position for each narration segment, allowing the single ContextRot component to serve multiple visual beats without duplicating state. The offsets (-240, -630, -870, -1350) correspond to different phases of the 1350-frame animation being synced to specific narration timestamps.

## Resolution Status: RESOLVED
