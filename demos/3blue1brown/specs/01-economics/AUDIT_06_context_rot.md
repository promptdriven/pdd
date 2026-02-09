# Audit: 06_context_rot (Context Rot - The AI-Specific Problem)

## Status: PASS

## Spec Summary
This spec calls for a 45-second (1350 frame at 30fps) animation showing how context rot affects AI coding on large codebases. Three main parts:
1. **Part 1 (0-300f)**: Zoom into the debt area of the chart, separate it into two layers: "Code Complexity" (solid amber #D9944A) and "Context Rot" (lighter amber #E8B888 with animated noise texture)
2. **Part 2 (300-900f)**: Show a "context window" metaphor where a fixed-size window covers less and less of a growing codebase grid (4x4 -> 32x32), with coverage dropping from 80% -> 2%
3. **Part 3 (900-1350f)**: Show the mismatch (red irrelevant inside window, green needed outside), display a performance graph inset with EMNLP citation, return to chart with context rot pulsing, end with generate line pulsing

## Implementation Files
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/ContextRot.tsx` - Main orchestrator
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/DebtLayerSeparation.tsx` - Part 1: debt zoom and layer split
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/ContextWindowVisualization.tsx` - Part 2: shrinking context window
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/CodebaseGrid.tsx` - Grid rendering with context window overlay
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/InGridMismatch.tsx` - Part 2b: in-grid red/green mismatch (active)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/SplitViewMismatch.tsx` - Alt split-screen mismatch (inactive, toggle available)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/PerformanceGraphInset.tsx` - Performance vs Context Length graph overlay
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/constants.ts` - Timing, colors, grid config, chart data
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/index.ts` - Barrel exports
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S01-Economics/Part1Economics.tsx` - Integration into full sequence (Visuals 10-14)

## Requirements Met

### Canvas and General
- [x] Resolution 1920x1080 (constants.ts:7-8: `CONTEXT_ROT_WIDTH = 1920`, `CONTEXT_ROT_HEIGHT = 1080`)
- [x] Dark background #1a1a2e (constants.ts:41: `BACKGROUND: "#1a1a2e"`, with gradient to #0f0f1a)
- [x] 30fps, 45 seconds, 1350 frames (constants.ts:4-6)

### Part 1: Zoom Into the Debt (0-300f)
- [x] Zoom into shaded debt area above large-codebase fork (DebtLayerSeparation.tsx:51-56: zoomProgress 0-60 frames, scale 1.0->1.5x)
- [x] Small-codebase fork and generate line fade to 20% opacity (DebtLayerSeparation.tsx:59-64: `focusFadeOpacity` interpolates to 0.2)
- [x] Large-codebase path stays visible (DebtLayerSeparation.tsx:297-305: opacity stays at 0.7)
- [x] Fork point (2020) remains visible at left edge as anchor (zoom center is at 2022.5 so 2020 remains visible)
- [x] Debt area separates into two layers at frames 60-150 (DebtLayerSeparation.tsx:75-80: `LAYER_SEPARATION_START: 60`, `LAYER_SEPARATION_END: 150`)
- [x] Bottom layer "Code Complexity" in darker amber #D9944A at 40% opacity (DebtLayerSeparation.tsx:330-332, constants.ts:49)
- [x] Top layer "Context Rot" in lighter amber #E8B888 with animated noise texture (DebtLayerSeparation.tsx:345-351, constants.ts:50, feTurbulence filter at lines 186-201)
- [x] Labels fade in for each layer (DebtLayerSeparation.tsx:83-88: labelOpacity after separation end, labels at lines 366-410)
- [x] Hold showing two-layer composition frames 150-300 (constants.ts:17-18: `HOLD_LAYERS_START: 150`, `HOLD_LAYERS_END: 300`)

### Part 2: The Shrinking Window (300-900f)
- [x] Transition to context window metaphor at frame 300 (ContextWindowVisualization.tsx:11-16: morphInOpacity from 300-360)
- [x] Context window with glowing blue border #4A90D9 and subtle pulse (CodebaseGrid.tsx:146, 180-191, constants.ts:53)
- [x] Small codebase state (360-540f): 4x4 grid with ~80% coverage (constants.ts:23-24, GRID_CONFIG.SMALL_SIZE: 4, CONTEXT_COVERAGE.SMALL: 80)
- [x] Label "Small project - AI sees almost everything" (ContextWindowVisualization.tsx:81-82)
- [x] Grid growth animation (540-720f): 4 -> 8 -> 16 -> 32 (ContextWindowVisualization.tsx:24-44, GRID_CONFIG sizes match)
- [x] Context window stays FIXED SIZE throughout (CodebaseGrid.tsx:26 blockSize=50 fixed; ContextWindowVisualization.tsx:73 FIXED_CONTEXT_WINDOW_SIZE=240)
- [x] Coverage counter: 80% -> 40% -> 10% -> 2% (ContextWindowVisualization.tsx:48-67; constants.ts:84-88 coverage values match spec exactly)
- [x] Large codebase state (720-900f): 32x32 grid with ~2% coverage (constants.ts:27-28)
- [x] Label "Large project - AI sees through a keyhole" (ContextWindowVisualization.tsx:83-84)
- [x] Interior blocks at full opacity, exterior at 40% opacity (CodebaseGrid.tsx:91: `opacity={inContext ? 1 : 0.4}`)
- [x] Codebase grid uses rounded rectangles (CodebaseGrid.tsx:89: `rx={Math.min(GRID_CONFIG.BLOCK_RADIUS, blockSize / 4)}`)
- [x] Bug dots (red) multiply as grid grows (CodebaseGrid.tsx:44-49, 98-106)

### Part 3: The Consequence (900-1350f)
- [x] Red irrelevant blocks inside context window, green needed blocks outside (InGridMismatch.tsx:93-95, active via `USE_IN_GRID_MISMATCH = true` in ContextRot.tsx:21)
- [x] Performance vs Context Length graph inset (PerformanceGraphInset.tsx, rendered at ContextRot.tsx:188-189 frames 1020 to 1020+90)
- [x] Graph shows performance degradation curve dropping from 100% to 15% (PerformanceGraphInset.tsx:45-52)
- [x] Citation text: "Even with perfect retrieval, performance degrades 14-85% as context grows (EMNLP, 2025)" (PerformanceGraphInset.tsx:298-300)
- [x] Graph is a small overlay inset, not a full chart transition (PerformanceGraphInset.tsx: 420x280px positioned at top-left)
- [x] Return to chart with fork visible at frame 1020 (ContextRot.tsx:176-518 renders full chart SVG with all fork lines)
- [x] Context rot layer pulses in returned chart (ContextRot.tsx:98-100: `contextRotPulse` via sine wave)
- [x] Annotation "Faster patching -> faster growth -> faster rot" (ContextRot.tsx:376)
- [x] Generate line pulses with emphasis (ContextRot.tsx:103-105: `generateLinePulse`, filter applied at line 290)
- [x] Solution annotation "Small modules. Clear prompts. Always fits in context." (ContextRot.tsx:401)

### Color Spec Compliance
- [x] Code Complexity layer: #D9944A at 40% opacity (constants.ts:49, DebtLayerSeparation.tsx:332)
- [x] Context Rot layer: #E8B888 with animated noise (constants.ts:50, DebtLayerSeparation.tsx:348)
- [x] Context window border: #4A90D9 with pulse (constants.ts:53, CodebaseGrid.tsx:187-188)
- [x] Relevant code: #5AAA6E soft green (constants.ts:56)
- [x] Irrelevant code: #944A4A red tint (constants.ts:57)

### Integration into S01-Economics
- [x] ContextRot is used across Visuals 10-14 in Part1Economics.tsx (lines 117-157)
- [x] Negative Sequence offsets correctly advance the internal frame counter for each visual segment (-240, -630, -870, -1350)
- [x] Registered in Root.tsx as standalone composition (id="ContextRot")

## Issues Found

### Issue 1: Frame Timing Structural Difference (Minor)
- **Spec says**: Part 3 "Consequence" is one unified section (frames 900-1350) containing mismatch, graph inset, return to chart, and solution setup as sub-sequences
- **Implementation does**: Splits into Part 2b "InGridMismatch" (900-1020) and Part 3 "Return to Chart" (1020-1350) as two distinct rendering phases
- **Severity**: Low - Functionally equivalent. The content and timing of each sub-element match the spec. The structural split is an implementation detail that does not affect the visual output.

### Issue 2: Coverage Counter Format (Minor)
- **Spec says**: "Counter in corner: 'Context coverage: 80% -> 40% -> 10% -> 2%'" suggesting the progression arrows
- **Implementation does**: Shows a coverage card with "Context Coverage" header and a large current percentage value that smoothly animates (ContextWindowVisualization.tsx:167-190)
- **Severity**: Low - The counter accurately displays the current coverage percentage. The spec's arrow notation was likely describing the intended range, not a literal display format. The live-updating counter is arguably more effective.

### Issue 3: Grid Growth is Smooth Rather Than Discrete Steps (Minor)
- **Spec says**: "Grid expands: 4x4 -> 8x8 -> 16x16 -> 32x32" implying distinct stages
- **Implementation does**: Smooth interpolation through these sizes in three sub-ranges (ContextWindowVisualization.tsx:32-44) using `Easing.inOut(Easing.cubic)`
- **Severity**: Low - The implementation passes through all four spec sizes. The smooth animation looks more polished than abrupt jumps. Each size is used as a keyframe in the interpolation.

### Issue 4: Return to Chart Uses Fade-In Rather Than Zoom-Out (Minor)
- **Spec says**: "Frame 1110-1230: Zoom back out to show full chart with the fork visible"
- **Implementation does**: Fades the chart in with opacity interpolation (ContextRot.tsx:50-55: `part3ChartOpacity`) rather than a reverse zoom animation
- **Severity**: Low - The chart appears with all elements including the fork. A fade transition is common and serviceable, though not the zoom-out described.

### Issue 5: Irrelevant Code Flash in Large Codebase State (Minor)
- **Spec says**: Frame 720-900 "Visual: Wrong/irrelevant blocks highlighted in red briefly"
- **Implementation does**: Shows a full-screen subtle red flash overlay (ContextWindowVisualization.tsx:260-272, `rgba(148, 74, 74, 0.05)` pulsing) plus bug indicators (red dots) on individual blocks
- **Severity**: Low - The implementation signals "something is wrong" through the screen-level flash and bug dots. Individual block-level red highlighting is reserved for the InGridMismatch phase immediately following, which is a reasonable sequencing choice.

## Notes

### Previous Audit Resolutions Verified
The prior audit identified two critical deltas that have been resolved:
1. **Performance Graph Inset** - Now fully implemented in `PerformanceGraphInset.tsx`. Confirmed: shows performance degradation curve, correct citation text, correct frame timing (1020 to 1020+90), small overlay format, animated line drawing, fade in/out transitions.
2. **In-Grid Mismatch Visualization** - Now fully implemented in `InGridMismatch.tsx`. Confirmed: red stroke highlights on irrelevant blocks inside the context window, green stroke/fill highlights on relevant blocks outside the window, maintains visual continuity with the grid metaphor. Toggled active via `USE_IN_GRID_MISMATCH = true`.

### Architecture Strengths
1. **Clean component separation**: Each animation phase is its own component (DebtLayerSeparation, ContextWindowVisualization, InGridMismatch/SplitViewMismatch, PerformanceGraphInset)
2. **Centralized constants**: All timings, colors, grid sizes, and chart data in constants.ts makes the animation highly configurable
3. **Toggle for mismatch approach**: `USE_IN_GRID_MISMATCH` flag allows switching between spec-compliant in-grid and alternative split-screen approaches
4. **Animated noise texture**: The feTurbulence SVG filter with frame-dependent seed (DebtLayerSeparation.tsx:191) creates the "signal degradation" effect called for in the spec's design notes
5. **Mathematical correctness**: Coverage percentages (80/40/10/2), grid sizes (4/8/16/32), color values, and timing beats all match the spec's data tables precisely

### S01-Economics Integration
The ContextRot component spans Visuals 10-14 in the Part1Economics sequence. The integration uses negative Sequence offsets to set the correct internal frame position for each narration segment, allowing the single ContextRot component to serve multiple visual beats without duplicating state.
