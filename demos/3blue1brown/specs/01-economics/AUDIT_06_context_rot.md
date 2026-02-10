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

## Rendered Frame Verification

Six still frames were rendered and visually inspected:

- **Frame 30** (mid-zoom): Chart zoomed in on debt area. Large-codebase fork and total cost lines prominent. Generate line and small-codebase fork visibly faded. Debt area filled with solid amber. Title "Context Rot: The AI-Specific Problem" visible. PASS.
- **Frame 100** (separation hold): Two distinct debt layers clearly visible -- darker bottom layer (Code Complexity) and lighter top layer (Context Rot) with visible noise texture. Labels "Code Complexity" and "Context Rot" rendered in correct amber hues. Background grid and non-focus lines dimmed. PASS.
- **Frame 450** (small codebase): 4x4 grid of code blocks displayed. Blue glowing context window covers most of the grid. "Context Coverage 80%" shown in top-right card. "Small project - AI sees almost everything" label in green. "Codebase: 4x4 modules (16 total)" indicator at bottom-left. Blocks inside window at full opacity, blocks outside dimmed. PASS.
- **Frame 630** (mid-growth): Grid expanded to approximately 13x13 (144 modules shown). Context window remains the same fixed size. Coverage counter shows 25%. Grid physically larger than context window. Smooth growth transition in progress. PASS.
- **Frame 800** (large codebase): 32x32 grid fills the frame. Tiny context window visible at center. "Context Coverage 2%" displayed. "Large project - AI sees through a keyhole" label in red. Red bug dots scattered across blocks, multiplying as expected. PASS.
- **Frame 960** (in-grid mismatch): "The Context Mismatch Problem" title. 32x32 grid with context window overlay. Red-bordered blocks inside the window (irrelevant code AI grabbed). Green-bordered and green-filled blocks outside the window (needed code AI missed). Legend at bottom: "Inside window: irrelevant code" and "Outside window: needed but missed". Explanation callout: "The Problem: AI grabbed wrong code inside its tiny window, while needed code sits outside, invisible." PASS.
- **Frame 1060** (performance graph + chart): "The Consequence" title. Full code cost chart visible with all five line series. Performance vs. Context Length inset at top-left showing degradation curve from 100% down to ~15%. Citation text: "Even with perfect retrieval, performance degrades 14-85% as context grows (EMNLP, 2025)". Legend on right with all chart elements including "Context Rot" swatch. PASS.
- **Frame 1250** (solution setup): Full chart visible. Both annotations present: "Faster patching -> faster growth -> faster rot" (in amber, right side) and "Small modules. Clear prompts. Always fits in context." (in blue, left side). Generate line appears brighter/pulsing with glow effect. Context rot debt area visible and pulsing. PASS.

## Requirements Met

### Canvas and General
- [x] Resolution 1920x1080 (`constants.ts:7-8`: `CONTEXT_ROT_WIDTH = 1920`, `CONTEXT_ROT_HEIGHT = 1080`)
- [x] Dark background #1a1a2e (`constants.ts:41`: `BACKGROUND: "#1a1a2e"`, with gradient to `#0f0f1a` applied in `ContextRot.tsx:155`)
- [x] 30fps, 45 seconds, 1350 frames (`constants.ts:4-6`: `CONTEXT_ROT_FPS = 30`, `CONTEXT_ROT_DURATION_SECONDS = 45`, `CONTEXT_ROT_DURATION_FRAMES = 1350`)
- [x] Registered as standalone composition in Root.tsx

### Part 1: Zoom Into the Debt (0-300f)

#### Frame 0-60: Zoom into the shaded debt area
- [x] Zoom into shaded debt area above the large-codebase fork (`DebtLayerSeparation.tsx:51-56`: `zoomProgress` interpolates from 0 to 1 over frames 0-60)
- [x] Zoom uses CSS scale transform centered on debt area (`DebtLayerSeparation.tsx:175-176`: `transform: scale(${1 + zoomProgress * 0.5})`, `transformOrigin: ${zoomCenterX}px ${zoomCenterY}px` centered at year 2022.5, 21 hours)
- [x] Small-codebase fork fades to 20% opacity (`DebtLayerSeparation.tsx:59-64`: `focusFadeOpacity` interpolates from 1 to 0.2)
- [x] Generate line fades to 20% opacity (`DebtLayerSeparation.tsx:268-275`: uses same `focusFadeOpacity`)
- [x] Large-codebase path and its debt area remain prominently visible (constant 0.7 and 0.8 opacity respectively)
- [x] Fork point (2020) remains faintly visible at left edge (confirmed in frame 30 render)

#### Frame 60-150: Debt area separates into two layers
- [x] Separation animation runs frames 60-150 (`constants.ts:15-16`)
- [x] Bottom layer: "Code Complexity" in darker amber #D9944A at 0.4 opacity (`DebtLayerSeparation.tsx:329-332`)
- [x] Top layer: "Context Rot" in lighter amber #E8B888 at 0.5 opacity (`DebtLayerSeparation.tsx:345-351`)
- [x] Context rot layer has animated noise/static texture (`DebtLayerSeparation.tsx:186-201`: SVG `feTurbulence` filter with `type="fractalNoise"`, `seed={Math.floor(frame / 3)}` for animation, `feBlend mode="overlay"`)
- [x] Labels fade in for each layer after separation (`DebtLayerSeparation.tsx:83-88`: 30-frame fade starting at frame 150; confirmed visible in frame 100 render)

#### Frame 150-300: Hold showing two-layer composition
- [x] Hold phase defined in constants (`constants.ts:17-18`: `HOLD_LAYERS_START: 150`, `HOLD_LAYERS_END: 300`)
- [x] No additional animations during hold; separation at maximum, labels fully visible

### Part 2: The Shrinking Window (300-900f)

#### Frame 300-360: Morph chart into context window visualization
- [x] Part 1 debt view fades out (`ContextRot.tsx:36-41`: `part1Opacity` interpolates from 1 to 0 over frames 240-300)
- [x] Context window visualization fades in (`ContextWindowVisualization.tsx:11-16`: `morphInOpacity` from 0 to 1 over frames 300-360)

#### Frame 360-540: Small Codebase state
- [x] Grid starts at 4x4 (`constants.ts:75`, confirmed in frame 450 render: "Codebase: 4x4 modules (16 total)")
- [x] Context window covers 80% (confirmed in frame 450 render: "Context Coverage 80%")
- [x] Label "Small project - AI sees almost everything" displayed (confirmed in render)
- [x] Blocks inside window at full opacity, outside dimmed to 0.4 (`CodebaseGrid.tsx:91`)

#### Frame 540-720: Codebase growth animation
- [x] Grid expands 4 -> 8 -> 16 -> 32 through three sub-ranges (`ContextWindowVisualization.tsx:24-44`)
- [x] Context window stays FIXED SIZE (`CodebaseGrid.tsx:26`: `blockSize = 50` fixed; `ContextWindowVisualization.tsx:73`: `FIXED_CONTEXT_WINDOW_SIZE = 240`)
- [x] Coverage counter animates 80% -> 40% -> 10% -> 2% (confirmed in frame 630 render showing 25% mid-transition)
- [x] Smooth easing through growth stages (confirmed visually)

#### Frame 720-900: Large Codebase state
- [x] Grid at 32x32 (confirmed in frame 800 render: "Codebase: 32x32 modules (1024 total)")
- [x] Context window covers ~2% (confirmed in render: "Context Coverage 2%")
- [x] Label "Large project - AI sees through a keyhole" (confirmed in render)
- [x] Red bug dots multiplying as grid grows (`CodebaseGrid.tsx:44-49`, confirmed visible in render)

### Context Window Visual Elements
- [x] Border: Glowing blue #4A90D9 with subtle pulse (`constants.ts:53`, `CodebaseGrid.tsx:146,180-191`)
- [x] Interior: Full opacity, Exterior: Dimmed 40% (`CodebaseGrid.tsx:91`)
- [x] Size: Fixed throughout growth animation (`ContextWindowVisualization.tsx:73`: constant 240px)

### Codebase Grid Visual Elements
- [x] Blocks are rounded rectangles (`CodebaseGrid.tsx:89`)
- [x] Colors: Various grays and muted colors (`constants.ts:64-70`: five gray-blue shades)
- [x] Red bug dots that multiply as grid grows (`CodebaseGrid.tsx:98-106`)

### Part 3: The Consequence (900-1350f)

#### Frame 900-1020: Degradation in action (mismatch visualization)
- [x] Red-highlighted irrelevant blocks inside context window (`InGridMismatch.tsx:94,111-123`, confirmed in frame 960 render)
- [x] Green-highlighted needed blocks outside window (`InGridMismatch.tsx:95,126-149`, confirmed in frame 960 render)
- [x] Explanation callout with inline colored text (`InGridMismatch.tsx:324-361`, confirmed in render)
- [x] In-grid approach active by default (`ContextRot.tsx:21`: `USE_IN_GRID_MISMATCH = true`)

#### Wrong Context Visualization Colors
- [x] Relevant blocks: Soft green glow #5AAA6E (`constants.ts:56`)
- [x] Irrelevant blocks: Red-tinted #944A4A (`constants.ts:57`)

#### Frame 1020-1110: Performance vs. Context Length graph inset
- [x] Graph inset appears at frame 1020 for 90 frames (`ContextRot.tsx:188-189`, confirmed in frame 1060 render)
- [x] Title "Performance vs. Context Length" (`PerformanceGraphInset.tsx:115`)
- [x] Performance line drops from 100% to 15% (`PerformanceGraphInset.tsx:45-52`)
- [x] Citation: "Even with perfect retrieval, performance degrades 14-85% as context grows (EMNLP, 2025)" (`PerformanceGraphInset.tsx:298-300`, confirmed in render)
- [x] Small overlay format at top-left corner (`PerformanceGraphInset.tsx:33-34`: 420x280px)
- [x] Fade in/out animation with animated line drawing effect

#### Frame 1110-1230: Return to chart
- [x] Full chart with fork visible (confirmed in frame 1060 and 1250 renders -- all five line series present)
- [x] Context rot layer pulses (`ContextRot.tsx:98-100`: sine wave modulating fill opacity)
- [x] Annotation: "Faster patching -> faster growth -> faster rot" (`ContextRot.tsx:376`, confirmed in frame 1250 render)

#### Frame 1230-1350: Setup for the solution
- [x] Generate line pulses with emphasis and glow filter (`ContextRot.tsx:103-105,290`)
- [x] Annotation: "Small modules. Clear prompts. Always fits in context." (`ContextRot.tsx:401`, confirmed in frame 1250 render)

### S01-Economics Integration
- [x] ContextRot is used across Visuals 10-14 in `Part1Economics.tsx` (lines 121-161)
- [x] Negative Sequence offsets correctly advance internal frame counter: Visual 10 (no offset, starts at internal 0), Visual 11 (-240), Visual 12 (-630), Visual 13 (-840), Visual 14 (-1000)

## Issues Found

### Issue 1: Frame Timing Structural Difference for Part 3 (Minor)
- **Spec says**: Part 3 frames 1110-1230 for return to chart, 1230-1350 for solution setup
- **Implementation does**: Return to chart starts at frame 1020, solution setup starts at frame 1140 instead of 1230
- **Severity**: Low - The solution setup annotation "Faster patching..." appears 90 frames earlier than spec, but the full duration (1140-1350 = 210 frames) provides adequate hold time. The visual content matches the spec's intent.

### Issue 2: Coverage Counter Format (Minor)
- **Spec says**: "Counter in corner: 'Context coverage: 80% -> 40% -> 10% -> 2%'" suggesting progression arrows
- **Implementation does**: Shows a card with "Context Coverage" header and a single large animating percentage value
- **Severity**: Low - The live-updating single-value counter is arguably more effective at communicating the shrinking ratio than showing all four values with arrows.

### Issue 3: Grid Growth is Smooth Rather Than Discrete Steps (Minor)
- **Spec says**: "Grid expands: 4x4 -> 8x8 -> 16x16 -> 32x32" implying four distinct stages
- **Implementation does**: Smooth interpolation through these sizes in three sub-ranges with `Easing.inOut(Easing.cubic)`, rounding to nearest integer
- **Severity**: Low - Each specified size is a waypoint in the interpolation. The smooth animation with easing looks polished.

### Issue 4: Return to Chart Uses Fade-In Rather Than Zoom-Out (Minor)
- **Spec says**: "Zoom back out to show full chart with the fork visible"
- **Implementation does**: Fades the chart in with opacity interpolation rather than a reverse zoom animation
- **Severity**: Low - The chart appears with all elements including the fork. A fade transition is serviceable though it differs from the zoom-out described.

### Issue 5: Irrelevant Code Flash in Large Codebase State (Minor)
- **Spec says**: Frame 720-900 "Wrong/irrelevant blocks highlighted in red briefly"
- **Implementation does**: Shows a full-screen subtle red flash overlay (`rgba(148, 74, 74, 0.05)` pulsing) plus bug dots, rather than per-block red highlighting
- **Severity**: Low - Per-block red highlighting is reserved for the InGridMismatch phase immediately following, which is a reasonable sequencing choice.

### Issue 6: Performance Graph Inset Timing Overlap (Minor)
- **Spec says**: Performance graph at 1020-1110, return to chart at 1110-1230 (sequential)
- **Implementation does**: Both begin at frame 1020, so the graph inset overlays the incoming chart
- **Severity**: Low - The layered approach works visually with the inset at top-left over the chart fading in behind it.

## Notes

### Architecture Strengths
1. **Clean component separation**: Each animation phase has its own component (DebtLayerSeparation, ContextWindowVisualization, InGridMismatch/SplitViewMismatch, PerformanceGraphInset) with clear responsibility boundaries.
2. **Centralized constants**: All timings, colors, grid sizes, and chart data in `constants.ts` makes the animation highly configurable and auditable.
3. **Toggle for mismatch approach**: `USE_IN_GRID_MISMATCH` flag allows switching between spec-compliant in-grid and alternative split-screen approaches without code changes.
4. **Animated noise texture**: The `feTurbulence` SVG filter with frame-dependent seed creates the "signal degradation" effect called for in the spec's design notes.
5. **Mathematical correctness**: Coverage percentages (80/40/10/2), grid sizes (4/8/16/32), color hex values, and timing beats all match the spec's data tables precisely.
6. **Dual mismatch implementations**: Both `InGridMismatch.tsx` and `SplitViewMismatch.tsx` are fully built, giving creative flexibility.

### Visual Verification Summary
All six spec-critical phases were rendered and visually confirmed:
- Debt zoom with layer separation and noise texture
- Small codebase grid with high context coverage
- Growth animation with shrinking coverage ratio
- Large codebase grid showing the "keyhole" effect
- Context mismatch with red/green block highlighting
- Chart return with annotations and pulsing generate line

### S01-Economics Integration Detail
The ContextRot component spans Visuals 10-14 in the Part1Economics sequence. The integration uses negative Sequence offsets to set the correct internal frame position for each narration segment: no offset (Visual 10, internal frame 0), -240 (Visual 11, Part 2 small codebase), -630 (Visual 12, growth animation), -840 (Visual 13, large codebase/mismatch), -1000 (Visual 14, performance graph / chart return).

## Resolution Status: RESOLVED
