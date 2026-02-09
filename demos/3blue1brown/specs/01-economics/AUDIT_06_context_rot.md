# Audit: 06_context_rot.md

## Spec Summary
This spec calls for a 45-second (1350 frame) animation showing how context rot affects AI coding on large codebases. It has three main parts:
1. **Part 1 (0-300f)**: Zoom into the debt area of the chart and separate it into two layers: "Code Complexity" (solid amber) and "Context Rot" (lighter amber with animated noise texture)
2. **Part 2 (300-900f)**: Show a "context window" metaphor where a fixed-size window covers less and less of a growing codebase grid (4x4 → 32x32), with coverage dropping from 80% → 2%
3. **Part 3 (900-1350f)**: Show the mismatch between what AI sees vs what's needed, display a performance graph inset, return to chart with context rot pulsing, and end with the generate line pulsing

## Implementation Status
**Implemented** - The core functionality exists across multiple components in `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/`

## Deltas Found

### Delta 1: Frame Timing Discrepancy
- **Spec says**: Part 3 "Consequence" runs frames 900-1350 (450 frames)
- **Implementation does**: Part 2b "Split View Mismatch" runs frames 900-1020 (120 frames), then Part 3 "Return to Chart" runs frames 1020-1350 (330 frames)
- **Severity**: Medium
- **Files**: `ContextRot.tsx:25-27, 164-167`
- **Details**: The spec describes showing the context mismatch (red irrelevant inside, green needed outside) as part of the consequence section starting at frame 900. The implementation treats this as a separate "Split View" phase (900-1020) before returning to the chart. This is functionally similar but structurally different from the spec's three-part division.

### Delta 2: Performance Graph Inset Missing
- **Spec says**: "Frame 1020-1110 (34-37s): Performance vs. Context Length graph inset appears - A subtle graph inset appears with line dropping from left to right, labeled 'Even with perfect retrieval, performance degrades 14-85% as context grows (EMNLP, 2025)'"
- **Implementation does**: No performance graph inset is rendered
- **Severity**: High
- **Details**: The spec explicitly calls for a small overlay graph showing performance degradation with context length, with specific citation. This visual element is completely missing from the implementation.

### Delta 3: Context Window Stays Fixed BUT Grid Doesn't Expand Physically
- **Spec says**: "The context window staying the same size while the codebase grows is the 'aha moment.'" The spec implies the grid should grow physically larger on screen while the window stays fixed.
- **Implementation does**: The grid size changes (4→8→16→32) but the `blockSize` is fixed at 50px (CodebaseGrid.tsx:26), meaning the grid expands in total area. The context window size is also fixed at 240px (ContextWindowVisualization.tsx:73).
- **Severity**: Low
- **Details**: The implementation does show the intended effect (coverage shrinking), but the mechanism is slightly different. The spec's "aha moment" description suggests the grid should physically grow to fill more screen space while the window stays the same size. The implementation achieves the same conceptual goal (fixed window, growing codebase) but with both elements expanding proportionally.

### Delta 4: Split View Mismatch vs Spec's "Wrong Context" Visualization
- **Spec says**: Frame 900-1020 shows "Inside the tiny window: some blocks highlighted red — irrelevant code the AI grabbed. Outside the window: green-highlighted blocks showing code that was actually needed but couldn't be seen"
- **Implementation does**: Creates a completely new split-screen view (SplitViewMismatch.tsx) with two panels: "What AI sees" (left, mixed relevant/irrelevant) vs "What's Actually Needed" (right, all relevant)
- **Severity**: Medium
- **Files**: `SplitViewMismatch.tsx:1-389`
- **Details**: The spec describes highlighting blocks inside/outside the context window in the existing grid view. The implementation instead transitions to a new split-screen comparison view. This is a creative interpretation that may be more visually clear, but it's a significant departure from the spec's description.

### Delta 5: Layer Separation Mechanism
- **Spec says**: Debt area separates into two distinct layers with "Bottom layer (darker amber): 'Code Complexity' - traditional tech debt" and "Top layer (lighter amber with static/noise texture): 'Context Rot'"
- **Implementation does**: Uses `buildDebtHalfPath` to split the debt area into top and bottom halves with vertical separation offset, applying noise filter to top layer
- **Severity**: Low
- **Files**: `DebtLayerSeparation.tsx:111-145, 326-360`
- **Details**: Implementation correctly separates layers and applies noise texture to context rot. The physical separation (offset) is a good visual choice not explicitly in the spec but aligns with the intent.

### Delta 6: Missing "Irrelevant Code Flash" Detail
- **Spec says**: Frame 720-900 "Large Codebase state: Visual: Wrong/irrelevant blocks highlighted in red briefly"
- **Implementation does**: Shows bugs (red dots) multiplying as the grid grows, but no red flash highlighting of irrelevant blocks inside the context window
- **Severity**: Low
- **Files**: `CodebaseGrid.tsx:98-106, ContextWindowVisualization.tsx:113-116`
- **Details**: The implementation shows bug indicators appearing, but doesn't specifically flash red on "irrelevant" blocks that the AI grabbed. The red flash overlay (ContextWindowVisualization.tsx:260-272) is subtle and affects the whole screen, not individual blocks.

### Delta 7: Coverage Counter Display Format
- **Spec says**: "Counter in corner: 'Context coverage: 80% → 40% → 10% → 2%'" suggesting animated counting
- **Implementation does**: Shows a coverage counter with current percentage (ContextWindowVisualization.tsx:168-190), but displays as a static card showing only the current value
- **Severity**: Low
- **Details**: The counter shows the right data but doesn't show the "→" progression format suggested in the spec.

### Delta 8: Annotation Text Mismatch
- **Spec says**: Part 3 annotation reads "Faster patching → faster growth → faster rot"
- **Implementation does**: Identical text (ContextRot.tsx:366)
- **Severity**: None (Match)

### Delta 9: Solution Annotation Text Mismatch
- **Spec says**: "Small modules. Clear prompts. Always fits in context."
- **Implementation does**: Identical text (ContextRot.tsx:391)
- **Severity**: None (Match)

## Missing Elements

1. **Performance vs Context Length Graph Inset** (High Priority)
   - Should appear frames 1020-1110
   - Small overlay graph showing performance degradation curve
   - Citation: "Even with perfect retrieval, performance degrades 14-85% as context grows (EMNLP, 2025)"
   - Referenced in spec as crucial evidence for the context rot problem

2. **Return to Full Chart with Fork Visible** (Medium Priority)
   - Spec says "Frame 1110-1230: Return to chart - Zoom back out to show full chart with the fork visible"
   - Implementation shows the chart in Part 3 but it's not clear if it zooms back from a previous zoomed state or just fades in
   - The "fork point (2020) remains faintly visible at the left edge as an anchor" detail from Part 1 isn't explicitly verified

3. **Specific Grid Growth Stages** (Low Priority)
   - Spec describes discrete stages: "Grid expands: 4x4 → 8x8 → 16x16 → 32x32"
   - Implementation does animate through these sizes (CodebaseGrid.tsx grid size calculation in ContextWindowVisualization.tsx:19-44) but the transitions are smooth rather than discrete stages

## Implementation Strengths

1. **Clean Component Architecture**: Well-separated components (DebtLayerSeparation, ContextWindowVisualization, SplitViewMismatch) make the code maintainable
2. **Animated Noise Texture**: The feTurbulence filter for context rot (DebtLayerSeparation.tsx:186-201) is a nice touch that creates the "signal degradation" effect
3. **Pulse Effects**: Context rot pulse and generate line pulse in Part 3 are well-implemented
4. **Coverage Calculation**: The coverage percentage calculation is mathematically sound
5. **Split View Mismatch**: While different from the spec, the split-screen comparison is very clear and pedagogically effective

## Recommendations

1. **Add Performance Graph Inset**: This is a key piece of evidence cited in the narration. Should be a small overlay chart, not a full transition.
2. **Consider Reverting to In-Grid Mismatch**: The split view is clear but loses the visual continuity with the context window metaphor. Consider showing red/green highlights within the grid as spec describes.
3. **Add Discrete Growth Stages**: Consider making the grid growth more stepped (hold at each size) rather than smooth continuous growth to emphasize the 4→8→16→32 progression.
4. **Add Brief Red Flash on Irrelevant Blocks**: When at the large codebase state, briefly highlight some blocks inside the context window in red to show "grabbed the wrong stuff".
