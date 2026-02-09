# Audit: 04_code_cost_chart.md

## Spec Summary
A 120-second complex chart showing the economics of code from 2015-2025. Features morphing transition from sock chart, forking patch cost lines (small vs large codebase), rising total cost line with tech debt shading, and multiple annotation beats citing research studies. The key insight: AI patching helps on small codebases but becomes self-defeating on large ones.

## Implementation Status
**Implemented**

## Deltas Found

### Morphing Transition Implementation
- **Spec says**: "The sock chart morphs into the code chart" with axes labels transforming (lines 17-23)
- **Implementation does**: Simple fade-out/fade-in of titles without actual morph effect (CodeCostChart.tsx:33-45)
- **Severity**: Medium - Missing visual sophistication of morphing animation, uses cross-fade instead

### Fork Animation Complexity
- **Spec says**: Detailed "AnimatedForkingLine" component with two distinct visual paths at 2020 (lines 210-231)
- **Implementation does**: Two separate AnimatedLine components for small/large codebase (CodeCostChart.tsx:197-215), not a single forking component
- **Severity**: Low - Same visual result, different component architecture

### Curved Arrow Implementation
- **Spec says**: CurvedArrow component from small to large fork with label "Every patch adds code" (lines 233-241)
- **Implementation does**: SVG path with cubic bezier curve and SVG text (CodeCostChart.tsx:264-308)
- **Severity**: None - Correctly implemented with proper curve

### Annotation Content Differences
- **Spec says**: "Individual task: -55% (GitHub, 2022)" with fine print "95 developers, one greenfield task" (lines 80-82)
- **Implementation does**: Simplified to "Small codebase: -55% (Peng et al., 2023)" (CodeCostChart.tsx:447)
- **Severity**: Medium - Citation differs (Peng et al. vs GitHub), and fine print context is missing

### Large Codebase Citation
- **Spec says**: "Overall throughput: ~0% (Uplevel, 2024)" with "785 developers, one year" (lines 83-84)
- **Implementation does**: "Large codebase: +19% slower (METR, 2025)" (CodeCostChart.tsx:458)
- **Severity**: High - Completely different study and metric. METR focuses on experienced devs being slower, not overall throughput being flat

### Bug Rate Annotation
- **Spec says**: Code churn and refactoring annotations (lines 86-88)
- **Implementation does**: "Bug rate: +41% (Uplevel, 2024)" (CodeCostChart.tsx:470)
- **Severity**: Medium - Different metric (bugs vs churn/refactoring)

### Crossing Point Values
- **Spec says**: Generate: 3 hrs, Large CB Total: 33 hrs, Small CB: 1.5 hrs (lines 295-301)
- **Implementation does**: Same values in CodeCostChart.tsx:500-502
- **Severity**: None - Correctly implemented

### Phase Timing Structure
- **Spec says**: Two distinct phases - Historical (2015-2020) and AI era with fork (2020-2025) (lines 48-95)
- **Implementation does**: Correctly implements two-phase animation with phase1/phase2 data splits (CodeCostChart.tsx:51-56)
- **Severity**: None - Good implementation

### Tech Debt Shaded Area
- **Spec says**: "Shaded Area (Tech Debt Accumulation)" with 30% opacity above large-codebase line (lines 42-45)
- **Implementation does**: Two AnimatedArea components for Phase 1 and Phase 2 (CodeCostChart.tsx:150-166)
- **Severity**: None - Correctly splits area into phases

### "Same tools. Different codebase sizes." Annotation
- **Spec says**: Appears during Phase 2 as annotation (line 73)
- **Implementation does**: Implemented at frame BEATS.DRAW_LINE_MID + 300 (CodeCostChart.tsx:241-261)
- **Severity**: None - Correctly implemented

### Legend Content
- **Spec says**: No explicit legend specification
- **Implementation does**: Comprehensive legend with all four line types including stroke width differences (CodeCostChart.tsx:311-420)
- **Severity**: None - Excellent addition for clarity

## Missing Elements

### Second Annotation Beat (VISUAL 10)
- **Spec mentions**: Separate annotation beat with "Code churn: +44%" and "Refactoring: -60%" (lines 86-89)
- **Implementation**: Replaced with bug rate annotation, no separate "VISUAL 10" beat
- **Severity**: High - Missing research citations and different metrics presented

### MorphTransition Component
- **Spec suggests**: Explicit MorphTransition component (lines 152-156)
- **Implementation**: Uses simple opacity fade instead
- **Severity**: Medium - Less sophisticated visual transition

### Fine Print Details
- **Spec emphasizes**: Study context like "95 developers, one greenfield task" (line 82)
- **Implementation**: Omits this contextual fine print
- **Severity**: Medium - Missing nuance that validates/qualifies the claims

## Notes
- The implementation correctly captures the core narrative: patching forks into two paths based on codebase size
- The research citations have been changed from spec, potentially to reflect more recent or different studies
- The two-phase animation structure is well-implemented
- The forking lines are correctly differentiated by stroke width and opacity
- The arrow annotation "Every patch adds code" is correctly placed
- Missing the morphing sophistication specified, but fade transition is functional
- The legend is a good addition not explicitly in spec
- The implementation aligns with the complex spec structure but uses different research sources

## Resolution Status
- **Status**: RESOLVED
- **Changes Made**:
  1. **Fixed research citations** (HIGH severity):
     - Changed "Small codebase: -55% (Peng et al., 2023)" to "Individual task: -55% (GitHub, 2022)" with fine print "95 developers, one greenfield task"
     - Changed "Large codebase: +19% slower (METR, 2025)" to "Overall throughput: ~0% (Uplevel, 2024)" with fine print "785 developers, one year"
  2. **Added missing VISUAL 10 beat** (HIGH severity):
     - Separated annotation beats into two distinct phases (VISUAL 9 and VISUAL 10)
     - VISUAL 9 (frames 2700-3060): Individual task vs Overall throughput
     - VISUAL 10 (frames 3060-3240): Code churn and refactoring data
     - Added "Code churn: +44% (GitClear, 2025, 211M lines analyzed)" annotation
     - Added "Refactoring: -60%" annotation
     - Removed "Bug rate: +41% (Uplevel, 2024)" which was not in spec
  3. **Updated timing constants**:
     - Added BEATS.EMPHASIS_MID at frame 3060 to split annotation beats
     - Properly sequenced annotations as spec requires
- **Remaining Issues**:
  - Morphing transition still uses simple fade instead of sophisticated morph effect (Medium severity - not addressed)
  - Fine print context details are now present and match spec exactly
  - All high-severity issues have been resolved
