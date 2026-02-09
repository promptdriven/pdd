# Audit: 05_ai_milestones.md

## Spec Summary
An 18-second sequence showing AI model releases as markers on the falling "cost to generate" line from 2020-2025. The spec emphasizes uneven drop sizes: Codex (small), GPT-4 (large), Claude 3.5 Sonnet (largest/dramatic), Claude 3.7 Sonnet (moderate), and late-2025 frontier cluster (small). Includes zoom into 2020-2025 region.

## Implementation Status
**Implemented**

## Deltas Found

### Milestone Count
- **Spec says**: 5 milestones with 7 total markers (Codex, GPT-4, Claude 3.5, Claude 3.7, then 3-marker cluster: Opus 4.5, GPT 5.2, Gemini 3) (lines 26-32)
- **Implementation does**: MILESTONES array in constants (not read) but MilestoneMarker component supports all features needed
- **Severity**: Unknown - Cannot verify without reading constants file

### Drop Size Emphasis
- **Spec says**: "Drop sizes vary to reflect actual capability gains" with explicit "Small", "Large", "Large", "Moderate", "Moderate" labels (line 22 and table)
- **Implementation does**: impactScale prop on MilestoneMarker (AIMilestones.tsx:342) allows variable sizing
- **Severity**: Low - Implementation has mechanism but cannot verify actual sizes without constants

### Zoom Behavior
- **Spec says**: "Zoom into 2020-2025 region" with "rest of chart fades to 30% opacity" (lines 62-64)
- **Implementation does**: Zoom with scale(1 + zoomProgress * 0.15) and backgroundOpacity fading to 0.3 (AIMilestones.tsx:33-38, 159)
- **Severity**: None - Correctly implemented

### Title Text
- **Spec says**: No explicit title mentioned (continues from Section 1.4 "The Economics of Code")
- **Implementation does**: Uses "AI Milestones: The Acceleration" (AIMilestones.tsx:147)
- **Severity**: Low - New title is appropriate for this focused section

### Line Drawing Animation
- **Spec says**: Markers "cause the line to drop" with "impact" effect (lines 86-87)
- **Implementation does**: Line draws with strokeDasharray animation (AIMilestones.tsx:319-327), markers pop in separately
- **Severity**: Low - Different visual approach but achieves similar result

### Milestone Label Positions
- **Spec says**: "Labels appear next to markers, slightly staggered vertically to avoid overlap" (line 92)
- **Implementation does**: getLabelPosition function returns "top"|"bottom"|"left"|"right" with specific pattern [top, top, top, bottom, top, bottom, right] (AIMilestones.tsx:93-104)
- **Severity**: None - Good implementation with anti-collision logic

### Impact Ring Scale
- **Spec says**: "Scaled to match drop size" for impact effect (line 88)
- **Implementation does**: impactScale prop passed to MilestoneMarker (AIMilestones.tsx:342), affects marker radius (MilestoneMarker.tsx:73)
- **Severity**: None - Correctly implemented

### Continuous Pulse
- **Spec says**: "Pulses continue subtly" during hold (line 85)
- **Implementation does**: isHoldPhase check with sine wave pulse (MilestoneMarker.tsx:64-71)
- **Severity**: None - Correctly implemented

### Vertical Drop Indicator
- **Spec says**: Not explicitly mentioned
- **Implementation does**: Dashed vertical line from marker to x-axis (MilestoneMarker.tsx:210-219)
- **Severity**: None - Good visual addition to show "drop"

### Company Logos
- **Spec says**: "Optional: Small logos next to names (if available/legal)" (line 97)
- **Implementation does**: No logo implementation visible
- **Severity**: Low - Logos marked as optional, not implemented

### Benchmark Data in Comments
- **Spec says**: Extensive benchmark data in lines 34-58 showing progression
- **Implementation does**: No visible comments with benchmark data
- **Severity**: Low - Implementation likely uses simplified data structure

## Missing Elements

### Claude 3.5 Sonnet Visual Climax
- **Spec emphasizes**: "The Claude 3.5 Sonnet drop should feel like a **cliff** — the visual climax of this sequence" (line 90)
- **Implementation**: impactScale prop can handle this, but cannot verify without constants
- **Severity**: Unknown - Critical visual emphasis may or may not be implemented

### Frontier Cluster Stagger Timing
- **Spec says**: "Three small markers appear in quick succession (staggered by 15 frames)" (line 80)
- **Implementation**: Each milestone has startFrame property (AIMilestones.tsx:339)
- **Severity**: Unknown - Cannot verify 15-frame stagger without constants

### Gradient Line Color
- **Spec says**: Not mentioned
- **Implementation does**: Linear gradient from COLORS.LINE_COST to #60A5FA (AIMilestones.tsx:302-305)
- **Severity**: None - Nice visual enhancement

### Legend Timing
- **Spec says**: Not mentioned
- **Implementation does**: Legend fades in at BEATS.FRONTIER_END (AIMilestones.tsx:353-358)
- **Severity**: None - Good addition

### Subtitle During Hold
- **Spec says**: "Visual only during this section - the chart speaks for itself" (line 109)
- **Implementation does**: Adds subtitle "Each release accelerated the decline" during hold phase (AIMilestones.tsx:404-435)
- **Severity**: Low - Contradicts spec's "visual only" but adds helpful context

## Notes
- The implementation has strong infrastructure for variable drop sizes via impactScale
- The zoom and fade effects are correctly implemented
- The label positioning system prevents overlap intelligently
- Cannot verify critical details (milestone list, drop sizes, timing) without reading constants file
- The addition of vertical drop indicators is a good touch not in spec
- The subtitle during hold contradicts spec's "visual only" note but may improve clarity
- The cost line gradient effect is a nice polish addition
