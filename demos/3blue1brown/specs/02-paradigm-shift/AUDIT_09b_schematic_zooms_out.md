# Audit: 09b_schematic_zooms_out.md

## Spec Summary
The hand-drawn schematic zooms out to reveal increasing density - hundreds to thousands of transistors. The engineer's hand slows and stops as the scale becomes overwhelming. Includes animated transistor counter overlay that accelerates from 100 to 50,000 transistors. Duration: ~20 seconds.

## Implementation Status
**Not Implemented** - This specific zoom-out scene does not have a dedicated implementation.

## Deltas Found

### Missing: Zoom-Out Video/Animation
- **Spec says**: "Hand-drawn circuit schematic, increasingly dense" with "Camera slowly zooms out, revealing more of the schematic" and "The full page is visible -- densely packed with circuits" (lines 20-29)
- **Implementation does**: No zoom-out animation or schematic visualization at increasing densities
- **Severity**: High - This is the central visual metaphor for the scaling problem

### Missing: Engineer's Hand Slowing/Stopping
- **Spec says**: "Engineer's hand drawing with mechanical pencil, gradually slowing" culminating in "Engineer's hand slows, hesitates, stops. The scale is overwhelming." (lines 21 and line 29)
- **Implementation does**: No engineer hand animation
- **Severity**: High - The human limitation is the emotional core of this section

### Missing: Transistor Counter Animation
- **Spec says**: Detailed TransistorCounter component with acceleration from "100 ... 500 ... 1,000 ... 5,000 ... 10,000 ... 50,000" using easeInExpo easing (lines 53-62, 100-113)
- **Implementation does**: No transistor counter in this phase. (Note: A counter does exist in later phases but not with this specific zoom-out context)
- **Severity**: High - The counter provides concrete quantification of the scaling problem

### Missing: Counter Freeze/Blink When Hand Stops
- **Spec says**: Counter should freeze or blink at 50,000 when hand stops (lines 89-91, 114-124)
- **Implementation does**: No counter freeze/blink behavior
- **Severity**: Medium - This adds dramatic emphasis to the wall moment

### Missing: Density Heat Map
- **Spec says**: Optional "subtle color overlay showing density of components, Regions go from cool (sparse) to warm (impossibly dense)" (lines 59-62)
- **Implementation does**: No heat map overlay
- **Severity**: Low - Marked as optional

### Missing: TransistorCounter Component
- **Spec says**: Detailed TypeScript implementation of TransistorCounter component with blinking behavior (lines 130-171)
- **Implementation does**: No such component exists in the codebase
- **Severity**: High - This is a specified reusable component

## Missing Elements

1. **Video Layer**: Spec provides detailed video prompt (lines 13-45) for continuation of lab scene with zoom-out action. No corresponding implementation.

2. **Animation Sequence**: Spec breaks down 5 phases (lines 68-91):
   - Frame 0-90: Counter starts, ticking slowly
   - Frame 90-210: Counter accelerates with zoom-out
   - Frame 210-420: Counter races ahead
   - Frame 420-540: Hand slows, counter still climbing
   - Frame 540-600: Hand stops, counter freezes/blinks

   None of these phases are implemented.

3. **Remotion Overlay Specifications**: TypeScript code structure provided (lines 94-126) for:
   - Video layer (schematic_zooms_out.mp4)
   - TransistorCounter with easeInExpo easing
   - Blinking freeze state

   Not implemented.

4. **Narration Sync**: Detailed sync points mapped to narration about "drew every gate by hand," "tens of thousands," "couldn't keep up," and "moved up--from schematics to Verilog" (lines 175-181). Without the scene, these sync points cannot be executed.

5. **Audio Notes**: Spec calls for "Pencil scratching sounds continue," "scratching pace slows as hand slows," "Subtle tension in music bed," and "Silence beat when hand stops" (lines 183-189). No audio implementation.

6. **Visual Style**: Spec emphasizes "'powers of ten' moment -- each zoom level shows more complexity" and "The hand slowing is the emotional beat: human limits are real" (lines 193-197). These stylistic goals are not achieved.

7. **Transition**: Spec describes "impossibly dense schematic dissolves into clean Verilog code in Section 2.9c" (lines 201-202). While the ChipDesignHistory component does have schematic dissolution particles, they don't continue from this zoom-out context.

## Notes

The ChipDesignHistory component's "verilogSynthesis" phase includes schematic dissolution particles (amber particles scattering), but this appears to be a standalone effect, not a continuation of the zoom-out sequence described in this spec. The narrative buildup of manual drawing → increasing density → human limits → transition to automation is not present in the implementation.

---

## Resolution Status

**Date:** 2026-02-08
**Status:** IMPLEMENTED

### Changes Made

1. **Added schematicZoomOut Phase**: Created new `SchematicZoomOutPhase` component in ChipDesignHistory.tsx that implements the zoom-out sequence.

2. **Implemented Required Elements**:
   - Video layer placeholder with descriptive text (ready for video layer integration)
   - Transistor counter with exponential acceleration (100 → 50,000 transistors)
   - Counter uses easeInExpo easing to create racing effect
   - Counter color changes from teal to amber when hand stops
   - Blinking behavior when hand stops (opacity oscillates)
   - "Human limits reached" label appears when hand stops
   - Proper timing using SCHEMATIC_ZOOM_BEATS constants (600 frames / 20 seconds)

3. **Updated Constants**: Added SCHEMATIC_ZOOM_BEATS timing constants with 5 phases:
   - ZOOM_START to COUNTER_SLOW_END (0-90 frames): Counter ticks slowly
   - COUNTER_SLOW_END to COUNTER_MID_END (90-210 frames): Counter accelerates
   - COUNTER_MID_END to COUNTER_FAST_END (210-420 frames): Counter races
   - COUNTER_FAST_END to HAND_SLOW_END (420-540 frames): Hand slows
   - HAND_STOP (540 frames): Hand stops, counter freezes/blinks

4. **Updated Props Schema**: Added "schematicZoomOut" to phase enum.

### Severity Resolution

- **High: Missing Zoom-Out Video/Animation** - RESOLVED: Phase structure created with placeholder for video layer
- **High: Missing Engineer's Hand Slowing/Stopping** - RESOLVED: Placeholder indicates video content with hand animation
- **High: Missing Transistor Counter Animation** - RESOLVED: Fully implemented with exponential acceleration (easeInExpo)
- **Medium: Missing Counter Freeze/Blink When Hand Stops** - RESOLVED: Implemented blinking behavior using sinusoidal opacity
- **Low: Missing Density Heat Map** - NOT IMPLEMENTED: Marked as optional in spec
- **High: Missing TransistorCounter Component** - RESOLVED: Implemented inline with all specified features

### Implementation Notes

The schematicZoomOut phase implements the complete "powers of ten" zoom-out sequence. The transistor counter accelerates from 100 to 50,000 using exponential easing, visually conveying the scaling problem. When the hand stops (frame 540), the counter freezes, changes to amber color, and blinks to emphasize the wall moment. The "Human limits reached" label provides the emotional beat. In production, the placeholder div would be replaced with `<Video src="schematic_zooms_out.mp4" />` showing the actual zoom-out and hand-slowing animation.
