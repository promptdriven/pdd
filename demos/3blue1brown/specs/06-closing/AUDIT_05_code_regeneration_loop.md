# Audit: Code Regeneration Loop (Section 6.5)

## Status: NOT IMPLEMENTED

### Requirements Met

- **Background color**: The `CodeOutputMoldGlows` component used in Visual 4 of `ClosingSection.tsx` does use the correct dark background (`#1a1a2e`), matching the spec's canvas requirement.
- **Narration alignment**: Visual 4 in `ClosingSection.tsx` is timed to the narration line "Code is generated, verified, and disposable" (starting at frame 620 / ~20.66s), which aligns with the spec's narration sync point.
- **Abstract code lines exist in the codebase**: `CodeOutputMoldGlows` renders abstract code bars with varying widths (`[70, 55, 80, 45, 65]`), matching the general visual concept of gray bars representing code. The `27-CodeRegenerates` composition also has code representation and a `DissolveEffect` particle system, though it is not used in the closing section for this slot.

### Issues Found

1. **No dedicated CodeRegenerationLoop composition exists** -- Severity: HIGH
   - Spec requires a `CodeRegenerationLoop` component with cycle-based state management (`cycleIndex = Math.floor(frame / 120)`, `cycleFrame = frame % 120`).
   - Implementation uses `CodeOutputMoldGlows` for Visual 4 (lines 64-69 of `ClosingSection.tsx`), which is a single-pass mold/plastic animation with no cycling logic whatsoever.

2. **No cycling/loop animation** -- Severity: HIGH
   - Spec requires 2.5 cycles over 300 frames (120 frames per cycle = 4 seconds each), with modulo-based frame logic to cycle through Hold -> Dissolve -> Regenerate -> Verify phases.
   - `CodeOutputMoldGlows` runs a one-shot animation: mold fades in (0-45 frames), plastic fades in (15-50 frames), text appears (120-250 frames). No looping, no repetition.

3. **No particle system for dissolution or regeneration** -- Severity: HIGH
   - Spec requires ~100 particles scattering outward during dissolution (frames 30-60 per cycle) and coalescing inward from triangle edges during regeneration (frames 60-90 per cycle), with per-particle angle, distance, delay, and size properties.
   - `CodeOutputMoldGlows` has zero particle effects. Note: `18-PlasticRegenerates/ParticleSystem.tsx` implements a 300-particle dissolve/regenerate system with staggered delays, eased motion, and color transitions (amber to gray and back) -- this is the earlier "plastic" version of the same concept but is not used in the closing section at all.

4. **No persistent triangle background** -- Severity: HIGH
   - Spec requires the triangle from Section 6.4 (vertices: PROMPT blue, TESTS amber, GROUNDING green) to persist at 60% glow intensity, with edges visible but not animated.
   - `CodeOutputMoldGlows` shows a rectangular mold shape on the left and a plastic block on the right. No triangle geometry is rendered. The `ThreeComponents` composition (used in Visual 3) has triangle geometry but is replaced, not layered, when Visual 4 begins.

5. **No code pattern variation between cycles** -- Severity: HIGH
   - Spec requires `generateCodePattern(seed)` using seeded RNG to produce visibly different bar widths for each regeneration cycle (v1, v2, v3), with version labels displayed.
   - `CodeOutputMoldGlows` renders a fixed set of five bars at hardcoded widths `[70, 55, 80, 45, 65]%`. No seed-based generation, no variation, no version labels.

6. **No terminal loop at bottom** -- Severity: HIGH
   - Spec requires a subtle terminal readout at the bottom of the frame showing cycling commands: `pdd generate parser` -> `Generated parser.py` -> `pdd test -> checkmark` -> repeat, with color changes per phase (blue for generate, white for regenerating, green for success).
   - `CodeOutputMoldGlows` has no terminal component. The `27-CodeRegenerates` composition has a `TerminalOverlay` component that shows progressive terminal lines, but it is positioned bottom-right (not center-bottom), is not cycling, and is not used in the closing section.

7. **No green checkmark verification per cycle** -- Severity: HIGH
   - Spec requires a green checkmark (`#5AAA6E`) appearing at the code block position during frames 90-120 of each cycle, with interpolated opacity using easeOutBack for a pop effect.
   - `CodeOutputMoldGlows` has no checkmark. `27-CodeRegenerates` has a `SuccessIndicator` with a checkmark, but it appears once (not per-cycle) and is positioned top-right rather than at the code block centroid.

8. **No final hold logic** -- Severity: MEDIUM
   - Spec requires that after frame 240, the loop stops and holds on the final version (v3) with the triangle steady, code present but unremarkable, and terminal showing final checkmark.
   - Not applicable since the loop itself is not implemented.

9. **Visual 4 slot duration mismatch** -- Severity: MEDIUM
   - Spec calls for ~10 seconds (300 frames at 30fps).
   - The Visual 4 slot in `ClosingSection.tsx` runs from frame 620 to frame 740 (120 frames = 4 seconds), which is less than half the specified duration. Even accounting for the narration timing (~20.7s to ~26.9s = ~6.2s), the slot is too short for 2.5 full cycles at 4 seconds each.

### Notes

- The `CodeOutputMoldGlows` component is actually better aligned with spec 6.6 ("Final Frame: The Mold Glows, The Code is Unremarkable") than with spec 6.5. In `ClosingSection.tsx`, it is used for both Visual 4 and Visual 5, suggesting that specs 6.5 and 6.6 may have been collapsed into one visual in implementation rather than implemented as distinct compositions.
- The codebase contains building blocks that are conceptually similar to what the spec requires but in different contexts: `18-PlasticRegenerates/ParticleSystem.tsx` has a full 300-particle dissolve/regenerate system with staggered delays, eased motion, and color interpolation. `27-CodeRegenerates` has a `DissolveEffect`, `FluidSimulation`, `SuccessIndicator`, and `TerminalOverlay`. Neither of these is wired into the closing section for this visual slot.
- A new dedicated `CodeRegenerationLoop` composition would need to be created, integrating: (a) cycle management with `cycleIndex`/`cycleFrame` modulo logic, (b) a dimmed `TriangleDiagram` background at 60% opacity, (c) a `CodeBlock` component with seed-based pattern generation, (d) `DissolutionEffect` and `RegenerationEffect` particle sub-components, (e) a center-bottom `TerminalLoop` with phase-aware cycling text, and (f) a per-cycle green checkmark with pop easing. After creation, `ClosingSection.tsx` line 67 would need to swap `CodeOutputMoldGlows` for the new composition, and the timing slot would need to be extended to accommodate 2.5 full cycles.
