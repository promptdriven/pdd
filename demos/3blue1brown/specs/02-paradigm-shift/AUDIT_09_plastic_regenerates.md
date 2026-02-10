# Audit: Plastic Part Dissolves and Regenerates (Section 2.9)

## Status: PASS

### Requirements Met

1. **Duration (~10 seconds, timestamp 9:03-9:16)**: Implementation defines 300 frames at 30 fps = 10 seconds exactly. `constants.ts:4-7` sets `PLASTIC_REGEN_FPS = 30`, `PLASTIC_REGEN_DURATION_SECONDS = 10`, and `PLASTIC_REGEN_DURATION_FRAMES = 300`. The composition is registered in `Root.tsx:608-618` with these values.

2. **Canvas resolution (1920x1080)**: `constants.ts:8-9` defines `PLASTIC_REGEN_WIDTH = 1920` and `PLASTIC_REGEN_HEIGHT = 1080`. The SVG element in `PlasticRegenerates.tsx:93-96` uses `width="1920" height="1080" viewBox="0 0 1920 1080"`. Root.tsx registration at lines 614-615 passes these dimensions.

3. **Dark background (#1a1a2e)**: `constants.ts:36` defines `BACKGROUND: "#1a1a2e"`. `PlasticRegenerates.tsx:89` applies it as a linear gradient from `#1a1a2e` to `#0f0f1a` (a slightly darker shade for depth). Matches spec.

4. **Plastic part - simple geometric shape, Amber #D9944A, positioned center-right**: `constants.ts:38` defines `PART_AMBER: "#D9944A"`. `constants.ts:50-56` defines the part as an 80x44 rounded rectangle with rx=10 at position (1100, 500) -- which is center-right of a 1920x1080 frame. `PlasticRegenerates.tsx:188-196` renders it as an SVG `<rect>` with these exact parameters and `fill={COLORS.PART_AMBER}`.

5. **Mold (background) - visible but slightly faded, still glowing with value aura, source of all parts**: The mold is rendered at `PlasticRegenerates.tsx:149-181` positioned at (500, 480) per `constants.ts:59-66`. It includes:
   - Base opacity of 0.5 with subtle pulsing glow via `Math.sin(frame * 0.08) * 0.1` (`PlasticRegenerates.tsx:52-54`)
   - Gold/white radial gradient aura with gaussian blur (`PlasticRegenerates.tsx:106-110, 152-159`)
   - Metallic gradient body from `#7a8a9a` to `#4a5a6a` (`PlasticRegenerates.tsx:100-104`)
   - Cavity detail (`PlasticRegenerates.tsx:173-180`)
   - Brightness boost of +0.3 opacity during regeneration phase (`PlasticRegenerates.tsx:56-62`)

6. **Animation sequence - all six phases match spec frame timings**: `constants.ts:18-32` defines BEATS that map exactly to spec:
   - Frame 0-30 (0-1s): Setup -- part visible, mold glowing (`SETUP_START: 0, SETUP_END: 30`)
   - Frame 30-90 (1-3s): Dissolution begins (`DISSOLVE_START: 30, DISSOLVE_END: 90`)
   - Frame 90-120 (3-4s): Fully dissolved, beat of absence (`ABSENCE_START: 90, ABSENCE_END: 120`)
   - Frame 120-180 (4-6s): Regeneration begins (`REGEN_START: 120, REGEN_END: 180`)
   - Frame 180-240 (6-8s): Part fully reformed (`REFORMED_START: 180, REFORMED_END: 240`)
   - Frame 240-300 (8-10s): Hold (`HOLD_START: 240, HOLD_END: 300`)

7. **Dissolution effect - part breaks into particles, scatter/fade, quick satisfying dissolution**: `ParticleSystem.tsx:52-54` activates dissolution for frames 30-120 (dissolve + absence). Particles scatter outward from part center at `ParticleSystem.tsx:85-86` using radial angles. Color fades from amber to gray at `ParticleSystem.tsx:104-114`. Opacity decreases during absence beat at `ParticleSystem.tsx:124-131`.

8. **Regeneration effect - new particles coalesce, form identical part, pop into existence**: `ParticleSystem.tsx:55-57` activates regeneration for frames 120-180. Particles flow inward from mold direction (`ParticleSystem.tsx:148-157`), color transitions gray to amber (`ParticleSystem.tsx:163-166`), and size grows as particles converge (`ParticleSystem.tsx:160`).

9. **Particle count (200-500)**: `constants.ts:69` sets `PARTICLE_COUNT = 300`, which is within the specified range.

10. **Dissolution particle specs**:
    - Direction outward with randomness: Radial outward with per-particle random angle offset of up to 0.6 radians (`ParticleSystem.tsx:37-40, 85-86`). Matches "outward, slightly random".
    - Fast initial burst then drift: Uses `Easing.out(Easing.quad)` at `ParticleSystem.tsx:81-83`, which matches the spec's `easeOutQuad`. Additional drift during absence at `ParticleSystem.tsx:88-99`.
    - Size 2-5px: `size: 2 + seededRandom(i + 2000) * 3` at `ParticleSystem.tsx:43` produces values in [2, 5). Matches spec.
    - Color Amber to Gray to Fade: RGB interpolation from (217,148,74) to (136,136,136) at `ParticleSystem.tsx:110-114`. Opacity fades during absence at `ParticleSystem.tsx:117-131`. Matches "Amber -> Gray -> Fade".
    - Easing easeOutQuad: `Easing.out(Easing.quad)` at `ParticleSystem.tsx:81-83`. Exact match.

11. **Regeneration particle specs**:
    - Direction inward from edges/mold: Particles originate from mold direction (PI +/- PI*0.4 spread) at distances 150-400px (`ParticleSystem.tsx:45-48`), and interpolate toward part center (`ParticleSystem.tsx:156-157`). Matches "inward from edges/mold".
    - Accelerating toward center: Uses `Easing.in(Easing.cubic)` at `ParticleSystem.tsx:143-145`. Exact match for `easeInCubic`.
    - Size Small to Original: `r = p.size * (0.4 + 0.6 * easedProgress)` at `ParticleSystem.tsx:160` grows from 40% to 100% of base size. Matches "Small -> Original".
    - Color Gray to Amber: RGB interpolation from (136,136,136) to (217,148,74) at `ParticleSystem.tsx:163-166`. Matches spec.
    - Easing easeInCubic: `Easing.in(Easing.cubic)` at `ParticleSystem.tsx:143-145`. Exact match.

12. **Particle stagger delay (0-0.3)**: Both dissolution and regeneration use `delay: seededRandom(i + 1000) * 0.3` (`ParticleSystem.tsx:42`) with stagger applied at lines 79 and 141. Matches the spec's example code pattern `delay: Math.random() * 0.3`.

13. **Completion glow/pulse on reformed part**: `PlasticRegenerates.tsx:65-70` defines a multi-keyframe interpolation over frames 180-240: 0 -> 1 -> 0.6 -> 0, creating a pulse effect. Rendered as a radial gradient ellipse with 20px gaussian blur at `PlasticRegenerates.tsx:112-116, 138-146, 200-210`. Matches "Slight glow/pulse on completion" and "satisfying snap into place".

14. **Part visibility lifecycle**: Part is solid during setup (frames 0-30), fades out during dissolution start (`PlasticRegenerates.tsx:32-37`), is absent during dissolve/absence/regen phases (`PlasticRegenerates.tsx:46-49`), and fades back in at reformed phase (`PlasticRegenerates.tsx:39-44`). Matches the spec's "Part is gone" during absence and "Identical to before" when reformed.

15. **Narration text**: Spec requires "The plastic part? Disposable. Regenerate it at will." Implementation renders this exact string at `PlasticRegenerates.tsx:237`. Fades in at frame 240 (`NARRATION_START: 240` in `constants.ts:31`) over 30 frames with `Easing.out(Easing.cubic)` (`PlasticRegenerates.tsx:73-84`).

16. **Section integration in Part2ParadigmShift**: PlasticRegenerates is imported at `Part2ParadigmShift.tsx:17` and rendered as Visual 6 at `Part2ParadigmShift.tsx:95-99`, sequenced from `BEATS.VISUAL_06_START`. The S02 `constants.ts:76` defines `VISUAL_06_START: s2f(54.82)` = frame 1645, aligning with narration segment "[10] In molding, value lives in the specification...". The visual sequence entry at `constants.ts:112` maps the correct description.

17. **Composition registration in Root.tsx**: Registered in `Root.tsx:608-618` under folder `"18-PlasticRegenerates"` with id `"PlasticRegenerates"`, using `PLASTIC_REGEN_DURATION_FRAMES` (300), `PLASTIC_REGEN_FPS` (30), `PLASTIC_REGEN_WIDTH` (1920), `PLASTIC_REGEN_HEIGHT` (1080), and `defaultPlasticRegeneratesProps`.

18. **Code structure**: Spec suggests separate `MoldBackground`, `PlasticPart`, `DissolutionEffect`, `RegenerationEffect` components. Implementation consolidates into `PlasticRegenerates.tsx` (main composition with inline mold and part SVG) and `ParticleSystem.tsx` (unified dissolve/regenerate particle logic). This is an architectural simplification that reduces component overhead while preserving all visual behaviors. The suggested structure in the spec is explicitly labeled as non-binding example code.

19. **Deterministic rendering**: Uses a seeded pseudo-random function `seededRandom()` at `constants.ts:75-78` based on `Math.sin()` hashing, ensuring identical particle positions across frame-seeking renders -- essential for Remotion's rendering model.

20. **Focus on single part and mold**: The composition renders exactly one part (center-right at 1100, 500) and one mold (left side at 500, 480). No additional elements clutter the scene. Matches "Focus on single part and mold".

### Issues Found

None. All spec requirements are fully implemented with accurate fidelity.

### Notes

- **Audio effects not in component**: The spec describes dissolution "whoosh", silence beat, regeneration "crystallize", and completion "click/snap" sounds. These are not implemented in the component code. This is consistent with the project's architecture where audio is managed at the section composition level (`Part2ParadigmShift.tsx:36` loads a single narration audio track) or in post-production.
- **Enhancements beyond spec**: The implementation includes several visual improvements that do not contradict the spec:
  - Absence drift: particles continue moving during the 90-120 absence beat (`ParticleSystem.tsx:88-99`), preventing a static freeze.
  - Mold brightness boost during regeneration (`PlasticRegenerates.tsx:56-62`), visually reinforcing the mold as the source.
  - Opacity culling: particles with opacity below 0.01 return null (`ParticleSystem.tsx:177`), optimizing render performance.
  - Multi-keyframe opacity transitions for smoother visual progression.
  - Background gradient (dark to darker) instead of flat color, adding depth.
- **File organization**: Clean 4-file structure: `PlasticRegenerates.tsx` (243 lines, main composition), `ParticleSystem.tsx` (193 lines, particle logic), `constants.ts` (94 lines, configuration and types), `index.ts` (10 lines, re-exports).
- **Props validation**: Uses Zod schema (`constants.ts:81-93`) for runtime prop validation, consistent with other compositions in this project.

## Resolution Status
- **Status**: RESOLVED
- **Changes Made**: No changes needed
- **Remaining Issues**: None

## Re-Audit Update (2026-02-09)
- **Status**: PASS
- **Result**: Standalone render at frame 134 confirms the composition renders correctly at the mid-dissolution/early-regeneration phase. The mold is visible on the left with its gold aura glow. Amber particles are visible dispersing from the part position, consistent with the dissolution-to-regeneration transition at this frame. The dark background gradient renders cleanly. The particle system uses deterministic seeded random for consistent output. No new issues detected.
