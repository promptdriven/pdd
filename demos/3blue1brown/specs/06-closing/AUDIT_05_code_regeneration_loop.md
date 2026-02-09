# Audit: Code Regeneration Loop (Section 6.5)

## Status: NOT IMPLEMENTED

The spec calls for a dedicated `CodeRegenerationLoop` composition featuring a cyclic dissolve-and-regenerate animation of code within a persistent triangle diagram. No such composition exists. The closing section's Visual 4 slot (narration: "Code is generated, verified, and disposable") uses `CodeOutputMoldGlows` instead, which is a single-pass mold-and-plastic reveal animation with no cycling behavior.

---

### Requirements Met

1. **Canvas resolution**: 1920x1080 is used across all related compositions.
   - `38-CodeOutputMoldGlows/constants.ts:8-9` (`CODE_OUTPUT_WIDTH = 1920`, `CODE_OUTPUT_HEIGHT = 1080`)
   - `27-CodeRegenerates/constants.ts:8-9` (`CODE_REGEN_WIDTH = 1920`, `CODE_REGEN_HEIGHT = 1080`)

2. **Background color `#1a1a2e`**: Matches the spec's dark background requirement.
   - `38-CodeOutputMoldGlows/constants.ts:38` (`BACKGROUND: "#1a1a2e"`)
   - `38-CodeOutputMoldGlows/CodeOutputMoldGlows.tsx:115` (`backgroundColor: COLORS.BACKGROUND`)
   - `27-CodeRegenerates/constants.ts:38` (`BACKGROUND: "#1a1a2e"`)

3. **FPS = 30**: Both compositions use 30fps.
   - `38-CodeOutputMoldGlows/constants.ts:4` (`CODE_OUTPUT_FPS = 30`)
   - `27-CodeRegenerates/constants.ts:4` (`CODE_REGEN_FPS = 30`)

4. **Narration alignment for "Code is generated, verified, and disposable"**: Visual 4 in `ClosingSection.tsx` starts at frame 620 (~20.66s), which aligns with the narration timestamp.
   - `S06-Closing/constants.ts:47` (`VISUAL_04_START: s2f(20.66)`)
   - `S06-Closing/ClosingSection.tsx:65-69` (Visual 4 renders `CodeOutputMoldGlows`)

5. **Abstract code bars exist as a concept**: `CodeOutputMoldGlows` renders gray code bars with varying widths, loosely matching the spec's "abstract code lines (gray bars of varying width)" concept.
   - `38-CodeOutputMoldGlows/CodeOutputMoldGlows.tsx:198-210` (five bars at fixed widths `[70, 55, 80, 45, 65]%`)

6. **Green success color `#5AAA6E`**: The correct green is defined in both compositions.
   - `27-CodeRegenerates/constants.ts:40` (`SUCCESS_GREEN: "#5AAA6E"`)
   - `38-CodeOutputMoldGlows/constants.ts:40` (`GROUNDING_GREEN: "#5AAA6E"`)

---

### Issues Found

1. **No `CodeRegenerationLoop` composition exists** -- Severity: **HIGH**
   - Spec defines a `CodeRegenerationLoop` component with cycle-based state management: `cycleIndex = Math.floor(frame / 120)`, `cycleFrame = frame % 120`, and distinct per-cycle phases (hold, dissolve, regenerate, verify).
   - The closing section uses `CodeOutputMoldGlows` (`S06-Closing/ClosingSection.tsx:66-68`), which has zero cycling logic. The standalone `27-CodeRegenerates` composition exists but implements a different concept (mold cross-section with fluid injection, not a triangle-based regeneration loop) and is not wired into `ClosingSection.tsx`.

2. **No cycling/loop animation (2.5 cycles over 10 seconds)** -- Severity: **HIGH**
   - Spec requires 2.5 cycles over 300 frames (120 frames per cycle = 4 seconds each), with modulo-based frame phases: Hold (0-30), Dissolve (30-60), Regenerate (60-90), Verify (90-120).
   - `CodeOutputMoldGlows` is a one-shot animation: mold fades in (frames 0-45), plastic fades in (frames 15-50), text appears (frames 120-250). No frame modulo, no repetition, no cycle counter.
   - `38-CodeOutputMoldGlows/CodeOutputMoldGlows.tsx:52-256` -- entire component is linear, no cycle logic.

3. **No persistent triangle background at 60% opacity** -- Severity: **HIGH**
   - Spec requires the triangle from Section 6.4 (vertices: PROMPT blue, TESTS amber, GROUNDING green) to persist as a dimmed background at 60% opacity with edges visible but not animated.
   - `CodeOutputMoldGlows` renders a rectangular mold shape with colored bars on the left and a plastic block on the right. No triangle geometry.
   - `37-ThreeComponents/ThreeComponents.tsx` has full triangle rendering (vertices at `TRIANGLE.PROMPT`, `TRIANGLE.TESTS`, `TRIANGLE.GROUNDING` with correct colors), but it is used in Visual 3 (`S06-Closing/ClosingSection.tsx:59-62`) and replaced (not layered) when Visual 4 begins. The `activeVisual` logic (`ClosingSection.tsx:22-27`) ensures only one visual renders at a time.

4. **No dissolution particle effect** -- Severity: **HIGH**
   - Spec requires ~100 particles scattering outward from the center code block during dissolution (frames 30-60 per cycle), with per-particle angle, distance, delay, and size properties, using `easeOutQuad` easing.
   - `CodeOutputMoldGlows` has zero particle effects.
   - `27-CodeRegenerates/CodeRegenerates.tsx:216-261` has a `DissolveEffect` with a 50x50 grid of particles (2500 particles), but it uses orange dissolve color (`COLORS.DISSOLVE_ORANGE = "#D9944A"`), not gray, and scatters from a mold cavity rectangle, not from a triangle centroid. It is not used in the closing section.
   - `18-PlasticRegenerates/ParticleSystem.tsx:31-50` has a 300-particle system with staggered delays and seeded random properties, closer to the spec's design, but also not used in the closing section.

5. **No regeneration particle effect** -- Severity: **HIGH**
   - Spec requires particles flowing inward from triangle edges/vertices toward center during regeneration (frames 60-90 per cycle), coalescing into a new code block with different line patterns, using `easeInCubic` easing.
   - No component in the codebase implements inward-flowing particles from triangle vertices. `27-CodeRegenerates/CodeRegenerates.tsx:264-360` has a `FluidSimulation` that flows liquid from a mold injection nozzle, but it is fluid-blob-based (ellipse + 12 particles), not a particle coalescence system, and does not reference triangle geometry.

6. **No code pattern variation between cycles (seeded RNG)** -- Severity: **HIGH**
   - Spec requires `generateCodePattern(seed)` using a seeded RNG to produce visibly different bar widths/counts for each cycle (v1, v2, v3), with version labels (`v1`, `v2`, `v3`) displayed.
   - `CodeOutputMoldGlows` uses a fixed set of five bars at hardcoded widths `[70, 55, 80, 45, 65]` (`CodeOutputMoldGlows.tsx:199`). No seeded generation, no variation, no version labels.

7. **No terminal loop at bottom center** -- Severity: **HIGH**
   - Spec requires a subtle terminal readout at center-bottom showing cycling commands with phase-aware coloring: `checkmark All tests passed` (green) -> `$ pdd generate parser...` (blue) -> `Regenerating parser.py...` (white) -> `$ pdd test parser -> checkmark` (green), repeating with each cycle. Font: JetBrains Mono, 13px.
   - `CodeOutputMoldGlows` has no terminal component whatsoever.
   - `27-CodeRegenerates/CodeRegenerates.tsx:6-53` has a `TerminalOverlay` positioned at bottom-right (`bottom: 30, right: 30`), not center-bottom. It shows progressive (non-cycling) lines: `$ pdd fix user_parser` -> `Regenerating code...` -> `All tests passing checkmark`. It is not used in the closing section.

8. **No green checkmark per cycle** -- Severity: **HIGH**
   - Spec requires a green checkmark (`#5AAA6E`) appearing at the code block's centroid position (left: 960, top: 520) during frames 90-120 of each cycle, with opacity interpolated as `[0, 1, 1, 0.5]` over `[90, 100, 115, 120]` and `easeOutBack` pop easing.
   - `CodeOutputMoldGlows` has no checkmark.
   - `27-CodeRegenerates/CodeRegenerates.tsx:363-406` has a `SuccessIndicator` with a checkmark, but it appears once (not per-cycle), is positioned top-right (`right: 40, top: 40`), and does not use `easeOutBack` easing (uses default linear interpolation).

9. **No final hold logic at frame 240-300** -- Severity: **MEDIUM**
   - Spec requires that after frame 240, the animation stops cycling and holds on the final version (v3) with the triangle steady, code present but unremarkable, and terminal showing final checkmark. `isFinalHold = frame >= 240` should suppress dissolution and regeneration.
   - Not applicable since the entire cycling mechanism is absent.

10. **Visual 4 slot duration too short** -- Severity: **MEDIUM**
    - Spec calls for ~10 seconds (300 frames at 30fps) for 2.5 full cycles.
    - Visual 4 in `ClosingSection.tsx` spans from frame 620 to frame 740 (120 frames = 4 seconds) per `S06-Closing/constants.ts:47-48`. Even the narration window (~20.7s to ~26.9s = ~6.2s = ~186 frames) is shorter than the 300 frames needed for 2.5 complete 4-second cycles.

11. **Easing functions not implemented** -- Severity: **MEDIUM**
    - Spec defines specific easing per animation element: dissolution particles use `easeOutQuad`, regeneration particles use `easeInCubic`, checkmark uses `easeOutBack`, and triangle background is constant (no easing).
    - None of these are implemented. `CodeOutputMoldGlows` uses `Easing.out(Easing.cubic)` and `Easing.out(Easing.quad)` for its own text/glow transitions, but these are unrelated to the spec's requirements. No `Easing.out(Easing.back)` call exists in either `38-CodeOutputMoldGlows/` or `27-CodeRegenerates/`.

12. **Wrong visual metaphor: mold/plastic instead of triangle/code** -- Severity: **HIGH**
    - Spec's core visual message is "THE CODE CHANGES, THE MOLD DOES NOT" expressed through a stable triangle (prompts + tests + grounding) with churning code at its center.
    - `CodeOutputMoldGlows` shows a glowing rectangular mold on the left and a static plastic block on the right. While it delivers a similar thematic message ("The code is just plastic. The mold is what matters."), it uses a completely different visual vocabulary (rectangular mold vs. triangle, side-by-side layout vs. centered-in-triangle, static vs. cycling).

---

### Notes

- **Architectural mismatch**: The `CodeOutputMoldGlows` component is better aligned with spec 6.6 ("Final Frame: The Mold Glows, The Code is Unremarkable") than 6.5. In `ClosingSection.tsx`, it is reused for both Visual 4 and Visual 5, suggesting that specs 6.5 and 6.6 were collapsed into a single implementation rather than being built as distinct compositions.

- **Existing building blocks not leveraged**: The codebase contains components conceptually similar to what the spec requires, but in different contexts and not wired into the closing section:
  - `18-PlasticRegenerates/ParticleSystem.tsx` -- 300-particle dissolve/regenerate with staggered delays, seeded random properties, and eased motion
  - `27-CodeRegenerates/CodeRegenerates.tsx` -- `DissolveEffect` (2500 grid particles), `FluidSimulation`, `SuccessIndicator`, `TerminalOverlay`
  - `37-ThreeComponents/ThreeComponents.tsx` -- Full triangle rendering with PROMPT/TESTS/GROUNDING vertices, edge gradients, centroid code block, and glow control

- **Implementation path**: A new `CodeRegenerationLoop` composition would need to integrate:
  (a) Cycle management with `cycleIndex`/`cycleFrame` modulo logic (120 frames per cycle)
  (b) A dimmed `ThreeComponents`-style triangle background at 60% opacity
  (c) A `CodeBlock` sub-component with `generateCodePattern(seed)` using seeded RNG
  (d) `DissolutionEffect` (~100 particles, `easeOutQuad`) and `RegenerationEffect` (~100 particles, `easeInCubic`) sub-components
  (e) A center-bottom `TerminalLoop` with phase-aware cycling text and color changes
  (f) A per-cycle green checkmark with `easeOutBack` pop easing
  (g) Final hold logic for frame >= 240
  After creation, `ClosingSection.tsx` Visual 4 would need to swap `CodeOutputMoldGlows` for the new composition, and the timing slot would need to be widened to accommodate 2.5 cycles (~300 frames).

---

### Resolution Status: UNRESOLVED

All 12 issues remain open. The spec requires a fundamentally different composition than what is currently rendered in the closing section's Visual 4 slot.
