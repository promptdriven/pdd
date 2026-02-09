# Audit: Code Output Mold Glows

## Status: ISSUES FOUND

### Requirements Met

1. **Background color matches spec** -- Spec line 15 requires dark `#1a1a2e`. Implementation uses `COLORS.BACKGROUND` which resolves to `"#1a1a2e"` (`constants.ts` line 37, `CodeOutputMoldGlows.tsx` line 115). Exact match.

2. **Resolution matches spec** -- Spec line 14 requires 1920x1080. Constants define `CODE_OUTPUT_WIDTH = 1920` and `CODE_OUTPUT_HEIGHT = 1080` (`constants.ts` lines 8-9). Exact match.

3. **FPS is 30** -- `CODE_OUTPUT_FPS = 30` (`constants.ts` line 4). Matches the spec's frame-based timing which assumes 30fps.

4. **Three mold component colors represented** -- The `MoldInterior` component (`CodeOutputMoldGlows.tsx` lines 6-50) renders colored bars using blue `rgba(74, 144, 217, ...)` for PROMPT, amber `rgba(217, 148, 74, ...)` for TESTS, and green `rgba(90, 170, 110, ...)` for GROUNDING. These RGB values correspond to the spec's `#4A90D9`, `#D9944A`, and `#5AAA6E` (spec lines 232-243).

5. **Second message text matches spec** -- "The mold is what matters." at `CodeOutputMoldGlows.tsx` line 251 matches spec line 39 and spec line 64 exactly.

6. **Message color differentiation present** -- First message is gray `#888888` at font-size 32, font-weight 400 (`CodeOutputMoldGlows.tsx` lines 228-229). Second message is white `#FFFFFF` at font-size 36, font-weight 600 (`CodeOutputMoldGlows.tsx` lines 241-242). Spec lines 290-306 specify line 1 in gray `#888` at font-size 24 and line 2 in white `#FFF` bold at font-size 28. Colors and weight hierarchy match; font sizes differ (see Issues).

7. **Mold glow increases over time** -- `baseMoldGlow` interpolates from 0.4 to 1.0 over frames [0, 60] (`CodeOutputMoldGlows.tsx` lines 61-66). `finalGlowBoost` further amplifies from 1.0 to 1.4 when the second message appears at frames [210, 270] (`CodeOutputMoldGlows.tsx` lines 104-109). The combined `finalGlowIntensity` (`CodeOutputMoldGlows.tsx` line 112) provides the spec's concept of the mold growing brighter over time.

8. **Multi-layer glow on mold** -- Three separate radial-gradient glow layers using all three component colors (`CodeOutputMoldGlows.tsx` lines 128-153), plus a three-color boxShadow on the mold container (`CodeOutputMoldGlows.tsx` lines 168-172). Creates a visually rich glow effect as the spec intends.

9. **Two messages appear sequentially** -- `text1Opacity` animates at frames [120, 160] (`CodeOutputMoldGlows.tsx` lines 88-93) and `text2Opacity` at frames [210, 250] (`CodeOutputMoldGlows.tsx` lines 96-101). Messages are staggered as the spec requires.

10. **Second message has text shadow using component colors** -- `CodeOutputMoldGlows.tsx` lines 244-248 apply a textShadow with blue, amber, and green glows. This reinforces the three-component theme and enhances the "mold glowing" visual. Not in spec but a thematic enhancement.

11. **Breathing animation on mold** -- Sinusoidal oscillation at `CodeOutputMoldGlows.tsx` line 58: `Math.sin(frame * 0.035) * 0.1 + 0.9`. Not in spec but adds organic life to the mold, supporting the "persistent, valuable" quality described in spec line 29.

12. **GENERATED_CODE constant defined** -- The `parse_user_id` Python function is defined in `constants.ts` lines 48-55, matching the spec's code snippet at lines 198-205 character for character.

13. **Integration into Part 3 sequence** -- `CodeOutputMoldGlows` is used as Visual 19 in `S03-MoldThreeParts/Part3MoldThreeParts.tsx` line 183, starting at frame 8590 (~286.3s). The narration at that point (segment 39 in `S03-MoldThreeParts/constants.ts` line 48) reads "complete specification. The code is output, the mold is..." which aligns with the visual's theme.

14. **Props schema with zod validation** -- `CodeOutputMoldGlowsProps` defined with zod in `constants.ts` lines 58-66 with `showMessages` boolean prop defaulting to `true`.

### Issues Found

1. **First message text does not match spec** (MEDIUM)
   - **Spec says** (lines 38, 59): "The code is output."
   - **Implementation does** (`CodeOutputMoldGlows.tsx` line 234): "The code is just plastic."
   - The spec's messaging is "The code is output. The mold is what matters." The implementation changes the first line to a plastic/mold metaphor ("just plastic") which differs from the spec's direct statement.

2. **Duration is 10 seconds instead of spec's ~20 seconds** (HIGH)
   - **Spec says** (line 4): ~20 seconds duration. The animation sequence spans frames 0-600, which at 30fps is 20 seconds.
   - **Implementation does** (`constants.ts` lines 5-7): `CODE_OUTPUT_DURATION_SECONDS = 10`, yielding 300 total frames.
   - The spec defines five distinct phases across 20 seconds (0-4s, 4-10s, 10-14s, 14-18s, 18-20s). A 10-second composition cannot accommodate these phases. Additionally, in the S03 section context, only ~5.5 seconds are allocated (frames 8590 to 8756 per `S03-MoldThreeParts/constants.ts` lines 137-138), further compressing the visual.

3. **Five-phase animation sequence not implemented** (HIGH)
   - **Spec says** (lines 43-66): Five phases:
     - Phase 1 (0-4s): Code glows brightly with "success" feeling
     - Phase 2 (4-10s): Code glow fades, code becomes gray and ordinary
     - Phase 3 (10-14s): Mold components glow brighter, code clearly secondary
     - Phase 4 (14-18s): "The code is output." message, code dim, mold strong
     - Phase 5 (18-20s): "The mold is what matters." message, hold on glowing mold
   - **Implementation does**: Three overlapping phases: mold and plastic appear in 0-2s, messages at 4s and 7s. There is no initial code-glow phase, no code-glow-fading phase, and no distinct mold-prominence phase. The narrative arc of the value shift is structurally absent.

4. **Generated code not displayed as actual code** (HIGH)
   - **Spec says** (lines 163-210): A `<GeneratedCode>` component rendering the actual `parse_user_id` Python function in a `<pre>` tag with JetBrains Mono font at 12px, inside a styled container with a glowing border that fades. The code is readable text.
   - **Implementation does** (`CodeOutputMoldGlows.tsx` lines 180-212): An abstract "plastic" representation consisting of five horizontal gray bars of varying widths (70%, 55%, 80%, 45%, 65%) inside a gray rectangle. No actual code text is rendered.
   - The `GENERATED_CODE` constant is defined in `constants.ts` lines 48-55 but is never imported or used by the component. The code display was either removed during a redesign or never added.

5. **Three mold components not shown as separate labeled elements** (MEDIUM)
   - **Spec says** (lines 216-269): A `<MoldSystem>` containing three separate `<MiniComponent>` boxes labeled "PROMPT", "TESTS", and "GROUNDING" in a horizontal flexbox layout with individual glow effects and colored borders.
   - **Implementation does** (`CodeOutputMoldGlows.tsx` lines 6-50, 117-178): A single unified rectangular mold shape containing thin colored horizontal bars inside. No text labels are displayed. The three components are represented abstractly as colored lines rather than distinct labeled boxes.

6. **Code glow interpolation missing** (HIGH)
   - **Spec says** (lines 101-107): `codeGlow` interpolation over `[0, 120, 300]` mapping to `[1, 1, 0]` -- code holds full glow for 4 seconds, then fades to zero by 10 seconds.
   - **Implementation does**: No code glow interpolation exists. The "plastic" element has a fixed low opacity animation (`plasticOpacity` from 0 to 0.4 over frames [15, 50]) and no glow property at all.
   - The central visual story of the code starting bright and fading is not implemented.

7. **Code opacity dimming is inverted** (HIGH)
   - **Spec says** (lines 109-115): `codeOpacity` interpolation from `[0, 300]` to `[1, 0.5]` -- code starts fully visible at opacity 1 and dims to 0.5.
   - **Implementation does** (`CodeOutputMoldGlows.tsx` lines 80-85): `plasticOpacity` interpolates from 0 to 0.4 over frames [15, 50]. The element starts invisible and fades IN to a low opacity.
   - The behavior is the opposite of what the spec requires. The spec's key narrative beat is code starting strong and becoming secondary.

8. **Mold glow timing significantly compressed** (MEDIUM)
   - **Spec says** (lines 118-123): `moldGlow` interpolates over frames `[200, 400]` (6.7s to 13.3s) from 0.5 to 1.0 with `easeOutQuad`.
   - **Implementation does** (`CodeOutputMoldGlows.tsx` lines 61-66): `baseMoldGlow` interpolates over frames `[0, 60]` (0s to 2s) from 0.4 to 1.0 with `Easing.out(Easing.cubic)`.
   - The mold reaches full glow in 2 seconds instead of the spec's gradual increase over ~6.7 seconds. The mold glow also starts immediately rather than after the code has had time to shine first.

9. **Message timing compressed** (MEDIUM)
   - **Spec says** (lines 127-138): `message1Opacity` at frames `[420, 460]` (14-15.3s), `message2Opacity` at frames `[540, 580]` (18-19.3s).
   - **Implementation does**: `text1Opacity` at frames `[120, 160]` (4-5.3s), `text2Opacity` at frames `[210, 250]` (7-8.3s).
   - Messages appear at 4s and 7s instead of 14s and 18s due to the halved duration.

10. **Easing functions partially differ** (LOW)
    - **Spec says** (lines 312-315): `easeInQuad` for code glow fade and code opacity, `easeOutQuad` for mold glow increase, `easeOutCubic` for message fade.
    - **Implementation does**: `Easing.out(Easing.cubic)` for mold glow (spec says `easeOutQuad`), `Easing.out(Easing.quad)` for text1 and plasticOpacity, `Easing.out(Easing.cubic)` for text2 (matches spec for message 2). Code glow/opacity easings are N/A since those interpolations do not exist.

11. **Value hierarchy visual shift not achieved** (HIGH)
    - **Spec says** (lines 68-93): Clear visual design showing code initially prominent and glowing at 0-4s, then reversing to mold glowing and code dim at 10-14s. The ASCII art diagram explicitly shows the transformation.
    - **Implementation does**: Both elements appear at low intensity from the start. The mold glows from frame 0; the plastic element fades in to 0.4 opacity and stays there. There is no reversal, no shift, no moment where the viewer sees code as initially valuable and then watches that value transfer to the mold.
    - This is the conceptual climax of Part 3 (spec line 333). The value hierarchy shift is the central visual message.

12. **Message font sizes differ from spec** (LOW)
    - **Spec says** (lines 290, 298): Line 1 at `fontSize: 24`, line 2 at `fontSize: 28`.
    - **Implementation does** (`CodeOutputMoldGlows.tsx` lines 228, 241): Line 1 at `fontSize: 32`, line 2 at `fontSize: 36`.
    - Both are 8px larger than spec. The relative hierarchy (line 2 larger than line 1) is preserved.

13. **showMessages prop unused** (LOW)
    - The `showMessages` prop is destructured at `CodeOutputMoldGlows.tsx` line 53 but is never referenced in the JSX. The messages always render regardless of prop value. The prop exists in the schema (`constants.ts` line 59) but has no effect.

14. **Message positioning differs from spec** (LOW)
    - **Spec says** (lines 283-288): Messages positioned at `bottom: 60`, centered via `left: '50%'` and `transform: 'translateX(-50%)'`.
    - **Implementation does** (`CodeOutputMoldGlows.tsx` lines 216-222): Messages positioned at `bottom: 140`, centered via `left: 0; right: 0; textAlign: center`.
    - Both achieve centering but the vertical position is 80px higher than spec. Minor layout difference.

### Notes

- The implementation has taken a deliberate artistic departure from the spec by adopting a "mold and plastic" metaphor with abstract shapes rather than the spec's approach of showing readable code alongside labeled mold components. The spec explicitly shows real code (the `parse_user_id` function) as a readable element that glows and fades, while the implementation shows abstract gray bars representing "plastic output."

- The `GENERATED_CODE` constant in `constants.ts` lines 48-55 contains the full `parse_user_id` function matching the spec, but it is never imported or used in `CodeOutputMoldGlows.tsx`. This is dead code.

- The `BEATS` comments in `constants.ts` lines 12-17 describe a different 6-phase timing structure than either the spec or the actual interpolation values. The comments reference phases like "Mold and plastic appear" (0-2s), "Mold glow intensifies" (2-4s), "First text line" (4-6s), "THE BEAT" (6-7s), "Second text line" (7-9s), and "Final hold" (9-10s). This confirms an intentional redesign to a 10-second, mold-and-plastic narrative rather than the spec's 20-second, code-glows-then-fades narrative.

- Within the S03-MoldThreeParts sequence, this visual is allocated approximately 5.5 seconds (frame 8590 to 8756, or 286.34s to 291.86s per `S03-MoldThreeParts/constants.ts` lines 137-138). At that duration, even the 10-second standalone composition would be cut off at around frame 166, meaning `text2Opacity` (starting at frame 210) would never be reached during Part 3 playback. The second message "The mold is what matters." would not appear in the section context.

- Key implementation files:
  - `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/38-CodeOutputMoldGlows/CodeOutputMoldGlows.tsx` (main component, 257 lines)
  - `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/38-CodeOutputMoldGlows/constants.ts` (constants and props, 67 lines)
  - `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/38-CodeOutputMoldGlows/index.ts` (barrel export)
  - `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/Part3MoldThreeParts.tsx` (section integration, Visual 19 at line 183)
  - `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/constants.ts` (section timing, lines 137-138)

- Summary: 6 high-severity issues, 4 medium-severity issues, and 4 low-severity issues found. The implementation achieves the broad thematic goal that the mold is more important than the code output, but it does not implement the spec's specific visual narrative: code initially glows brightly as "just generated" output, the glow fades to reveal the code as disposable, the mold grows in prominence, and the viewer sees a clear value shift. The implementation instead shows abstract shapes appearing simultaneously at low intensity with no reversal or shift.

## Resolution Status: UNRESOLVED
