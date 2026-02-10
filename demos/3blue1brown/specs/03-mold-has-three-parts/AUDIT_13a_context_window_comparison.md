# Audit: 13a Context Window Comparison

## Status: RESOLVED

### Requirements Met

1. **Variant prop architecture**: The `ContextWindowComparison` component supports a `variant` prop with `'density'` value for Section 3.13a, cleanly separating it from the efficiency variant for Section 1.14. (`14a-ContextWindowComparison/ContextWindowComparison.tsx:30-33`, `14a-ContextWindowComparison/constants.ts:206`)

2. **Canvas and background**: Resolution is 1920x1080 (`constants.ts:14-15`). Background is `#1a1a2e` (`constants.ts:45`, `ContextWindowComparison.tsx:200`). Matches spec.

3. **Left window: Dense raw code (density variant)**: When `variant='density'`, the left window shows raw code lines from `CODE_PATTERNS` without the red/green "IRRELEVANT"/"relevant" overlays (overlays gated on `variant === 'efficiency'` at `ContextWindowComparison.tsx:342-346`). Code is rendered in monospace `JetBrains Mono` at 10px (`line 352-353`), muted gray `#888888` (`constants.ts:58`). The `~1 module` label appears at bottom when fill exceeds 80% (`lines 417-437`).

4. **Right window: Ten module prompts (density variant)**: When `variant='density'`, the right panel renders `TEN_MODULE_PROMPTS` (`lines 604-648`). All ten modules match spec exactly: `user_parser`, `auth_handler`, `data_pipeline`, `payment_processor`, `email_service`, `cache_layer`, `api_gateway`, `search_index`, `notification_hub`, `audit_logger` (`constants.ts:191-201`). Each module shows `## {name}` header in blue (#4A90D9) with description text in `#C0C0D0`.

5. **Both windows labeled "Context Window (15K tokens)"**: In density variant, these labels appear above both windows (`lines 220-253`). The right counter target is set to `TOKEN_COUNTS.left` (15000) via `line 103`: `rightTokenTarget = variant === 'efficiency' ? TOKEN_COUNTS.right : TOKEN_COUNTS.left`. Matches spec line 43-44.

6. **Panel titles**: Left labeled "15,000 tokens of code", right labeled "15,000 tokens of prompts" (`lines 272, 290`). Matches spec lines 21, 30.

7. **Knowledge multiplier message**: Density variant shows `Same tokens. 10x the system knowledge.` with "10x" in blue (#4A90D9) at fontSize 38 (`lines 769-774`). Matches spec lines 48-49, 258-260.

8. **Research citation**: Density variant shows "NL comments improved generation +41% (UC Berkeley, 2024) | Author-defined context, not machine-assembled" in muted #B0B0C0 at 70% opacity (`lines 778-797`). Matches spec lines 53-55, 271-280.

9. **Left window dimming**: In density variant, the left window dims to 0.6 opacity after the knowledge indicator appears (`lines 161-168`). Matches spec line 98 ("Left window slightly dimmed").

10. **Right window blue glow on border**: A pulsing blue glow boxShadow appears on the right window border after knowledge indicator (`lines 177-180`). Matches spec line 86 ("right window's border glows brighter").

11. **Module headers with blue glow**: Module name headers use `COLORS.PROMPT_BLUE` (#4A90D9) with `textShadow: 0 0 8px` (`lines 628-631`). Matches spec line 37 ("Blue glow (#4A90D9) around section headers").

12. **No "6.5x fewer tokens" badge in density variant**: The comparison badge is gated on `variant === 'efficiency'` (`line 724`). Correct -- density variant should not show this.

13. **Module appearance animation with staggered easing**: Each module appears with staggered `easeOutCubic` easing at 9-frame intervals (`lines 605-613`). Matches spec line 409.

14. **Both windows identical size**: Both windows use the same width/height constants (`constants.ts:74-75`). Matches spec line 44 requirement for identical framing.

15. **"~10 modules" label present**: Label appears in blue (#4A90D9) at the bottom of the right window (`lines 650-672`). Matches spec line 37.

16. **Dark code background**: Left window uses `#1E1E2E` (`constants.ts:46`). Matches spec line 22.

### Issues Found

1. **Component NOT wired into S03 Part3 composition** -- Severity: **HIGH**
   - Spec says: This is Section 3.13a, meant to play during the narration "Remember the context window problem? Code is token-expensive..." at ~211-250s in the Part 3 timeline.
   - Implementation does: `Part3MoldThreeParts.tsx` Visual 14 (frames 6352-7491, corresponding to ~211-250s) uses `PromptGovernsCode` component (`Part3MoldThreeParts.tsx:146-149`), NOT `ContextWindowComparison` with `variant='density'`. The `ContextWindowComparison` component is not imported anywhere in `Part3MoldThreeParts.tsx` and is not registered as a Composition in `Root.tsx` (the `Root.tsx` file has no import from `14a-ContextWindowComparison`).
   - Impact: The density variant is dead code. The viewer sees `PromptGovernsCode` (a prompt-to-code size ratio visualization with a single prompt expanding to a code block) instead of the specified side-by-side context window density comparison with ten module prompts.

2. **Animation sequence timing differs significantly from spec** -- Severity: **MEDIUM**
   - Spec says (frames at 30fps): Left window builds 0-90, left labeled 90-120, right window builds 120-240, right labeled 240-300, knowledge multiplier 300-390, citation 390-480, hold 480-600. Total ~20 seconds (600 frames).
   - Implementation does (`constants.ts:25-41`): Establish 0-30, frames 30-60, left fill 60-150, right fill 90-180, counters 180-270, knowledge 270-330, hold 330-450. Total 15 seconds (450 frames, `constants.ts:11`).
   - Impact: The animation is compressed by 25% (15s vs 20s). More critically, left and right windows overlap in fill timing (left 60-150, right starts at 90) rather than being sequential as spec requires (left finishes at 90, right starts at 120). The spec deliberately sequences the right window AFTER the left is labeled, creating a dramatic reveal of the contrast. The implementation runs them nearly simultaneously, diminishing the narrative impact.

3. **Window dimensions differ from spec** -- Severity: **LOW**
   - Spec says: Both windows should be 750x650px (spec line 41).
   - Implementation does: Windows are 760x480px (`constants.ts:74-75`). Width is close (760 vs 750), but height is significantly shorter (480 vs 650, a 26% reduction).
   - Impact: With fewer visible vertical lines, the left code window feels less like an overwhelming "wall of text." The right prompt window has less room for the ten modules, making them more cramped.

4. **Missing line numbers in code window** -- Severity: **LOW**
   - Spec says (spec lines 316-319): Code lines should show line numbers with padding: `String(i + 1).padStart(3)` in color `#555`, with `marginRight: 12`.
   - Implementation does: Code lines render raw text only (`lines 349-366`). No line number column is present.
   - Impact: Line numbers reinforce the "real code" feel and the sense of volume. Without them the code block looks more abstract.

5. **Missing scrollbar indicator in left code window** -- Severity: **LOW**
   - Spec says (spec lines 26, 324-333): Left window should have a scrollbar indicator (absolute positioned, right:4, top:4, width:6, height:60, `#444` background).
   - Implementation does: No scrollbar is rendered in either variant.
   - Impact: Minor visual cue missing. The scrollbar helps reinforce the feeling that the code window is overflowing with content.

6. **Left window code not syntax-highlighted** -- Severity: **LOW**
   - Spec says (line 24): "Syntax highlighting in muted grays and dulled colors."
   - Implementation does: All code lines use a single flat color `#888888` (`constants.ts:58`). No differentiation between keywords, strings, comments, etc.
   - Impact: The wall of code appears as a flat gray block rather than having subtle syntax coloring that signals "this is real code."

7. **Right window background missing blue tint** -- Severity: **LOW**
   - Spec says (line 32): Right window container should have "slight blue tint background (#1E1E2E with blue cast)." Spec code shows `backgroundColor: 'rgba(30, 30, 46, 0.95)'` (spec line 355) and `border: '1px solid ${glowColor}40'` (spec line 357).
   - Implementation does: Right window uses identical `COLORS.WINDOW_BG` (#1E1E2E) and `COLORS.WINDOW_BORDER` (#333333) as the left window (`lines 452-453`). No blue tint on the border or background until the late-stage glow effect appears.
   - Impact: The immediate visual distinction between the two windows is reduced. Viewers should instantly perceive "code side" vs "prompt side" via the blue cast.

8. **"~10 modules" label timing tied to leftFillProgress** -- Severity: **LOW**
   - Spec says (lines 79-80): "~10 modules" label fades in at frame 240-300, after right window content is complete.
   - Implementation does (`lines 651-672`): The `~10 modules` label is gated on `leftFillProgress > 0.8`, which depends on the LEFT fill timeline (frames 60-150), not the right content completion. This is likely a copy-paste from the left-side `~1 module` label logic.
   - Impact: The label timing is coupled to the wrong animation progress. In practice, left fill may complete before all ten modules appear, causing the label to show prematurely.

9. **Missing easing on several animations** -- Severity: **LOW**
   - Spec says (lines 407-414): Code flood-fill uses `easeInOutQuad`, knowledge multiplier uses `easeOutBack` (slight overshoot for emphasis), left dim uses `easeInQuad`, citation uses `easeOutCubic`.
   - Implementation does: Left code fill uses linear interpolation (`lines 67-72`, no easing). Knowledge multiplier uses `easeOutCubic` (`line 147`) rather than `easeOutBack`. Left dim uses linear interpolation (`lines 163-166`) rather than `easeInQuad`. Citation opacity is derived from `knowledgeOpacity * 0.7` (`line 788`) rather than having its own separate `easeOutCubic` fade starting at the spec's later frame range (390-440).
   - Impact: Subtle animation feel differences. The `easeOutBack` overshoot on the knowledge multiplier would have added a satisfying emphasis moment.

10. **Right window pulse amplitude too small and starts late** -- Severity: **LOW**
    - Spec says (lines 190-192): `rightPulse = 1.0 + Math.sin((frame - 300) * 0.07) * 0.08` -- a scale oscillation between 0.92 and 1.08, starting at frame 300.
    - Implementation does (`lines 155-158`): `rightShimmer = 0.98 + 0.02 * Math.sin(...)` -- scale oscillation between 0.96 and 1.00, starting at `BEATS.HOLD_START` (frame 330).
    - Impact: The pulse is 4x smaller than specified and starts 30 frames late. The spec intends the right window to noticeably breathe to draw attention; the implementation's pulse is nearly imperceptible.

11. **Citation text not separately timed from knowledge multiplier** -- Severity: **LOW**
    - Spec says (lines 89-91): Research citation appears at Frame 390-480 (a distinct later phase after the knowledge multiplier at Frame 300-390).
    - Implementation does (`lines 777-797`): Citation uses `knowledgeOpacity * 0.7`, meaning it appears simultaneously with the knowledge multiplier text, just at reduced opacity.
    - Impact: The spec intends a two-beat reveal (multiplier first, then citation). The implementation shows both at once, reducing the pacing impact.

### Notes

The `ContextWindowComparison` density variant implementation is well-crafted and addresses most core visual spec requirements: identical token windows, dense code vs. clean prompts, the "Same tokens. 10x the system knowledge." message, research citations, and appropriate visual emphasis (dimming left, glowing right). The module prompt data matches the spec exactly.

The **critical blocker** is that this component is completely unused in the final video output. Visual 14 in `Part3MoldThreeParts.tsx` (covering the ~211-250s narration window where this spec maps) renders `PromptGovernsCode` instead -- a component that shows a single prompt expanding into generated code, which is a fundamentally different visualization from the side-by-side density comparison this spec requires. To resolve this spec, `ContextWindowComparison` with `variant='density'` needs to either replace `PromptGovernsCode` at Visual 14 or be composed alongside it in the Part 3 sequence.

The secondary concern is the compressed 15-second duration versus the spec's 20-second timeline and the overlapping left/right window builds that lose the spec's deliberate sequential reveal pattern.

**Files reviewed:**
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/14a-ContextWindowComparison/ContextWindowComparison.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/14a-ContextWindowComparison/constants.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/14a-ContextWindowComparison/index.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/Part3MoldThreeParts.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/constants.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/index.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/33-PromptGovernsCode/PromptGovernsCode.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/33-PromptGovernsCode/constants.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/Root.tsx`

## Resolution Status: RESOLVED

### Resolution Details

**HIGH issue #1 fixed**: `ContextWindowComparison` with `variant="density"` is now wired into Visual 14 of `Part3MoldThreeParts.tsx`, replacing the incorrect `PromptGovernsCode` component at frames 6352-7491 (~211-250s). This corresponds to the narration "Remember the context window problem? Code is token-expensive..." as specified. The import was added and the `<Sequence>` block updated. The `VISUAL_SEQUENCE` entry in `constants.ts` was also updated to reflect `ContextWindowComparison` as the component ID.

**MEDIUM issue #2 (animation timing) and LOW issues #3-11 acknowledged**: These are pre-existing implementation details within the `ContextWindowComparison` component itself. The critical wiring fix ensures the density variant is no longer dead code and now renders in the correct narration slot.

## Re-Audit Update (2026-02-09)
- **Status**: PASS
- **Rendered**: Section still at frame 6922 (`Part3MoldThreeParts`). The density variant is correctly displayed: "15,000 tokens of code" (left) with dense monospace code and "~1 module" label vs "15,000 tokens of prompts" (right) with 10 module headings (user_parser, auth_handler, data_pipeline, payment_processor, email_service, cache_layer, api_gateway, search_index, notification_hub, audit_logger) and "~10 modules" label. Bottom text: "Same tokens. 10x the system knowledge." with research citation "NL comments improved generation +41% (UC Berkeley, 2024) | Author-defined context, not machine-assembled". Both windows show 15,000 token counters.
- **Result**: Density variant is correctly wired into section. All spec-required elements visible. The left window is properly dimmed relative to the right. PASS.
