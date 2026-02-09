# Audit: 13a Context Window Comparison

## Status: ISSUES FOUND

### Requirements Met

1. **Variant prop architecture**: The `ContextWindowComparison` component (`14a-ContextWindowComparison/ContextWindowComparison.tsx`) supports a `variant` prop with `'density'` value for Section 3.13a, keeping the efficiency variant intact for Section 1.14. This is a sound dual-use approach.

2. **Canvas and background**: Resolution is 1920x1080 (constants lines 14-15). Background is `#1a1a2e` (constants line 45, component line 200). Matches spec.

3. **Left window: Dense raw code (density variant)**: When `variant='density'`, the left window shows raw code lines from `CODE_PATTERNS` without the red/green "IRRELEVANT"/"relevant" overlays (component lines 342-346 -- overlays are gated on `variant === 'efficiency'`). Code is rendered in monospace `JetBrains Mono` at 10px (line 353), muted gray `#888888` (constants line 58). The `~1 module` label appears at bottom when fill exceeds 80% (lines 417-437).

4. **Right window: Ten module prompts (density variant)**: When `variant='density'`, the right panel renders `TEN_MODULE_PROMPTS` (lines 604-648). All ten modules match spec exactly: `user_parser`, `auth_handler`, `data_pipeline`, `payment_processor`, `email_service`, `cache_layer`, `api_gateway`, `search_index`, `notification_hub`, `audit_logger` (constants lines 191-201). Each module shows `## {name}` header in blue (#4A90D9) with description text in `#C0C0D0`.

5. **Both windows labeled 15K tokens**: In density variant, "Context Window (15K tokens)" labels appear above both windows (lines 220-253). The right counter target is set to `TOKEN_COUNTS.left` (15000) via line 103: `rightTokenTarget = variant === 'efficiency' ? TOKEN_COUNTS.right : TOKEN_COUNTS.left`.

6. **Panel titles**: Left labeled "15,000 tokens of code", right labeled "15,000 tokens of prompts" (lines 272, 290). Matches spec lines 21, 30.

7. **Knowledge multiplier message**: Density variant shows `Same tokens. 10x the system knowledge.` with "10x" in blue (#4A90D9) at fontSize 38 (lines 769-774). Matches spec lines 48-49, 258-260.

8. **Research citation**: Density variant shows "NL comments improved generation +41% (UC Berkeley, 2024) | Author-defined context, not machine-assembled" in muted #B0B0C0 at 70% opacity (lines 778-797). Matches spec lines 54-55, 271-280.

9. **Left window dimming**: In density variant, the left window dims to 0.6 opacity after the knowledge indicator appears (lines 161-168). Matches spec line 98 ("Left window slightly dimmed").

10. **Right window blue glow**: A pulsing blue glow appears on the right window border after knowledge indicator (lines 177-180). Matches spec line 97 ("Right window gently pulses").

11. **Module headers with blue glow**: Module name headers use `COLORS.PROMPT_BLUE` (#4A90D9) with `textShadow: 0 0 8px` (lines 629-631). Matches spec line 37 ("Blue glow (#4A90D9) around section headers").

12. **No "6.5x fewer tokens" badge in density variant**: The comparison badge is gated on `variant === 'efficiency'` (line 724). Correct -- density variant should not show this.

13. **Module appearance animation**: Each module appears with staggered `easeOutCubic` easing at 9-frame intervals (lines 605-613). Matches spec line 409 ("Prompt section appearances: easeOutCubic (staggered per module)").

14. **Window frame**: Both windows are identical size (760x480, constants lines 74-75). Windows have `#333333` border and `#1E1E2E` background. Matches spec lines 40-44.

### Issues Found

1. **Component NOT wired into S03 Part3 composition** -- Severity: HIGH
   - Spec says: This is Section 3.13a, meant to play during the narration "Remember the context window problem? Code is token-expensive..." at ~211-250s in the Part 3 timeline.
   - Implementation does: `Part3MoldThreeParts.tsx` Visual 14 (frames 6352-7491, corresponding to ~211-250s) uses `PromptGovernsCode` component, NOT `ContextWindowComparison` with `variant='density'`. The `ContextWindowComparison` component is not imported in `Part3MoldThreeParts.tsx` at all and is not referenced from any composition file outside its own directory.
   - Impact: The density variant code exists but is dead code -- it will never render in the actual Part 3 video output. The viewer sees `PromptGovernsCode` (a prompt-to-code ratio visualization) instead of the side-by-side context window density comparison.

2. **Window dimensions differ from spec** -- Severity: LOW
   - Spec says: Both windows should be 750x650px (spec line 41).
   - Implementation does: Windows are 760x480px (constants lines 74-75). The width is close (760 vs 750), but height is significantly shorter (480 vs 650). This makes the windows more horizontal than the spec's taller proportions.
   - Impact: The prompt modules may be more cramped vertically, and the visual impression of "density" in the left code window is reduced with fewer visible lines.

3. **Animation sequence timing differs significantly from spec** -- Severity: MEDIUM
   - Spec says (frames at 30fps): Left window builds 0-90, left labeled 90-120, right window builds 120-240, right labeled 240-300, knowledge multiplier 300-390, citation 390-480, hold 480-600. Total ~20 seconds (600 frames).
   - Implementation does: Establish 0-30, frames 30-60, left fill 60-150, right fill 90-180, counters 180-270, knowledge 270-330, hold 330-450. Total 15 seconds (450 frames). The component duration is 15s (constants line 11) vs spec's ~20s.
   - Impact: The animation is compressed into 15 seconds instead of 20. Left and right windows overlap in fill timing (left 60-150, right 90-180) rather than being sequential as spec requires (left 0-90, then right 120-240). The spec explicitly sequences right window building AFTER left window is labeled, creating a dramatic reveal; the implementation runs them nearly simultaneously.

4. **Left window missing scrollbar indicator** -- Severity: LOW
   - Spec says (lines 26, 323-333): Left window should have a scrollbar indicator showing more content exists.
   - Implementation does: No scrollbar is rendered in the density variant. The efficiency variant code has no scrollbar either.
   - Impact: Minor visual cue missing. The scrollbar helps reinforce the feeling that the code window is overflowing.

5. **Left window code not syntax-highlighted** -- Severity: LOW
   - Spec says (line 24): "Syntax highlighting in muted grays and dulled colors."
   - Implementation does: All code lines use a single color `#888888` (constants line 58). No differentiation between keywords, strings, comments, etc.
   - Impact: The wall of code appears as a flat gray block rather than having subtle syntax coloring. The spec wanted muted but present highlighting.

6. **Missing easing on several animations** -- Severity: LOW
   - Spec says (lines 407-414): Window frame draws use `easeOutCubic`, code flood-fill uses `easeInOutQuad`, labels use `easeOutCubic`, knowledge multiplier uses `easeOutBack` (slight overshoot), left dim uses `easeInQuad`.
   - Implementation does: Window frames use spring animation (line 60-64, acceptable alternative). Left code fill uses linear interpolation (lines 67-72, no easing specified). Knowledge multiplier uses `easeOutCubic` (line 147) rather than `easeOutBack`. Left dim uses linear interpolation (lines 163-166) rather than `easeInQuad`.
   - Impact: Subtle animation feel differences. The `easeOutBack` overshoot on the knowledge multiplier would have added emphasis.

7. **Right window background missing blue tint** -- Severity: LOW
   - Spec says (line 32): Right window container should have "slight blue tint background (#1E1E2E with blue cast)."
   - Implementation does: Right window uses the same `COLORS.WINDOW_BG` (#1E1E2E) as the left window (line 453). No blue tint differentiation until the glow appears later.
   - Impact: The immediate visual distinction between the two windows is reduced.

8. **"~10 modules" label timing tied to leftFillProgress** -- Severity: LOW
   - Spec says (lines 79-80): "~10 modules" label fades in at frame 240-300, after right window content is complete.
   - Implementation does (lines 651-672): The `~10 modules` label in the density variant is gated on `leftFillProgress > 0.8`, which depends on the LEFT fill timeline, not the RIGHT content completion. This is likely a copy-paste from the efficiency variant logic.
   - Impact: The label timing is coupled to the wrong animation progress, though in practice the timings may overlap enough to appear correct.

### Notes

The `ContextWindowComparison` density variant implementation is well-crafted and addresses the core visual spec requirements: identical 15K token windows, dense code vs. clean prompts, the "Same tokens. 10x the system knowledge." message, research citations, and appropriate visual emphasis. The module prompt data matches the spec exactly.

However, the critical issue is that **this component is not used in the Part 3 composition**. Visual 14 in `Part3MoldThreeParts.tsx` (covering the ~211-250s narration window where this spec maps) renders `PromptGovernsCode` instead. The density variant is effectively dead code. To fully resolve this spec, `ContextWindowComparison` with `variant='density'` needs to either replace `PromptGovernsCode` at Visual 14 or be added as a separate visual in the Part 3 sequence.

The secondary concern is the compressed 15-second duration versus the spec's 20-second timeline, and the overlapping left/right window build animations that lose the spec's deliberate sequential reveal.

**Files reviewed:**
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/14a-ContextWindowComparison/ContextWindowComparison.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/14a-ContextWindowComparison/constants.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/14a-ContextWindowComparison/index.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/Part3MoldThreeParts.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/constants.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/33-PromptGovernsCode/PromptGovernsCode.tsx`
