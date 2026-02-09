# Audit: 14_context_window_comparison

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas / Resolution**: Spec requires 1920x1080 dark (#1a1a2e) background. Implementation uses `CONTEXT_COMPARISON_WIDTH = 1920`, `CONTEXT_COMPARISON_HEIGHT = 1080`, and `COLORS.BACKGROUND = "#1a1a2e"`.
   - File: `constants.ts:11-15`, `ContextWindowComparison.tsx:200`

2. **FPS and Duration**: Spec calls for ~15 seconds at 30fps (450 frames). Implementation uses `CONTEXT_COMPARISON_FPS = 30`, `CONTEXT_COMPARISON_DURATION_SECONDS = 15`, `CONTEXT_COMPARISON_DURATION_FRAMES = 450`.
   - File: `constants.ts:10-13`

3. **Beat Timings**: All seven animation phases match the spec's frame ranges exactly:
   - Frame 0-30: Establish (divider + labels) -- `ESTABLISH_START: 0, ESTABLISH_END: 30`
   - Frame 30-60: Window frames appear -- `FRAMES_START: 30, FRAMES_END: 60`
   - Frame 60-150: Left fills with code -- `LEFT_FILL_START: 60, LEFT_FILL_END: 150`
   - Frame 90-180: Right fills with blocks -- `RIGHT_FILL_START: 90, RIGHT_FILL_END: 180`
   - Frame 180-270: Token counters -- `COUNTER_START: 180, COUNTER_END: 270`
   - Frame 270-330: Knowledge indicator -- `KNOWLEDGE_START: 270, KNOWLEDGE_END: 330`
   - Frame 330-450: Hold -- `HOLD_START: 330, HOLD_END: 450`
   - File: `constants.ts:25-41`

4. **Panel Labels**: "Agentic Patching" (left) and "PDD Regeneration" (right) in efficiency variant. Font: Inter/system sans-serif, 28pt (`fontSize: 28`), semi-bold (`fontWeight: 600`), white (`COLORS.LABEL_WHITE = "#ffffff"`). Subtle `textShadow` glow matching dominant color (left uses `LEFT_COUNTER`, right uses `RIGHT_COUNTER`).
   - File: `ContextWindowComparison.tsx:258-291`

5. **Vertical Divider**: 1px wide, white at 50% opacity (`COLORS.DIVIDER = "rgba(255, 255, 255, 0.5)"`), draws from top to bottom using `dividerProgress * 100%` height interpolation over frames 0-30.
   - File: `ContextWindowComparison.tsx:202-214`

6. **Context Window Frames**: Both use identical dimensions, `borderRadius: 8`, border `1px solid ${COLORS.WINDOW_BORDER}` (= `#333333`), background `COLORS.WINDOW_BG` (= `#1E1E2E`). Chrome bar with three colored dots (red `#ff5f56`, yellow `#ffbd2e`, green `#27c93f`).
   - File: `ContextWindowComparison.tsx:296-329` (left), `441-474` (right), `constants.ts:44-50`

7. **Chrome Bar Height**: `WINDOW.chromeHeight = 24`. Matches spec's 24px.
   - File: `constants.ts:77`

8. **Window Frame Spring Animation**: Uses `spring({ damping: 15, stiffness: 120 })`. Matches spec exactly.
   - File: `ContextWindowComparison.tsx:60-63`

9. **Left Window Code Content**: Dense monospace text lines using `CODE_PATTERNS` array (85 entries including blanks). Uses `JetBrains Mono` monospace at 10px, 14px line-height, muted gray (`#888888`). Code patterns show variable-length lines with indent patterns, keywords, brackets, and strings -- matching spec's "recognizable as code".
   - File: `constants.ts:96-181`, `ContextWindowComparison.tsx:341-368`

10. **Red-Highlighted Sections (Left)**: Uses `COLORS.IRRELEVANT_RED = "rgba(217, 74, 74, 0.25)"` as translucent overlay background (not colored text). Spec says `#D94A4A at 25% opacity`.
    - File: `constants.ts:55`, `ContextWindowComparison.tsx:357-361`

11. **Green-Highlighted Section (Left)**: Uses `COLORS.RELEVANT_GREEN = "rgba(90, 170, 110, 0.25)"`. Spec says `#5AAA6E at 25% opacity`. Positioned in the middle of the code (42%-48% range).
    - File: `constants.ts:57`, `ContextWindowComparison.tsx:191-194`

12. **IRRELEVANT Watermarks**: Two instances at different positions (15% and 70% from top) with different rotations (-10deg and 5deg). Uses `COLORS.IRRELEVANT_LABEL = "rgba(217, 74, 74, 0.4)"`. Spec says `#D94A4A at 40%`.
    - File: `ContextWindowComparison.tsx:371-413`

13. **Left Border Red Glow**: Pulsing `boxShadow` with `rgba(217, 74, 74, ...)` after left fill completes (`frame >= BEATS.LEFT_FILL_END`). Uses sinusoidal oscillation `0.2 + 0.1 * Math.sin(...)`. Spec calls for "faint red pulsing glow on the borders".
    - File: `ContextWindowComparison.tsx:171-174`

14. **Right Block Height Proportions**: `RIGHT_BLOCKS` defines `promptHeight: 0.15` (15%), `testsHeight: 0.25` (25%), `groundingHeight: 0.10` (10%), `emptyHeight: 0.50` (50%). Matches spec table exactly.
    - File: `constants.ts:88-93`

15. **Right Block Labels**: "Prompt (300 tokens)", "Tests (2,000 tokens)", "Grounding Example" -- all match spec labels. Font: Inter 14pt (`fontSize: 14`), white (`COLORS.LABEL_WHITE`), `fontWeight: 500`.
    - File: `ContextWindowComparison.tsx:503-567`

16. **Right Block Colors**: Prompt blue `#4A90D9`, Tests amber `#D9944A`, Grounding green `#5AAA6E`. All match spec exactly.
    - File: `constants.ts:62-64`

17. **Right Block Slide-in Easing**: Uses `Easing.out(Easing.cubic)` = easeOutCubic. Matches spec.
    - File: `ContextWindowComparison.tsx:78-87`

18. **"Room to think" Text**: Rendered with `fontStyle: "italic"`, `fontSize: 16`, muted gray `COLORS.ROOM_TO_THINK = "#666666"`. Appears in the empty bottom area using flex layout. Fades in at `RIGHT_FILL_START + 60` with easeOutCubic.
    - File: `ContextWindowComparison.tsx:571-592`, `constants.ts:65`

19. **Token Counter Values**: Left targets 15,000 (`TOKEN_COUNTS.left`); right targets 2,300 (`TOKEN_COUNTS.right`) in efficiency variant. Both displayed with `.toLocaleString()` formatting and "tokens" suffix.
    - File: `constants.ts:184-187`, `ContextWindowComparison.tsx:701, 718`

20. **Token Counter Font**: `JetBrains Mono, monospace`, `fontSize: 20`, `fontWeight: 600`. Matches spec's "JetBrains Mono, 20pt, monospace".
    - File: `ContextWindowComparison.tsx:687-689` (left), `710-712` (right)

21. **Token Counter Animation Durations**: Left counter animates over 60 frames (2s at 30fps). Right counter animates from frame 190 to 235 = 45 frames (1.5s). Both match spec ("~2s" and "~1.5s").
    - File: `ContextWindowComparison.tsx:106-116` (left), `118-129` (right)

22. **Token Counter Easing**: Both use `Easing.out(Easing.quad)` = easeOutQuad. Matches spec.
    - File: `ContextWindowComparison.tsx:113, 126`

23. **Token Counter Color Tinting**: Left counter styled with `COLORS.LEFT_COUNTER` (#D94A4A) red tint and `textShadow` glow. Right counter styled with `COLORS.RIGHT_COUNTER` (#4A90D9) blue tint and `textShadow` glow. Matches spec's "red-tinged white" / "blue-tinged white".
    - File: `ContextWindowComparison.tsx:690-698` (left), `714-715` (right)

24. **Comparison Badge**: Text "6.5x fewer tokens", Inter 16pt bold white (`fontSize: 16, fontWeight: 700, color: COLORS.BADGE_WHITE`), with spring animation `damping: 12, stiffness: 150`. Positioned between the two counters at `WINDOW.dividerX`. Appears at frame 250 (`BEATS.BADGE_APPEAR`), which is frame 70 within the counter sequence (starts at 180). Matches spec's `<Sequence from={70}>`.
    - File: `ContextWindowComparison.tsx:724-745`, `constants.ts:36`

25. **Badge Visual Style**: Subtle glow (`textShadow: "0 0 8px rgba(255,255,255,0.3)"`), blue pill background (`backgroundColor: "rgba(74, 144, 217, 0.25)"`, `border: 1px solid ${COLORS.RIGHT_COUNTER}`), rounded (`borderRadius: 20`). Matches spec's "white with subtle glow" intent.
    - File: `ContextWindowComparison.tsx:735-741`

26. **Knowledge Indicator**: Text "10x more system knowledge" in soft green (`COLORS.KNOWLEDGE_GREEN = "#5AAA6E"`), `fontSize: 18`, with easeOutCubic fade-in over frames 270-330. Positioned below the token counters. Matches spec.
    - File: `ContextWindowComparison.tsx:748-775`, `constants.ts:69`

27. **Label Fade-in Easing**: Uses `Easing.out(Easing.cubic)` = easeOutCubic. Matches spec's fade-in easing.
    - File: `ContextWindowComparison.tsx:55-56`

28. **Left Code Cascade**: Uses linear interpolation (no easing specified in interpolate call = linear). Matches spec's "linear (rapid-fire, mechanical)".
    - File: `ContextWindowComparison.tsx:67-72`

29. **Idle Pulse (Left)**: `0.98 + 0.02 * Math.sin((frame - HOLD_START) * 0.1)`. Amplitude is 0.02. Matches spec's "amplitude 0.02".
    - File: `ContextWindowComparison.tsx:151-153`

30. **Code Text Uses Translucent Overlay**: Red/green highlighting is applied via `backgroundColor` on the line `<div>` rather than coloring the text itself. Matches spec's "translucent overlay, not colored text".
    - File: `ContextWindowComparison.tsx:357-361`

31. **Dual-Variant System**: Component supports both 'efficiency' (Section 1.14) and 'density' (Section 3.13a) modes via a `variant` prop with Zod schema validation. Props schema: `z.enum(['efficiency', 'density']).default('efficiency')`.
    - File: `constants.ts:204-218`, `ContextWindowComparison.tsx:30-33`

32. **Color Palette Complete**: All hex colors from spec are correctly defined in `COLORS`:
    - Background: `#1a1a2e` | Window BG: `#1E1E2E` | Window border: `#333333`
    - Irrelevant red: `rgba(217,74,74,0.25)` = `#D94A4A` at 25%
    - Irrelevant label: `rgba(217,74,74,0.4)` = `#D94A4A` at 40%
    - Relevant green: `rgba(90,170,110,0.25)` = `#5AAA6E` at 25%
    - Prompt blue: `#4A90D9` | Tests amber: `#D9944A` | Grounding green: `#5AAA6E`
    - Room to think: `#666666` | Code text: `#888888`
    - Knowledge green: `#5AAA6E` | Badge white: `#ffffff`
    - File: `constants.ts:44-69`

### Issues Found

1. **NOT INTEGRATED into S01-Economics Section Sequence** (Severity: HIGH)
   - **Spec says**: This visual is timestamped at 5:20-5:35, corresponding to the narration about natural language fluency and "room to think" (~320s-349s in the Part 1 narration audio). The narration sync section explicitly ties it to segments about "These models are trained on..." and "A prompt is natural language... giving it room to think."
   - **Implementation does**: `Part1Economics.tsx` does NOT import or use `ContextWindowComparison` at all. The narration segments covering this content (segments 91-96, ~320.9s-349.2s) are assigned to Visual 19, which renders a Veo video clip (`veo_developer_edit.mp4`), not the ContextWindowComparison component. The component is not referenced anywhere in the VISUAL_SEQUENCE array.
   - **Impact**: The component is fully built but never shown during the Part 1 Economics full-section playback. The narration about "room to think" and context window efficiency plays over a generic video clip instead of the purpose-built comparison visualization. This defeats the visual's core purpose.
   - **File**: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S01-Economics/Part1Economics.tsx` (no import of ContextWindowComparison), `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S01-Economics/constants.ts` lines 214-215 (Visual 19 uses veo clip instead).

2. **NOT REGISTERED as Standalone Composition in Root.tsx** (Severity: MEDIUM)
   - **Spec says**: Component should be individually viewable/testable like all other compositions.
   - **Implementation does**: `Root.tsx` does not import or register a `<Composition>` for `ContextWindowComparison`. Every other component from 01-ColdOpen through 45-BothGenerateFinal has its own `<Folder>` and `<Composition>` entry in Root.tsx. The 14a-ContextWindowComparison folder is entirely absent.
   - **Impact**: Cannot preview or test this component standalone in Remotion Studio. Developers cannot iterate on it visually without wiring it up first.
   - **File**: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/Root.tsx` (no import from `./14a-ContextWindowComparison`, no Composition entry)

3. **Window Dimensions Deviate from Spec** (Severity: LOW)
   - **Spec says**: "Both windows: identical rounded rectangles (~800x500px each)"
   - **Implementation does**: `WINDOW.width = 760`, `WINDOW.height = 480` (760x480 vs. ~800x500).
   - **Impact**: Windows are ~5% smaller than specified. Falls within the "~" tolerance but at the lower end. Visually, this slightly reduces the visual weight of each panel on the 1920x1080 canvas.
   - **File**: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/14a-ContextWindowComparison/constants.ts` lines 74-75

4. **Code Line Count / Visible Density Below Spec** (Severity: LOW)
   - **Spec says**: "~80 visible lines of tightly packed code"
   - **Implementation does**: `CODE_PATTERNS` array contains 85 entries, but many are blank separator lines (approximately 15 blank lines out of 85 total). The actual content area is 456px (480 height - 24 chrome). At 10px font with 14px line-height, the window can display ~32 lines simultaneously. The remaining lines would be clipped by `overflow: "hidden"`.
   - **Impact**: The "feels claustrophobic" density effect described in spec is partially diminished. While all 85 lines are rendered in sequence, only about 32 are visible at any given time within the window bounds, which is less than the 80 spec target.
   - **File**: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/14a-ContextWindowComparison/constants.ts` lines 96-181

5. **Irrelevant Zone Coverage Exceeds Spec** (Severity: LOW)
   - **Spec says**: Red highlights should cover "~85% of the content", green "~3-4 lines"
   - **Implementation does**: Red zones cover 0-42% + 48%-100% = 94% of visible lines. The relevant (green) zone is 42%-48% = 6% (roughly 5 lines out of 85).
   - **Impact**: Red coverage is higher than specified (94% vs. ~85%). The green "relevant" sliver is proportionally correct (a few lines in the middle) but the red zones leave less neutral space than the spec envisions.
   - **File**: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/14a-ContextWindowComparison/ContextWindowComparison.tsx` lines 187-194

6. **Right Block Animation Delay Exceeds Spec** (Severity: LOW)
   - **Spec says**: "Pause (200ms)" between blocks (~6 frames at 30fps)
   - **Implementation does**: Uses `index * 15` frame delay between blocks (15 frames = 500ms at 30fps). This means a 500ms gap between each block's animation start, not the 200ms specified.
   - **Impact**: Blocks appear more slowly than intended. The deliberate pacing is 2.5x longer than spec, which may feel overly leisurely rather than "smooth, deliberate."
   - **File**: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/14a-ContextWindowComparison/ContextWindowComparison.tsx` line 75

7. **Idle Pulse Period Does Not Match Spec** (Severity: LOW)
   - **Spec says**: "sin wave (amplitude 0.02, period 2s)" -- period of 2s means the angular frequency should be `2 * Math.PI / 60` = ~0.1047 per frame at 30fps.
   - **Implementation does**: Left pulse uses factor `0.1` per frame, giving period `2*PI/0.1 = ~62.8 frames = ~2.09s`. Right shimmer uses factor `0.08`, giving period `2*PI/0.08 = ~78.5 frames = ~2.62s`.
   - **Impact**: Left pulse is very close to spec (2.09s vs 2.0s -- essentially correct). Right shimmer is meaningfully slower (2.62s vs 2.0s -- 31% too slow).
   - **File**: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/14a-ContextWindowComparison/ContextWindowComparison.tsx` lines 151-158

8. **Left Counter Color Logic Does Not Gradually Shift** (Severity: LOW)
   - **Spec says**: "Text subtly shifts toward red tint as it climbs"
   - **Implementation does**: The color ternary on lines 690-697 uses `interpolate(leftCounterValue, [0, TOKEN_COUNTS.left], [1, 1], ...)` which outputs a constant value of 1 regardless of input. The condition `> 0` is therefore always true, so the counter color is `COLORS.LEFT_COUNTER` (red) from the very first frame. There is no gradual transition from white to red.
   - **Impact**: Minor visual polish issue. Counter starts red immediately instead of shifting from neutral white to red as the number climbs higher.
   - **File**: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/14a-ContextWindowComparison/ContextWindowComparison.tsx` lines 690-697

9. **Right Window Green Glow Pulse Missing in Efficiency Variant** (Severity: LOW)
   - **Spec says**: "Subtle pulse on the right window border (green glow) to reinforce" during the knowledge indicator phase (frame 270-330).
   - **Implementation does**: The `rightGlowOpacity` calculation on lines 177-180 only activates for the `density` variant (`variant === 'density'`). In the `efficiency` variant (which is the one this Section 1.14 spec describes), the right window border never receives a green glow. Additionally, even in the density variant, the glow is blue (`rgba(74, 144, 217, ...)`) not green as spec requires.
   - **Impact**: A reinforcing visual cue that the right panel represents "knowledge" is entirely absent in the efficiency variant. The spec's intent was to pulse the right window green during the "10x more system knowledge" reveal.
   - **File**: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/14a-ContextWindowComparison/ContextWindowComparison.tsx` lines 177-180, 455-456

### Notes

- The component itself is well-implemented with clean code structure, proper separation of constants, and organized animation logic. The core visual design faithfully captures the spec's contrast between "chaos" (left) and "clarity" (right).
- The most critical issue is the non-integration into the Part 1 Economics section sequence (Issue #1). The component exists as a standalone implementation in `14a-ContextWindowComparison/` but is never imported or rendered in `S01-Economics/Part1Economics.tsx`. The narration window where this visual should appear (segments 91-96, covering "And there's something else... room to think") currently plays a Veo video clip instead. This is the only HIGH severity issue.
- The missing Root.tsx registration (Issue #2) compounds the integration gap -- the component cannot even be previewed independently in Remotion Studio.
- The dual-variant system (efficiency + density) is a thoughtful addition that allows the same component to serve two different spec sections, but only the efficiency variant is relevant to this Section 1.14 audit.
- All color values, primary easing functions, and spring configurations match the spec with high fidelity. The issues found are primarily about integration (high severity) and minor numerical/behavioral deviations (low severity).
- The right-block slide-in animation uses `translateX` (horizontal slide from right) rather than the spec's description of "slides in from top." This is a directional difference but arguably produces a similarly smooth entrance effect. Not flagged as a separate issue given the low visual impact.

### Resolution Status: UNRESOLVED -- 2 structural issues (HIGH, MEDIUM) and 7 low-severity deviations remain open.
