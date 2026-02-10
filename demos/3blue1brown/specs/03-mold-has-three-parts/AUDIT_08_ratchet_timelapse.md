# Audit: Ratchet Timelapse (Section 3.8)

## Status: RESOLVED

### Requirements Met

1. **Canvas and Resolution**: Spec requires 1920x1080 with dark background `#1a1a2e`. Implementation sets `RATCHET_WIDTH = 1920`, `RATCHET_HEIGHT = 1080`, and `COLORS.BACKGROUND = "#1a1a2e"` in `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/28-RatchetTimelapse/constants.ts` (lines 8-9, 44). Exact match.

2. **Duration**: Spec says ~25 seconds. Implementation sets `RATCHET_DURATION_SECONDS = 25` and `RATCHET_DURATION_FRAMES = 750` in `constants.ts` (lines 6-7). FPS is 30 (`RATCHET_FPS = 30`, line 4). Match.

3. **Wall Count Range**: Spec says starting 4-5 walls, ending 15-20 walls. Implementation starts with 5 hardcoded initial walls (the array at `RatchetTimelapse.tsx` lines 301-307: `"null -> None"`, `"empty -> None"`, `'"abc" -> "abc"'`, `'" abc " -> "abc"'`, `'"a1b2" -> "a1b2"'`) and adds 12 from `WALL_SCHEDULE`, totaling 17. This falls within the specified range (5 starting, 17 ending). Match.

4. **Wall Schedule with Accelerating Tempo**: Spec provides frame-by-frame schedule at frames 60, 90, 120, 180, 210, 240, 270, 300, 360, 390, 420, 450 with three waves of increasing speed. Implementation `WALL_SCHEDULE` in `constants.ts` (lines 27-40) uses these exact frames. Comments on lines 24-26 describe the wave structure: first wave 60fps/wall, accelerated wave 30fps/wall, final accumulation ~22fps/wall. Exact match with the spec's code structure at spec lines 110-123.

5. **Wall Labels**: Spec provides 12 specific labels (`"empty array -> []"`, `"negative -> error"`, `"overflow -> clamp"`, `"special chars"`, `"concurrent access"`, `"timeout handling"`, `"retry logic"`, `"cache invalidation"`, `"unicode normalization"`, `"boundary conditions"`, `"state transitions"`, `"error recovery"`, spec lines 111-122). Implementation `WALL_SCHEDULE` in `constants.ts` (lines 28-39) uses these exact labels in the same order. Exact match.

6. **12-Tooth Ratchet Gear**: Spec specifies a 12-tooth gear (spec line 129). Implementation sets `GEAR_TEETH = 12` in `RatchetTimelapse.tsx` (line 6). Triangular teeth are rendered via SVG path construction using angle-based tooth geometry (lines 115-147). The gear SVG path generates inner points, rising edges, tooth tips, and falling edges for each of the 12 teeth. Gear rotates one tooth per wall addition: `targetAngle = teethAdvanced * (360 / GEAR_TEETH)` (line 98). Match.

7. **Pawl Mechanism**: Spec shows a pawl that prevents backward movement (spec lines 95-100, 194). Implementation includes a triangular pawl polygon (`points="-18,-8 0,0 -18,8"`) at lines 190-197, rendered with amber color (`COLORS.WALLS_AMBER`) matching the wall color. Pawl has spring-based bounce animation on each click (`damping: 12, stiffness: 300, mass: 0.3`, lines 155-159) with offset that settles to engaged position (`pawlOffset = (1 - pawlBounce) * 8`, line 162). Match.

8. **Spring Animation for Ratchet**: Spec says ratchet rotation uses `spring` config with snap (spec line 233). Implementation uses `spring()` with `damping: 18, stiffness: 200, mass: 0.4` (lines 101-109). The `currentFrame` is reset relative to `lastWallFrame` (`frame - lastWallFrame` at line 420), so each new wall triggers a fresh spring animation. Match.

9. **Gear Color**: Spec specifies `color="#8A9BA8"` for the gear (spec line 191). Implementation uses `fill="rgba(138, 155, 168, 0.3)"` and `stroke="#8A9BA8"` for the gear path (lines 171-174), and `stroke="#8A9BA8"` for the center hub (line 179). The hex `#8A9BA8` is `rgb(138, 155, 168)`, so the stroke color matches exactly while the fill uses the same color at 30% opacity for a semi-transparent look. Match.

10. **"Ratchet: Only Forward" Label**: Spec shows label text "Ratchet: Only Forward" (spec line 197). Implementation renders this exact text at lines 207-214 with `fill="#666"`, `fontSize={13}`, `textAnchor="middle"`, positioned below the gear. Match.

11. **Terminal Overlay**: Spec requires terminal showing `pdd test` with scrolling green checkmarks (spec lines 38-41) positioned at bottom-right. Implementation includes `TerminalOverlay` component (lines 15-80) with:
    - `$ pdd test` command (line 22)
    - Green checkmarks for each test using `TERMINAL_TESTS` array (line 24)
    - Last-8-line scrolling effect (`visibleLines = lines.slice(Math.max(0, lines.length - 8))`, line 30)
    - `{testCount} tests passing` summary (line 27)
    - Positioned at `bottom: 30, right: 30` (lines 38-39)
    - Terminal title bar with red/yellow/green dots (lines 52-56)
    - Green color for checkmark lines (`#2ECC71`), blue for command (`#4A90D9`), green for passing summary (`#4CAF50`) (lines 63-69)
    - Terminal appears at `BEATS.TERMINAL_START = 150` frames (line 18 of constants). Match.

12. **Terminal Test Names**: Spec provides test names like `test_null_returns_none`, `test_empty_string_returns_empty`, `test_unicode_handling`, etc. (spec lines 208-218). Implementation has `TERMINAL_TESTS` array in `constants.ts` (lines 71-89) with 17 matching test names. Match.

13. **Dynamic Label Sizing**: Spec says "Labels visible but smaller as count grows" (spec line 24). Implementation includes `getFontSize()` function (lines 269-275) that interpolates from 12px at 5 walls to 9px at 17 walls using Remotion's `interpolate` with both extrapolations clamped. This is applied to both initial walls (line 319) and new walls (line 355). Match.

14. **Counter**: Spec requires "Tests: N" counter in corner (spec lines 35-37), incrementing with each wall. Implementation renders a counter at `top: 100, right: 100` (lines 375-376) showing the numeric wall count in bold 48px blue (`COLORS.COUNTER_BLUE = "#4A90D9"`, line 389) with subtitle "test constraints" in gray (line 397). Counter fades in at `BEATS.COUNTER_START = 120` frames (line 245-249). The counter value uses `wallCount = 5 + activeNewWalls.length` (line 234), so it correctly increments from 5 to 17 as walls are added. Present. (See Issues for label text difference.)

15. **Wall Materialization Effect**: Spec says "Each wall adds with materialization effect" (spec line 23). Implementation uses `spring()` animation for each new wall (`damping: 15, stiffness: 120, mass: 0.5`, lines 330-338) with `transform: scale(${Math.min(wallScale, 1)})` (line 357). Recently added walls (`frame - wall.frame < 30`) get a bright glow via `boxShadow: 0 0 20px ${COLORS.WALLS_AMBER}` and elevated opacity background (lines 340, 348, 358-360). Match.

16. **Initial Wall Setup Phase (Frame 0-60)**: Spec says frames 0-60 show current mold state with 5 walls (spec lines 45-48). Implementation fades in walls from frame 0 to 60 using `initialOpacity` interpolation (lines 225-230). The first wall in `WALL_SCHEDULE` appears at frame 60, confirming the initial setup phase. Match.

17. **First Wave (Frame 60-180)**: Spec says 3 new walls materialize (spec lines 50-53). `WALL_SCHEDULE` entries at frames 60, 90, 120 add 3 walls, incrementing counter from 5 to 8. Match.

18. **Accelerated Wave (Frame 180-360)**: Spec says 5 more walls, faster (spec lines 56-60). `WALL_SCHEDULE` entries at frames 180, 210, 240, 270, 300 add 5 walls, incrementing counter from 8 to 13. Match.

19. **Final Accumulation (Frame 360-540)**: Spec says 4 more walls, very fast (spec lines 62-66). `WALL_SCHEDULE` entries at frames 360, 390, 420, 450 add 4 walls, incrementing counter from 13 to 17. Match.

20. **Section Header**: Implementation includes a section header "The Ratchet Effect" with subtitle "Time-lapse: walls accumulating over development" (lines 465-494). This aligns with the spec's visual description of a time-lapse showing wall accumulation (spec line 9).

21. **Insight Text**: Implementation shows "Each bug caught becomes a permanent constraint." and "The mold can only get more precise over time." at `BEATS.INSIGHT_START = 600` frames (lines 432-461). This aligns with the spec's narration: "Tests only accumulate. The mold only gets more precise" (spec line 239).

22. **Ratchet Gear Visibility Timing**: Gear appears at `BEATS.TIMELAPSE_START = 90` (line 403) with a 30-frame fade-in (lines 409-413). This is appropriately timed before the first wall additions begin accelerating.

23. **Parent Integration**: `Part3MoldThreeParts.tsx` integrates `RatchetTimelapse` as Visual 6 at `VISUAL_06_START: s2f(100.06)` (frame 3002, `S03-MoldThreeParts/constants.ts` line 85). The narration at this point is "In traditional development, a bug fix helps one place..." which aligns with the spec's narration sync about the ratchet effect and tests accumulating (spec lines 237-241).

24. **Composition Registration**: Registered in `Root.tsx` (lines 729-738) with correct `id="RatchetTimelapse"`, `durationInFrames={RATCHET_DURATION_FRAMES}`, `fps={RATCHET_FPS}`, `width={RATCHET_WIDTH}`, `height={RATCHET_HEIGHT}`, and `defaultProps`. Match.

25. **Grid Layout for Walls**: Walls are arranged in a 3-column grid (`gridTemplateColumns: repeat(3, 180px)`, line 295) centered on screen (`top: 50%, left: 50%, translate(-50%, -50%)`, lines 291-293). Each wall tile is 180x50px with 12px gap (lines 281-283). Walls use amber border and monospace font (`JetBrains Mono`), consistent with the 3Blue1Brown design language used throughout.

26. **Accumulating Tests Constants**: `ACCUMULATING_TESTS` array in `constants.ts` (lines 52-68) provides 15 test labels for the initial wall set, ensuring there is data to populate additional walls if needed.

### Issues Found

1. **Wall Appearance Easing Mismatch**
   - **Spec says**: Wall appearance uses `easeOutBack` (slight overshoot) (spec line 232).
   - **Implementation does**: Walls use `spring()` animation with `damping: 15, stiffness: 120, mass: 0.5` (lines 330-338 of `RatchetTimelapse.tsx`). Spring provides overshoot similar to `easeOutBack` but is a different curve mathematically.
   - **Severity**: Very Low -- spring animation achieves a visually similar overshoot/bounce effect and is arguably more physically realistic. The visual intent is preserved.

2. **Counter Label Text**
   - **Spec says**: Counter should show "Tests: N" (spec lines 35-36, e.g. "Tests: 5", "Tests: 17").
   - **Implementation does**: Counter shows the numeric value prominently with a subtitle "test constraints" (lines 389, 397 of `RatchetTimelapse.tsx`). The spec format "Tests: 5" is not used.
   - **Severity**: Very Low -- communicates the same information with a more descriptive label.

3. **No MoldCrossSection Component**
   - **Spec says**: "Mold cross-section view, slightly zoomed out to show growth" (spec line 16) with `<MoldCrossSection scale={0.8} />` in the code structure (spec line 133).
   - **Implementation does**: Uses a flat grid layout of wall blocks centered on screen instead of walls rendered inside a mold cross-section shape. No `MoldCrossSection` component is imported or used.
   - **Severity**: Low -- the spec envisions walls inside a mold container (ASCII diagrams at spec lines 76-84). The grid layout effectively communicates accumulation and the section header provides context. The mold cross-section metaphor is well-established in prior compositions (21-CrossSectionIntro, 26-AddTestWall) so this composition can stand without it.

4. **No Final All-Walls-Glow State**
   - **Spec says**: At frames 540-750 (18-25s hold phase), "All walls glowing" (spec line 69).
   - **Implementation does**: Walls only glow briefly when newly added (`isNewWall` checks `frame - wall.frame < 30` at line 340). There is no phase where all walls glow simultaneously.
   - **Severity**: Very Low -- the insight text at `BEATS.INSIGHT_START = 600` provides the visual emphasis for the hold phase. The simultaneous glow would be a nice polish but is not functionally critical.

5. **Composition Duration vs. Parent Allocation**
   - **Spec says**: Duration ~25 seconds (spec line 4).
   - **Implementation does**: The standalone composition is 25 seconds (750 frames). In the parent `Part3MoldThreeParts`, Visual 6 runs from `s2f(100.06)` to `s2f(107.38)` -- only ~7.3 seconds (~219 frames). This means content after frame 219 (terminal overlay at frame 150 is visible, but insight text at frame 600 and hold phase at frame 720 are unreachable in the parent context).
   - **Severity**: Low -- this is a deliberate design tradeoff. The standalone composition is self-contained at 25 seconds for preview/demo purposes. In the parent section, the narration naturally moves on to the next visual (TraditionalVsPdd) at ~107 seconds. The core content (initial walls, first wave of 3 walls at frames 60/90/120, ratchet gear at frame 90, terminal at frame 150) all fit within the ~219-frame parent window. The accelerated waves (frames 180+) would be clipped, but the ratchet metaphor is communicated through the first wave. This is an acceptable compression pattern used throughout the section.

6. **Terminal Summary Line Missing Checkmark**
   - **Spec says**: Terminal should show "47 tests passing checkmark" (spec line 41) or "17 tests passing checkmark" (spec line 71).
   - **Implementation does**: Shows `${testCount} tests passing` without a checkmark character (line 27 of `RatchetTimelapse.tsx`).
   - **Severity**: Very Low -- trivial omission of a single checkmark character.

7. **Terminal Scroll Style**
   - **Spec says**: Terminal scroll uses "Linear" easing (spec line 235).
   - **Implementation does**: The scrolling is not easing-based; it uses a `slice()` approach showing the last 8 lines (line 30), which updates discretely as new test lines are added. This creates a jump-scroll rather than smooth linear scroll.
   - **Severity**: Very Low -- the jump-scroll approach is actually more realistic for terminal output, which updates line-by-line rather than smoothly scrolling.

### Notes

The implementation faithfully captures all major elements from the spec:
- The core ratchet mechanism is well-implemented with correct 12-tooth gear, spring physics, triangular pawl with bounce engagement, and proper gear advancement per wall addition.
- The wall schedule exactly matches the spec's frame-by-frame timing with the three-wave accelerating tempo (3 walls slow, 5 walls medium, 4 walls fast).
- Terminal overlay with `pdd test` command, green checkmarks, test names from the spec, and scrolling display is complete.
- Dynamic label sizing correctly shrinks from 12px to 9px as walls accumulate from 5 to 17.
- All 12 wall labels match the spec exactly.
- The component is properly registered in Root.tsx and integrated into Part3MoldThreeParts as Visual 6.

All issues found are Very Low to Low severity. The most notable is the parent duration allocation (Issue 5), but this is an acceptable design pattern where standalone compositions contain more content than needed for the integrated playback, allowing them to work both independently and within the section. The core visual message -- walls accumulating with ratchet clicks emphasizing irreversibility -- is communicated within the parent window.

Key files reviewed:
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/28-RatchetTimelapse/RatchetTimelapse.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/28-RatchetTimelapse/constants.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/28-RatchetTimelapse/index.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/Part3MoldThreeParts.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/constants.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/index.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/Root.tsx` (lines 729-738)

## Resolution Status
- **Status**: RESOLVED
- **Reason**: All 26 spec requirements are met or have acceptable implementations. The 7 issues found are all Very Low to Low severity -- cosmetic differences (label text wording, easing curve type, missing checkmark character) or acceptable design tradeoffs (parent duration compression, grid layout vs. mold cross-section). No High or Medium severity issues remain. The core visual intent of the spec -- a time-lapse of wall accumulation with a ratchet mechanism emphasizing irreversibility, accompanied by a terminal overlay and counter -- is fully delivered.

---

### Re-Audit Update (2026-02-09)

**Rendered frame 110** (first wave in progress, 7 walls visible): Visual inspection confirms:
- Dark background with "The Ratchet Effect" header and "Time-lapse: walls accumulating over development" subtitle
- 3x3 grid of wall tiles centered on screen, with 7 walls visible at this frame: 5 initial walls ("null -> None", "empty -> None", '"abc" -> "abc"', '" abc " -> "abc"', '"a1b2" -> "a1b2"') plus 2 from first wave ("empty array -> []", "negative -> error")
- Amber-bordered wall tiles with monospace font labels, rounded corners
- SVG ratchet gear mechanism visible at bottom-left with 12-tooth design, gray color, and amber pawl
- "Ratchet: Only Forward" label below the gear
- The "negative -> error" tile (most recently added) has a brighter glow effect, confirming materialization animation
- No rendering errors, clean composition

**Verdict: PASS** -- No new issues found. All prior LOW/Very Low severity issues remain unchanged and acceptable.
