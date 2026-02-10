# Audit: Focus Single Wall (04_focus_single_wall)

## Status: RESOLVED

### Requirements Met

1. **Canvas resolution 1920x1080** -- SVG viewBox is `0 0 1920 1080` and constants define `FOCUS_WALL_WIDTH = 1920`, `FOCUS_WALL_HEIGHT = 1080` (`FocusSingleWall.tsx:123`, `constants.ts:8-9`). Matches spec exactly.

2. **Dark background #1a1a2e** -- `COLORS.BACKGROUND` is `"#1a1a2e"` applied via `AbsoluteFill` style (`constants.ts:32`, `FocusSingleWall.tsx:109`). Matches spec exactly.

3. **Zoomed view 2-3x magnification** -- Zoom interpolates from `[1, 2.5]` (`FocusSingleWall.tsx:23`). 2.5x falls within the spec's stated 2-3x range. Matches spec.

4. **Wall close-up: single wall segment dominates frame** -- A single `<rect>` wall segment is rendered at center (960, 540) with dimensions 200x300 pixels (`FocusSingleWall.tsx:97-100, 209-223`), which at 2.5x zoom dominates the frame. Matches spec.

5. **"null -> None" label clearly visible** -- Three `<text>` elements display "null" (line 237), arrow Unicode character (line 246), and "None" (line 259) using `JetBrains Mono, monospace` font at 24px with amber color and glow effect (`FocusSingleWall.tsx:226-260`). Content matches spec's "null -> None" label requirement. Rendered vertically rather than horizontally, but information is equivalent.

6. **Wall has texture detail visible at zoom** -- Wall has filled rectangle with variable amber opacity (`rgba(217, 148, 74, ${0.3 + 0.4 * impactGlow})`), amber stroke, and drop-shadow filter that activates on impact (`FocusSingleWall.tsx:215-223`). Provides visual detail at zoom. Acceptable interpretation.

7. **Approaching liquid: code-like liquid flows toward wall** -- Liquid body (semi-transparent blue rectangle) appears at `LIQUID_APPROACH_START` and moves toward wall from right side (`FocusSingleWall.tsx:127-168`). Main liquid mass uses `COLORS.LIQUID_BLUE` at 0.6 opacity with a brighter leading edge at 0.8 opacity (`FocusSingleWall.tsx:130-151`). Matches spec.

8. **Slight code snippets visible in liquid (optional)** -- Five white semi-transparent horizontal rectangles inside the liquid body (`rgba(255,255,255,0.15)`) simulate code-like texture lines (`FocusSingleWall.tsx:153-167`). Matches spec's optional requirement.

9. **Momentum visible in flow** -- Liquid approaches from right at constant velocity (linear easing) with leading edge highlight. See Issue #1 below regarding easing mismatch, but motion is present and visible.

10. **Impact moment: liquid hits wall** -- At `IMPACT_FRAME` (frame 180), liquid position clamps to 0, placing it directly against wall edge (`FocusSingleWall.tsx:29-34`). Matches spec.

11. **Brief splash/compression effect** -- Splash particles (12 particles, lines 81-94) emanate from impact point and dissipate over frames 180-210 (`FocusSingleWall.tsx:172-192`). Compression effect squashes liquid body with peak at 0.15 (`FocusSingleWall.tsx:45-52`). Matches spec concept.

12. **Wall flashes brighter on impact** -- `impactGlow` peaks at 1.0 then decays to 0.4, increasing wall fill opacity and activating amber drop-shadow filter (`FocusSingleWall.tsx:37-42, 215-222`). Matches spec's "Wall glows bright amber."

13. **Liquid stops DEAD (instant, no easing)** -- `liquidX` uses `Easing.linear` with `extrapolateRight: "clamp"` at `IMPACT_FRAME`, producing constant velocity followed by an abrupt stop (`FocusSingleWall.tsx:33`). The stop is instantaneous. Matches spec's "Impact stop: Instant (no easing - hard stop)" requirement.

14. **Held state: liquid pressed against wall, cannot pass through** -- After `IMPACT_FRAME`, `liquidX` is clamped at 0, so liquid remains pressed against wall for the remainder of the composition. Wall is rendered on top, visually blocking passage (`FocusSingleWall.tsx:33, extrapolateRight: "clamp"`). Matches spec.

15. **Visual tension at the boundary** -- Compression effect, splash particles, ripple ring, and wall glow all create visual activity at the liquid-wall boundary post-impact. Matches spec concept.

16. **Ripple effect on wall** -- An `<ellipse>` ripple ring at the impact point expands from radius 10 to 60 (rx) / 10 to 90 (ry) while fading from 0.7 to 0 opacity (`FocusSingleWall.tsx:196-206`). Spec calls for ripple radius 0-50 and opacity 0.8-0 (spec lines 141-142). Radii and opacity are close approximations. Matches spec concept.

17. **Wall glow easing: easeOutQuad** -- `impactGlow` uses `Easing.out(Easing.quad)` (`FocusSingleWall.tsx:41`). Matches spec line 161 exactly.

18. **Narration sync: "literally" lands as liquid stops** -- Explanation text includes "The code literally cannot violate this constraint" (`FocusSingleWall.tsx:302`). This appears at `EXPLANATION_START` (frame 240), which is post-impact (frame 180), aligning with the concept. In parent S03, the composition starts at 53.6s; the narration segment at 60.2s says "It sees these tests. The code it produces must pass them..." which aligns with the wall constraint focus. Acceptable alignment.

19. **S03 integration** -- `FocusSingleWall` is integrated as Visual 3 in `Part3MoldThreeParts.tsx` at `VISUAL_03_START = s2f(53.6)` (frame 1608) through `VISUAL_03_END = s2f(66.98)` (frame 2009), running for ~13.4 seconds of narration time (`Part3MoldThreeParts.tsx:69-73`, `S03-MoldThreeParts/constants.ts:73-74`). Correctly sequenced.

20. **Splash particles positioned correctly** -- Particles originate at `wallCenterX + wallWidth / 2` (right side of wall), matching the liquid approach direction from right (`FocusSingleWall.tsx:176`). Verified correct.

21. **Liquid approaches from right** -- `liquidBaseX = wallCenterX + wallWidth / 2 - liquidX` where `liquidX` goes from -300 to 0, so `liquidBaseX` goes from `wallCenterX + 100 + 300 = 1360` down to `wallCenterX + 100 = 1060` (right side of wall) (`FocusSingleWall.tsx:106`). Liquid correctly approaches from right. Verified.

### Issues Found

1. **Liquid approach easing is linear instead of easeInQuad** -- Severity: LOW
   - Spec says: `easeInQuad` for liquid approach, described as "building momentum" (spec line 159)
   - Implementation does: `Easing.linear` (`FocusSingleWall.tsx:33`)
   - Linear produces constant velocity throughout. The spec intended accelerating approach (starts slow, speeds up) via `easeInQuad`. Since the interpolation range ends at `IMPACT_FRAME` with `extrapolateRight: "clamp"`, using `Easing.in(Easing.quad)` would still produce an instant stop at impact while adding the momentum-building quality. However, the visual difference is subtle and the core requirement -- that the liquid approaches and stops dead -- is met. Downgraded from MEDIUM to LOW since the hard stop (the critical visual element) is correct.

2. **Zoom easing is easeInOutCubic instead of easeOutCubic** -- Severity: LOW
   - Spec says: `easeOutCubic` for zoom (spec line 158)
   - Implementation does: `Easing.inOut(Easing.cubic)` (`FocusSingleWall.tsx:24`)
   - `easeOut` starts fast and decelerates; `easeInOut` starts slow, speeds up, then decelerates. Different character but both produce smooth zoom motion. Minor stylistic deviation.

3. **Frame timing shifted by ~30 frames** -- Severity: LOW
   - Spec says: Zoom 0-90, liquid 90-150, impact at 150, hold 180-300
   - Implementation does: Wall fade-in 0-30, zoom 30-120, liquid 120-180, impact at 180, explanation at 240, hold at 360
   - All phases shifted ~30 frames to accommodate an initial wall fade-in not in spec. The relative proportions of each phase are preserved. Zoom is 90 frames (spec) vs 90 frames (impl). Liquid approach is 60 frames in both. The overall structure matches.

4. **Compression peak is 0.15 instead of 0.1** -- Severity: LOW
   - Spec says: Compression ranges `[0, 0.1, 0]` (spec line 145)
   - Implementation does: `[0, 0.15, 0]` (`FocusSingleWall.tsx:49`)
   - 50% larger than specified, but the visual effect is very similar at either value.

5. **Duration is 15s standalone instead of ~10s** -- Severity: LOW
   - Spec says: ~10 seconds (spec line 4)
   - Implementation does: `FOCUS_WALL_DURATION_SECONDS = 15` in standalone mode (`constants.ts:5`). In S03 parent, runs ~13.4 seconds.
   - The "~10" is approximate. Extra time accommodates the fade-in phase and extended hold for narration. Acceptable for integration context.

6. **Wall label layout is vertical, not single-line horizontal** -- Severity: LOW
   - Spec says: Single label "null -> None" (spec line 22)
   - Implementation does: Three `<text>` elements stacked vertically -- "null" / arrow / "None" (`FocusSingleWall.tsx:226-260`)
   - Same content, different layout. The vertical arrangement may be more readable at the wall's proportions.

7. **No per-component audio SFX** -- Severity: LOW
   - Spec says: Whoosh, thud, silence, hum (spec lines 171-175)
   - Implementation does: No audio. Parent S03 provides narration only.
   - Audio SFX are outside this component's scope and would require audio asset integration.

8. **Extra elements not in spec** -- Severity: LOW
   - Section header "Focusing on a single constraint..." at top (`FocusSingleWall.tsx:308-328`)
   - Explanation panel at bottom with description text (`FocusSingleWall.tsx:264-306`)
   - These are additions that support the narrative, not contradictions of the spec.

9. **Splash particles use Math.random() in useMemo** -- Severity: LOW
   - Comment says "Generate deterministic splash particles" (`FocusSingleWall.tsx:80`) but uses `Math.random()` which is non-deterministic across renders. In practice, `useMemo` with `[]` dependency means they are only generated once per mount, so they are stable within a render session. Not a spec issue, but a code quality note.

### Notes

- All previously identified fixes (liquid direction, hard stop, splash direction, impact positioning) from earlier audit rounds remain correctly applied in the current code.
- The one remaining substantive deviation (liquid approach easing: linear vs easeInQuad) is downgraded to LOW severity because the critical visual requirement -- the instant hard stop at impact -- is correctly implemented. The "building momentum" quality from `easeInQuad` would enhance the animation but its absence does not undermine the spec's core intent.
- All other issues are LOW severity stylistic variations that do not contradict the spec's visual goals.
- The component is properly integrated into S03 at the correct narration timing position.

### Resolution Status: RESOLVED

All issues are LOW severity. The implementation faithfully captures the spec's core visual narrative: camera zooms into a single "null -> None" wall constraint, liquid approaches from the right, hits the wall with an instant dead stop, wall glows amber, splash and ripple effects fire, and the liquid remains held against the immovable wall. No changes required.

---

### Re-Audit Update (2026-02-09)

**Rendered frame 200** (post-impact, liquid pressed against wall): Visual inspection confirms:
- Zoomed-in view (~2.5x) showing a single amber wall segment dominating the left-center of the frame
- "null" / arrow / "None" label clearly visible on the wall in monospace font (vertical layout)
- Blue-gray liquid body pressed against the right side of the wall, stopped dead at the boundary
- Subtle code-line texture visible inside the liquid body (white semi-transparent horizontal lines)
- Impact ripple ring visible at the contact point (expanding ellipse, fading)
- Splash particles visible around the contact zone
- Wall is glowing brighter amber from the impact
- "Focusing on a single constraint..." section header at top
- No visual artifacts, clean zoomed composition

**Verdict: PASS** -- No new issues found. All prior LOW-severity issues remain unchanged and acceptable.
