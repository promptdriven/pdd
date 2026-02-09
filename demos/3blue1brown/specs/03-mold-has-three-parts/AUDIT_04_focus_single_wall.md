# Audit: Focus Single Wall (04_focus_single_wall)

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas resolution and background** -- 1920x1080 with `#1a1a2e` dark background matches spec exactly (`FocusSingleWall.tsx` line 109, `constants.ts` lines 8-9, 32).

2. **Zoom magnification range** -- Zooms from 1 to 2.5x (`constants.ts` line 23, `FocusSingleWall.tsx` lines 20-24), which falls within the spec's 2-3x range.

3. **Liquid approaches from right** -- Previous audit flagged liquid approaching from wrong direction. Now verified fixed: `liquidX` interpolates from `[-300, 0]` (line 32) and `liquidBaseX = wallCenterX + wallWidth / 2 - liquidX` (line 106) correctly positions liquid to the right of the wall, approaching leftward toward it.

4. **Hard stop at impact** -- Previous audit flagged smooth deceleration instead of instant stop. Now verified fixed: `Easing.linear` (line 33) with clamping at IMPACT_FRAME gives constant velocity followed by abrupt stop, matching spec's "Liquid stops DEAD" and "Instant (no easing - hard stop)" requirement.

5. **Impact glow peaks and holds** -- Glow interpolates `[0, 1, 0.4]` matching spec values. Wall fill opacity increases and amber glow filter activates on impact (`FocusSingleWall.tsx` lines 37-41, 215-222).

6. **Wall glow uses easeOutQuad** -- `Easing.out(Easing.quad)` on line 41 matches spec's `easeOutQuad`.

7. **Ripple effect at impact** -- Ellipse ripple on right side of wall (lines 196-206) with expanding radius and fading opacity approximates the spec's RippleRing component.

8. **Splash particles direction** -- Particles splash to the right (angle centered at 90 degrees, line 86) consistent with liquid arriving from the right. Positioned at `wallCenterX + wallWidth / 2` (line 176). Fix verified.

9. **Impact position on right side of wall** -- Ripple and splash both originate at `wallCenterX + wallWidth / 2` (lines 176, 197). Fix verified.

10. **Wall label content** -- Displays "null", arrow, "None" matching spec's "null -> None" constraint label (`FocusSingleWall.tsx` lines 226-260, `constants.ts` lines 42-46).

11. **Liquid compression at impact** -- Compression effect activates post-impact with interpolated squash (lines 45-52), matching spec's CompressionWave concept.

12. **Code-like texture in liquid** -- White semi-transparent rectangles inside liquid body (lines 153-167) implement the spec's optional "slight code snippets visible in liquid."

13. **Held state after impact** -- Liquid remains pressed against wall from IMPACT_FRAME onward with clamped position, matching spec's "Liquid pressed against wall / Cannot pass through / Visual tension at the boundary."

14. **Narration alignment** -- Explanation text "The code literally cannot violate this constraint" (line 302) echoes the spec's narration sync point where "literally" lands as liquid stops.

### Issues Found

1. **Zoom easing profile differs from spec** -- Severity: LOW
   - Spec says: `easeOutCubic` for zoom (spec line 158)
   - Implementation does: `Easing.inOut(Easing.cubic)` (`FocusSingleWall.tsx` line 24)
   - `easeInOut` starts and ends slow; `easeOutCubic` starts fast and decelerates. Different feel during zoom-in.

2. **Frame timing offsets throughout** -- Severity: LOW
   - Spec says: Zoom frames 0-90, liquid approach frames 90-150, impact at frame 150, hold frames 180-300
   - Implementation does: Wall fade-in frames 0-30, zoom frames 30-120, liquid approach frames 120-180, impact at frame 180
   - All phases are shifted by ~30 frames to accommodate an initial wall fade-in phase not in the spec. Internal proportions are similar.

3. **Liquid approach easing should be easeInQuad, not linear** -- Severity: MEDIUM
   - Spec says: `easeInQuad` for liquid approach ("building momentum") (spec line 159)
   - Implementation does: `Easing.linear` (line 33)
   - The spec calls for `easeInQuad` (starts slow, accelerates -- building momentum) with instant stop at impact. Linear gives constant velocity throughout, missing the "building momentum" visual quality. The previous fix changed from `easeInQuad` to `linear` to address the hard stop concern, but the correct solution would be `easeInQuad` with the interpolation range ending at IMPACT_FRAME (which would still give an instant stop at clamp while having the accelerating approach).

4. **Compression magnitude exceeds spec** -- Severity: LOW
   - Spec says: Compression ranges 0 to 0.1 back to 0 (spec line 145)
   - Implementation does: 0 to 0.15 back to 0 (`FocusSingleWall.tsx` line 49)
   - 50% more compression than specified. Minor visual difference.

5. **Duration exceeds spec** -- Severity: LOW
   - Spec says: ~10 seconds (spec line 4)
   - Implementation does: `FOCUS_WALL_DURATION_SECONDS = 15` in standalone mode (`constants.ts` line 5). In S03 parent, runs for ~13.4 seconds (frames 1608-2009 at 30fps).
   - Exceeds target by 3-5 seconds, though "~10" is approximate.

6. **Wall label rendered as three separate text lines instead of single label** -- Severity: LOW
   - Spec says: Single label "null -> None" on wall (spec line 22)
   - Implementation does: Three `<text>` elements -- "null" on top, arrow in middle, "None" below (lines 226-260)
   - Same information, vertical layout vs. single horizontal string.

7. **No separate audio effects** -- Severity: LOW
   - Spec says: Whoosh for approaching liquid, sharp thud on impact, brief silence, subtle hum of constraint holding (spec lines 171-175)
   - Implementation does: No per-component audio. Parent S03 provides only narration track.
   - Audio SFX would require audio system integration beyond this component's scope.

8. **Added elements not in spec** -- Severity: LOW
   - Section header text "Focusing on a single constraint..." at top (lines 308-328) not in spec
   - Explanation panel at bottom (lines 264-306) not in spec, though content aligns with narration
   - These are additions, not contradictions, and support the narrative.

### Notes

- The previous audit's resolution notes claim fixes for liquid direction, hard stop, splash direction, and impact positioning. All four fixes are verified as correctly applied in the current code.
- The one lingering medium-severity issue is the liquid approach easing: `Easing.linear` was used as the fix for the hard stop problem, but the spec actually calls for `easeInQuad` approach with instant clamp at impact. Using `Easing.in(Easing.quad)` with the interpolation range `[LIQUID_APPROACH_START, IMPACT_FRAME]` and `extrapolateRight: "clamp"` would satisfy both requirements -- accelerating approach and instant stop.
- The component is well-integrated into the S03 parent composition as Visual 3 at the correct narration position (53.6s-66.98s).
- All low-severity deviations are acceptable stylistic choices that do not undermine the spec's intent.
