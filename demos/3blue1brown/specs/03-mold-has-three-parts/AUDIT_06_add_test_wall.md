# Audit: Add Test Wall (Section 3.6)

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas and background**: Resolution is 1920x1080 (`ADD_TEST_WALL_WIDTH`/`ADD_TEST_WALL_HEIGHT` in `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/26-AddTestWall/constants.ts` line 8-9). Background is `#1a1a2e` (`COLORS.BACKGROUND`, constants.ts line 32). Matches spec exactly.

2. **ParticleEffect component implemented**: 30 particles converge from scattered positions toward a center point (`AddTestWall.tsx` lines 7-51). Uses `convergenceProgress` to move particles via `p.x * (1 - convergenceProgress)` (line 38), matching the spec's convergence formula at spec line 193. Particle count of 30 matches spec line 179. Random size range `Math.random() * 4 + 2` matches spec line 183. Particle color uses `COLORS.WALLS_AMBER` (#D9944A), matching spec line 198's `#D9944A`. Opacity factor of 0.8 matches spec line 199.

3. **Particle timing**: Active from `BEATS.PARTICLES_START` (frame 90) to `BEATS.PARTICLES_END` (frame 180), matching spec's "Frame 90-180" range (spec lines 50-54). Convergence uses `Easing.in(Easing.quad)` (AddTestWall.tsx line 293), matching spec's `easeInQuad` (spec line 207).

4. **RatchetMechanism component implemented**: Full SVG gear mechanism with 8 teeth (`AddTestWall.tsx` lines 53-146). Includes inner circle, center dot, and a pawl that rotates from -15 degrees to 0 degrees when engaged (line 110). Flash effect on engagement with golden glow ring (lines 131-138). Engages at `BEATS.RATCHET_ENGAGE` (frame 270), matching spec's "Frame 270-360" ratchet engagement (spec line 62).

5. **MoldCrossSection component implemented**: SVG showing left wall, right wall, and bottom wall of the mold cavity with "Test Mold" label (`AddTestWall.tsx` lines 148-208). Uses `COLORS.LABEL_GRAY` at 0.4 opacity for subtle structural context.

6. **Three-phase wall formation**:
   - Phase 1 (frames 90-180): Particles gather and converge (`AddTestWall.tsx` lines 407-414)
   - Phase 2 (frames 180-270): Dashed outline appears, progressively filling with solid amber. Border transitions from `dashed` to `solid` based on `wallSolidProgress` (lines 417-443). Uses `Easing.out(Easing.cubic)` for solidification (line 309), matching spec's `easeOutCubic` (spec line 208).
   - Phase 3 (frame 270+): Solid wall with ratchet engagement. `ratchetEngaged = frame >= BEATS.RATCHET_ENGAGE` is a boolean snap (line 321), matching spec's "Instant (no easing)" for ratchet click (spec line 209).

7. **Terminal overlay**: Positioned bottom-right (lines 219-220: `bottom: 30, right: 30`), matching spec's "Bottom-right corner" (spec line 32). Shows correct command `$ pdd bug user_parser` (line 346). Progressive line reveal: "Creating failing test..." at `BEATS.TERMINAL_COMMAND_START` (frame 90), "Test created: test_whitespace_returns_none" at `BEATS.TERMINAL_COMPLETE` (frame 300), matching spec lines 163-168.

8. **Terminal timing**: Appears at `BEATS.TERMINAL_START` (frame 60), matching spec's Frame 60-90 range for terminal appearance (spec line 163).

9. **Beat timing alignment**: Constants (constants.ts lines 13-28) follow spec's frame ranges: 0-90 return to mold, 90-180 particles, 180-270 solidify, 270-360 click/lock, 360-600 hold. All match spec lines 44-72.

10. **Hold phase pulse**: Glow pulse on new wall during hold phase starting at frame 360 (`BEATS.HOLD_START`), with `boxShadow` animating from 0 to 0.3 and back (lines 330-335, 435-437). Matches spec's "Brief pulse on new wall" (spec line 72).

11. **Label appearance**: Label fades in starting at frame 240 (`BEATS.LABEL_START`) with `easeOutCubic` (lines 312-318), matching spec's label fade range of 240-300 (spec line 131) and easing (spec line 210).

12. **Permanence narration alignment**: Explanation text appears during hold phase saying "Wall is now **permanent**. That bug can never occur again." with "permanent" in bold amber (lines 461-481), aligning with spec narration "That wall is permanent. That bug can never occur again" (spec lines 218-220).

13. **Existing walls displayed**: Three existing test labels shown: "null -> None", "empty -> None", '"abc" -> "abc"' (constants.ts lines 40-44), with amber color and monospace font (AddTestWall.tsx lines 381-401).

14. **Composition registered**: Component is registered in Root.tsx as `AddTestWall` composition and integrated into `Part3MoldThreeParts.tsx` as Visual 5 in the S03 sequence.

### Issues Found

1. **New wall label does not match spec**: The spec says the new wall label should be `"whitespace -> None"` (spec lines 29, 149). The implementation uses `'" abc " -> "abc"'` (constants.ts line 47, `NEW_TEST`). While this is a reasonable whitespace-related test, it does not match the exact label text specified. The spec explicitly states the label should be `"whitespace -> None"` in the wall formation visual (spec line 82-83), in the NewWall component (spec line 149), and in the terminal output context.

2. **Duration mismatch**: The spec says "Duration: ~20 seconds" (spec line 4), which would be 600 frames at 30fps. The implementation sets `ADD_TEST_WALL_DURATION_SECONDS = 15` (constants.ts line 5), yielding 450 frames. The `BEATS.HOLD_END` is set to 600 (constants.ts line 27), which exceeds the 450-frame composition duration, meaning the hold phase from frames 450-600 would never render. This is inconsistent -- either the duration should be 20 seconds (600 frames) to match the spec, or `HOLD_END` should be capped at 450.

3. **Particle spread range differs from spec**: The spec defines particle positions as `Math.random() * 100 - 50` for both x and y (spec line 182), giving a range of -50 to +50. The implementation uses `Math.random() * 200 - 100` (AddTestWall.tsx line 15-16), giving a range of -100 to +100. This makes particles spread twice as wide before converging.

4. **ParticleEffect positioning issue**: The `ParticleEffect` component receives `centerX={960}` (AddTestWall.tsx line 411), which is the center of the 1920px canvas. However, the `ParticleEffect` is rendered inside a container that is itself positioned at `left: "50%"` with `transform: "translate(-50%, -50%)"` (lines 375-377). The particles' absolute position of `left: 960px` is relative to this already-centered container, not the viewport, which would place the particle effect off-center to the right.

5. **Gap between mold walls appearing and particles**: Existing walls and mold cross-section finish fading in at frame 30 (`BEATS.WALLS_VISIBLE_END`), but particles do not start until frame 90 (`BEATS.PARTICLES_START`). The spec describes frames 0-90 as "Return to mold" with existing walls becoming visible and a gap where the new wall will go (spec lines 44-48). The implementation has a 60-frame static gap (frames 30-90) where nothing animates -- the mold is visible but nothing is happening. The spec implies a more gradual reveal through the full 0-90 range.

6. **No audio implementation**: The spec calls for a soft "gathering" sound during particle phase, a rising tone during solidification, and a sharp "CLICK" when the ratchet engages (spec lines 222-228). No audio elements are present. This may be handled externally, but worth noting.

### Notes

The implementation now faithfully covers the major structural requirements from the spec: three-phase wall formation (particles, solidification, lock), a proper ratchet mechanism with gear teeth and engaging pawl, a mold cross-section view, correct terminal overlay with progressive line reveal, and matching easing functions. The prior audit's original deltas (missing ParticleEffect, missing RatchetMechanism, missing MoldCrossSection, simplified formation, wrong terminal timing) have all been substantively addressed.

The remaining issues are relatively minor. The most meaningful are the label text mismatch (issue 1) and the duration/HOLD_END inconsistency (issue 2), which could cause the hold phase to be truncated. The particle positioning issue (issue 4) may cause the particle convergence to render in an unexpected location due to nested centering transforms. The other issues are cosmetic or may be handled by separate systems (audio).

Key files reviewed:
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/26-AddTestWall/AddTestWall.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/26-AddTestWall/constants.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/26-AddTestWall/index.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/Part3MoldThreeParts.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/constants.ts`
