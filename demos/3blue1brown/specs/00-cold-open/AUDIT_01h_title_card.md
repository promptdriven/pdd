# Audit: 01h Title Card

## Status: ISSUES FOUND

### Requirements Met

1. **Title text content**: The title "Prompt-Driven Development" is correctly displayed (ColdOpenSection.tsx line 152).

2. **Typography**: Implementation matches spec precisely:
   - Font family: `Inter, system-ui, sans-serif` (spec: Inter or system sans-serif fallback) -- line 144
   - Font size: 72px -- line 145
   - Font weight: 600 (semi-bold) -- line 146
   - Color: `#F8F4F0` (warm white) -- line 147
   - Letter-spacing: `0.02em` -- line 148

3. **Title fade-in with upward drift**: Title fades from opacity 0 to 1 with a translateY drift from +20px to 0px (lines 140, 143), matching the spec's animation concept.

4. **Blue glow behind title**: Text-shadow includes `0 0 60px rgba(74, 144, 217, 0.15)` (line 150), using the correct glow color (#4A90D9 = rgb(74,144,217)) and target opacity (0.15).

5. **Background dark color**: AbsoluteFill uses `#1a1a2e` (line 120), close to spec's `#1E1E2E`.

6. **Dimmed code backdrop**: The clean regenerated code from VISUAL_03 is shown behind the title (lines 122-132), maintaining visual continuity from the code regeneration scene. Code content matches the clean version from VISUAL_03 (line 130 matches line 98).

7. **No narration**: This section has no narration overlay, matching the spec's "silent beat" intention. The narration "So why are we still patching?" from the audio track plays during this visual.

8. **Canvas resolution**: 1920x1080 (constants.ts lines 18-19).

9. **Center alignment**: Title is centered using flexbox `alignItems: "center"` and `justifyContent: "center"` (lines 138-139).

### Issues Found

1. **Duration is 5x shorter than spec (HIGH)**
   - Spec: ~10 seconds (timestamp 1:50-2:00), with frames 0-60 for code dim, frames 30-90 for title fade, frames 90-270 for hold, frames 270-300 for transition prep
   - Implementation: VISUAL_04 runs from 14.1s to 15.96s (frames 423-479 at 30fps), giving only 1.87 seconds total duration (S00-ColdOpen/constants.ts lines 42-43)
   - The entire cold open section is 19 seconds (constants.ts line 16), whereas the spec's cold open extends to 2:00. The compressed timeline leaves no room for the title card to breathe.

2. **No hold period (HIGH)**
   - Spec: Frames 90-270 (3-9s) should be a 6-second static hold with "pure stillness" where the viewer reads and absorbs the title. The spec explicitly states: "No animation -- pure stillness. This is the moment the viewer reads and absorbs the title."
   - Implementation: The title fades in over frames 0-60 of the local sequence (2 seconds), then the cold open section ends roughly 0.87s later. No contemplative hold exists.

3. **Code dimming is static, not animated (MEDIUM)**
   - Spec: Code opacity animates from 1.0 to 0.15 over the first 2 seconds using `easeInOutCubic`, creating a "crossfade from code to title backdrop"
   - Implementation: Code backdrop is set to a static opacity of 0.25 (line 127) with no animation. The value is also slightly off (0.25 vs spec's 0.15).

4. **No vignette (MEDIUM)**
   - Spec: Soft radial vignette darkening edges, center bright, edges at ~85% darkness, fading in from 0 to target opacity over frames 0-60
   - Implementation: No vignette overlay exists in VISUAL_04. The 01-ColdOpen/ColdOpenSplitScreen.tsx does implement a vignette (radial-gradient, line 82), but this is in the separate split-screen composition, not the title card.

5. **No editor chrome or terminal fade-out (MEDIUM)**
   - Spec: Editor chrome (top bar, gutter) and terminal snippet in bottom-right should fade out during the title card transition. Cursor should stop blinking and disappear.
   - Implementation: VISUAL_03 shows a terminal indicator (`$ pdd generate user_parser` at line 111), but it does not carry over into VISUAL_04. The visual switch between activeVisual states is a hard cut rather than a crossfade, so these elements simply disappear rather than fading out.

6. **Glow implementation differs from spec (LOW)**
   - Spec: Glow should be a separate div behind the title text with `radial-gradient(ellipse at center, rgba(74,144,217,glowOpacity), transparent 70%)`, `filter: blur(20px)`, spanning `inset: -40px`
   - Implementation: Glow is implemented as a text-shadow `0 0 60px rgba(74, 144, 217, 0.15)` (line 150). The visual effect is similar but technically different. Bloom radius is 60px vs spec's 40px.

7. **No separate glow fade-in animation (LOW)**
   - Spec: Glow intensity should animate independently from 0 to 0.15 over frames 45-90 using `easeOutCubic`
   - Implementation: Since glow is part of the text-shadow, it fades in coupled to the title opacity (frames 0-60), not on its own delayed timeline.

8. **Title fade-in timing offset (LOW)**
   - Spec: Title fades in from frame 30 to 90 (1-3s), overlapping with the code dimming so "title arrives as code recedes"
   - Implementation: Title fades in from frame 0 to 60 (0-2s relative to VISUAL_04 start). Animation starts immediately rather than being delayed to allow code dimming to begin first.

9. **Title vertical position not shifted above center (LOW)**
   - Spec: Title should be positioned at ~45% from top ("optionally shifted ~5% above true center for visual weight balance")
   - Implementation: Title container uses flexbox centering at exact center (lines 136-139), with no vertical offset. The spec's reference code uses `top: '45%'` with `transform: translate(-50%, -50%)`.

10. **Background color slight mismatch (LOW)**
    - Spec: `#1E1E2E`
    - Implementation: `#1a1a2e` (slightly darker). Minor visual difference.

11. **FPS difference between implementations (LOW)**
    - S00-ColdOpen runs at 30fps (constants.ts line 15)
    - 01-ColdOpen runs at 60fps (01-ColdOpen/constants.ts line 4)
    - The spec's frame numbers (e.g., "Frame 0-60" for 2 seconds) assume 30fps, which matches S00-ColdOpen.

### Notes

The title card implementation in `S00-ColdOpen/ColdOpenSection.tsx` (VISUAL_04, lines 117-157) captures the core visual design accurately. Typography, color palette, title text, code backdrop, and the blue glow are all present and closely match the spec. The fundamental look of the title card is correct.

The primary gap is **timing and pacing**. The spec envisions the title card as a 10-second contemplative beat -- the "poster frame" of the entire video. The title arrives over 2 seconds as background code recedes, then holds in silence for 6 seconds, allowing the rhetorical question "So why are we still patching?" to resonate. This stillness is described as giving "the title weight."

The implementation compresses VISUAL_04 to under 2 seconds. The title fades in and the cold open ends almost immediately. The viewer barely has time to read the title, let alone contemplate it. This is consistent with the overall pattern of the implemented cold open being ~19 seconds versus the spec's ~2:00 timeline.

The secondary gap is **transition quality**. The spec describes a smooth crossfade where code dims, editor chrome fades, terminal disappears, vignette frames the title, and the glow blooms -- a choreographed sequence. The implementation uses a hard cut between visual states (the `activeVisual` switching logic at lines 18-24), so VISUAL_03 elements vanish instantly when VISUAL_04 begins.

The `01-ColdOpen/` directory contains an alternative implementation (`ColdOpenSplitScreen.tsx`) that covers the split-screen sock/code sequence (0:00-0:38 in spec), but does not include a title card component. The title card exists only in `S00-ColdOpen/ColdOpenSection.tsx`.

**Files reviewed:**
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/ColdOpenSection.tsx` (primary implementation, VISUAL_04 at lines 117-157)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/constants.ts` (timing at lines 42-43)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/01-ColdOpen/ColdOpenSplitScreen.tsx` (alternative composition, no title card)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/01-ColdOpen/constants.ts` (alternative timing)
