# Audit: 01h_title_card.md

## Spec Summary
Title card showing "Prompt-Driven Development" centered over dimmed regenerated code (~10 seconds, 1:50-2:00):
- Clean regenerated code from 01g becomes dimmed backdrop (opacity 1.0 → 0.15)
- Editor chrome and terminal fade out completely
- Title text fades in with slight upward drift (20px → 0)
- Typography: Inter/Helvetica Neue, 72px, weight 600, warm white (#F8F4F0), tracked 0.02em
- Subtle blue glow (#4A90D9, 40px radius, opacity 0.15) behind title
- Vignette framing (edges at ~85% darkness)
- No narration - silent beat giving question from 01g room to breathe
- Optional musical cue beginning as title appears
- Final shot of Cold Open Section 0

## Implementation Status
Implemented with Deltas

## Deltas Found

### Delta 1: Timing significantly different
- **Spec says**: Duration ~10 seconds at timestamp 1:50-2:00, following 15-second 01g regeneration sequence
- **Implementation does**: VISUAL_04 runs 14.1-15.96s (423-479 frames at 30fps = 1.87 seconds), per ColdOpenSection.tsx constants.ts lines 42-43
- **Severity**: High - Duration is 5x shorter than spec (1.87s vs 10s)

### Delta 2: Code dimming implementation
- **Spec says**: "Background Code Dim - Code opacity reduces from 1.0 to 0.15 over the first 2 seconds, Terminal snippet fades out completely, Editor chrome fades out, Cursor stops blinking and disappears, Code becomes subtle texture"
- **Implementation does**: Code appears already dimmed at opacity 0.25 (line 127), no animation from 1.0 → 0.15. There is no terminal or editor chrome to fade out because they're not part of this implementation
- **Severity**: Medium - Static dim instead of animated fade

### Delta 3: Title fade-in and drift animation
- **Spec says**: "Frame 30-90 (1-3s): Title opacity: 0 → 1 (`easeOutCubic`), Title Y position: +20px → 0px (`easeOutCubic`)"
- **Implementation does**: Title fades in from opacity 0 → 1 over frames 0-60 (lines 140) and drifts from +20px → 0 (line 143), both using interpolate with extrapolateLeft/Right clamp. Animation exists but timing is different (0-2 seconds in implementation vs 1-3 seconds in spec)
- **Severity**: Low - Animation present but starts immediately instead of delayed

### Delta 4: Title positioning
- **Spec says**: "Position: centered horizontally and vertically, Centered in frame, optionally shifted ~5% above true center (more visually balanced)"
- **Implementation does**: Title container is positioned absolutely with flexbox centering (lines 136-139), no visible vertical shift above center
- **Severity**: Low - May be visually centered but not the suggested 5% above-center for balance

### Delta 5: Glow implementation
- **Spec says**: "Very faint blue glow (#4A90D9) behind title text, Bloom radius: ~40px, opacity: 0.15, glow is subtle enough to feel atmospheric"
- **Implementation does**: Text-shadow includes glow effect (line 150) `0 0 60px rgba(74, 144, 217, 0.15)` which is the right color and opacity, but radius is 60px instead of 40px. Also uses text-shadow instead of a background radial gradient
- **Severity**: Low - Glow present with slightly larger radius and different implementation technique

### Delta 6: No separate glow fade-in animation
- **Spec says**: "Frame 45-90: Glow intensity 0 → 0.15 opacity with easeOutCubic"
- **Implementation does**: Glow is part of text-shadow on title element, so it fades in with the title (0-60 frames), not on a separate delayed timeline (45-90 frames)
- **Severity**: Low - Glow timing coupled to title instead of independent

### Delta 7: Vignette implementation unclear
- **Spec says**: "Soft radial vignette, darkening edges, Center bright, edges at ~85% darkness, Frame 0-60: Vignette fades in: 0 → target opacity"
- **Implementation does**: No visible vignette implementation in VISUAL_04 code (lines 118-157). AbsoluteFill background is #1a1a2e but no radial-gradient overlay
- **Severity**: Medium - Vignette framing missing from title card

### Delta 8: No hold period
- **Spec says**: "Frame 90-270 (3-9s): Hold - Static composition, no animation, pure stillness, viewer reads and absorbs the title"
- **Implementation does**: VISUAL_04 ends at frame 479 (relative frame 56 from start at 423), meaning title is visible for 1.87s total with no extended hold period
- **Severity**: High - No contemplative hold, title appears and video ends almost immediately

### Delta 9: Typography matches well
- **Spec says**: "Font: Inter (or system sans-serif fallback), Weight: 600, Size: 72px, Color: #F8F4F0, Tracking: 0.02em, Line-height: 1.2, Alignment: Center"
- **Implementation does**: Matches exactly (lines 144-151): fontFamily "Inter, system-ui, sans-serif", fontSize 72, fontWeight 600, color "#F8F4F0", letterSpacing "0.02em", lineHeight would use default but structure is correct
- **Severity**: None - Typography implementation matches spec precisely

### Delta 10: Background code is simplified
- **Spec says**: "Dimmed code backdrop (from previous scene)" showing the regenerated clean function from 01g as texture behind title
- **Implementation does**: Shows the clean code (lines 122-132) which matches the regenerated code from VISUAL_03 (lines 98), maintaining visual continuity
- **Severity**: None - Code backdrop implemented correctly

### Delta 11: Transition notes differ from implementation
- **Spec says**: "Transition to Section 1 (Economics) can be: Hard cut, Fade to black (brief, 0.5s), or Dissolve from title card"
- **Implementation does**: VISUAL_04 ends at 15.96s which is also COLD_OPEN_DURATION_SECONDS per constants - appears to be end of cold open with no visible transition logic in ColdOpenSection.tsx
- **Severity**: Low - Transition to next section handled at higher composition level

## Missing Elements

1. **Extended hold period**: Spec describes a 6-second static hold (frames 90-270) where "pure stillness" lets the title sink in. Implementation has total duration of 1.87s with no hold.

2. **Vignette animation**: Spec includes radial-gradient vignette that fades in over first 2 seconds and frames the title card. Not visible in implementation.

3. **Glow layer as separate element**: Spec's code structure (lines 206-212) shows glow as a separate positioned div with radial-gradient and blur filter. Implementation uses text-shadow which is simpler but different.

4. **Code dimming animation**: Spec describes code fading from full opacity to 0.15 over 2 seconds. Implementation shows code pre-dimmed at 0.25.

5. **Terminal snippet fade-out**: Spec describes terminal and editor chrome fading out during title fade-in, but implementation doesn't have these elements to fade out (they're from the missing 01f/01g components).

6. **Musical cue note**: Spec mentions "if using a score, this is where the main theme could begin" around frame 30 - no audio implementation visible in code.

7. **"Poster frame" quality**: Spec emphasizes this should work as a standalone still image and be the "poster frame" of the video, suggesting it should hold longer for impact.

## Notes

The title card implementation captures the core visual design quite well - typography, color, layout, and the code backdrop are all aligned with the spec. The glow is present, though implemented differently (text-shadow vs separate gradient layer).

The major delta is **timing and pacing**. The spec describes a 10-second contemplative beat where the title appears over 3 seconds, then holds in silence for 6 seconds, allowing the rhetorical question from the previous narration ("So why are we still patching?") to resonate before the viewer.

The implementation compresses this to under 2 seconds - title fades in and the cold open ends. This loses the "breathing room" and "quiet confidence" the spec intended. The viewer barely has time to read the title, much less contemplate it.

This is consistent with the pattern seen in the other audits: the implemented cold open is significantly faster-paced than the spec (16 seconds vs the spec's apparent 2:00 timeline). The title card exists and looks right, but doesn't get its moment to land.

Recommendation: If the goal is to match spec intent, VISUAL_04 should be extended to at least 5-7 seconds total, with the title fade-in over 1.5-2 seconds followed by a static hold. However, the current fast pace may be an intentional creative decision for the final cut.
