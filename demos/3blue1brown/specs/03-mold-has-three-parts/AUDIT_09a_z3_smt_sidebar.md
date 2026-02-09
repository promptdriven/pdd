# Audit: Z3 SMT Sidebar (09a)

## Status: ISSUES FOUND

### Requirements Met

1. **Composition exists**: Standalone composition at `/remotion/src/remotion/29a-Z3SmtSidebar/` with three files: `Z3SmtSidebar.tsx`, `constants.ts`, `index.ts`.

2. **Canvas and resolution**: 1920x1080 at 30fps, 20-second duration (600 frames). Background color is `#1a1a2e` per spec. All match spec exactly.

3. **Synopsys Formality icon (left)**: Checkmark icon rendered as SVG path in teal `#2AA198`. Size is 100x100 container with 80x80 SVG. Label "Synopsys Formality" in teal, 16px Inter font below icon. Fades in frames 0-60 with `easeOutCubic`. All match spec (lines 20-26, 55-59, 117-120).

4. **Z3 logo (right)**: Stylized "Z3" text in teal `#2AA198`, 48px bold JetBrains Mono font. Size is 100x100 container. Label "Z3 (Microsoft Research)" in teal, 16px Inter font below. Fades in frames 60-120 with `easeOutCubic`. Matches spec (lines 27-31, 60-65, 125-130).

5. **Bridge line connection**: Horizontal teal line 200px wide with `boxShadow: 0 0 8px` glow. Draws from left via width percentage, frames 120-180 with `easeInOutQuad`. Equals sign `=` appears at center when progress > 0.5, fading in as `(progress - 0.5) * 2`. Matches spec (lines 33-38, 67-70, 250-284).

6. **Comparison text block - three lines**:
   - "Hardware: SMT-based formal proof" -- 24px, `#B0B0C0`, frames 180-220, `easeOutCubic`.
   - "PDD: SMT-based formal proof" -- 24px, `#B0B0C0`, frames 220-260, `easeOutCubic`.
   - "Same math." -- 32px, `#FFFFFF`, bold (fontWeight 700), frames 260-300, `easeOutCubic`.
   - All text uses Inter font. Positioned at bottom 280px. Matches spec (lines 39-47, 72-77, 141-152, 206-241).

7. **"Same math." pulse**: Sinusoidal pulse after frame 300: `1.0 + Math.sin((frame - 300) * 0.08) * 0.1`. Applied as CSS `transform: scale()`. Matches spec (lines 78-87, 155-157).

8. **Sidebar accent lines**: Top and bottom teal lines at 80px from edges, inset 120px left/right, height 1px, opacity 0.3. Controlled by `showOverlay` prop. Matches spec (lines 48-51, 91-108).

9. **Beat timings in constants.ts**: All timing values match the spec animation sequence exactly:
   - SYNOPSYS: 0-60 (spec: 0-2s = 0-60 frames)
   - Z3: 60-120 (spec: 2-4s = 60-120 frames)
   - BRIDGE: 120-180 (spec: 4-6s = 120-180 frames)
   - LINE1: 180-220, LINE2: 220-260, LINE3: 260-300 (spec: 6-10s)
   - PULSE_START: 300 (spec: 10s)
   - HOLD_START: 420 (spec: 14s)

10. **Easing functions**: All match spec (line 289-293):
    - Logo fade-ins: `Easing.out(Easing.cubic)` -- matches `easeOutCubic`.
    - Bridge line: `Easing.inOut(Easing.quad)` -- matches `easeInOutQuad`.
    - Text fade-ins: `Easing.out(Easing.cubic)` -- matches `easeOutCubic`.
    - Pulse: `Math.sin` -- matches sinusoidal.

11. **Color palette**: All colors correctly defined in constants:
    - BACKGROUND: `#1a1a2e`, TEAL: `#2AA198`, MUTED_WHITE: `#B0B0C0`, BRIGHT_WHITE: `#FFFFFF`.

12. **Text content**: All text strings match spec exactly in constants.ts.

13. **Props and exports**: Zod schema with `showOverlay` boolean prop. Clean index.ts exports composition and all constants.

### Issues Found

1. **Not integrated into S03-MoldThreeParts sequence**: The `Z3SmtSidebar` composition is never imported or used in `Part3MoldThreeParts.tsx`. Instead, Visuals 8 and 9 (frames 3528-5143, covering the Z3/SMT narration from 117.6s to 171.4s) both render `TraditionalVsPdd` as a fallback. The `Z3SmtSidebar` component is not imported in `Part3MoldThreeParts.tsx` and does not appear in its import list. The VISUAL_SEQUENCE in S03 constants.ts labels these slots as "Synopsys uses SAT/SMT, PDD uses Z3, same class solver" and "Z3 proves for all inputs, symbolic reasoning, same math" -- clearly intended for this composition -- but the code still renders `TraditionalVsPdd` for both.

2. **Not registered in Root.tsx**: The `Z3SmtSidebar` composition is not registered as a `<Composition>` in `Root.tsx`. It cannot be previewed or rendered standalone from the Remotion Studio.

3. **Missing Synopsys shimmer/pulse animation**: Spec line 57 calls for a "Brief shimmer/pulse" on the Synopsys icon to signal recognition ("you remember this from Part 2"). The implementation only has a simple opacity fade-in -- no shimmer or pulse effect on the Synopsys icon itself.

4. **Missing logo pulse in unison**: Spec line 69 states "Both logos pulse gently in unison" during the bridge connection phase (frames 120-180). The implementation has no pulsing animation on either logo during this phase.

5. **Missing sidebar frame fade-in with easing**: Spec line 293 calls for sidebar frame to use `easeOutCubic` easing. The accent lines are rendered with a static opacity of 0.3 with no animated fade-in.

### Notes

- The standalone `Z3SmtSidebar` composition is faithfully implemented against the spec in terms of visual elements, colors, timings, text content, and easing curves. The core visual design matches the spec closely.
- The primary issue is integration: the composition exists but is completely disconnected from both the S03 parent sequence and the Root composition registry. In the parent sequence, `TraditionalVsPdd` is used as a placeholder for the narration segments that should show this Z3 sidebar.
- Three minor animation details are missing: the Synopsys recognition shimmer, the synchronized logo pulse during bridge drawing, and the sidebar frame animated fade-in. These are polish items that affect the "callback recognition" feel described in the spec but do not affect the core visual layout or content.
- The narration timing in S03 constants maps frames 3528-5143 (117.6s-171.4s) to the Z3/SMT content, aligning with the spec timestamp of 13:00-13:20 relative to Part 3's start. The standalone composition's own 600-frame duration (20s) would need to be coordinated with these parent sequence timings when integrated.
