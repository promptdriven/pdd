# Audit: 09b_formal_verification_comparison.md

## Status: ISSUES FOUND

### Requirements Met

1. **Standalone composition created**: `FormalVerification.tsx` exists at `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/29b-FormalVerification/` with supporting `constants.ts` and `index.ts`.

2. **Canvas and resolution**: 1920x1080 at 30fps, 25 seconds (750 frames). Matches spec exactly (spec lines 13-15).

3. **Background color**: Dark `#1a1a2e` applied via `AbsoluteFill`. Matches spec (spec line 15).

4. **Center divider**: Vertical line at `left: 50%`, 1px wide, teal `#2AA198` at 30% opacity, draws from top downward using `interpolate` on frames 0-60 with `easeInOutQuad`. Matches spec (spec lines 36-38, 346).

5. **Left panel header**: "Synopsys Formality" in teal `#2AA198`, fontSize 28, fontWeight 600, Inter font. Fades in frames 0-45 with `easeOutCubic`. Matches spec (spec lines 21, 56-58, 347).

6. **Left panel circuit icon**: SVG icon with two circles connected by a line with a center dot, rendered in teal. Appears with same opacity as the left header. Matches spec intent (spec line 22).

7. **Left panel proof description**: Three-line layout -- "SMT solver proves" (fontSize 22, muted `#B0B0C0`), "RTL ≡ gates" (fontSize 28, white, fontWeight 600), "for all inputs" (fontSize 22, muted, italic). Fades in frames 90-180 with `easeOutCubic`. Matches spec (spec lines 23-25, 61-65, 280-318).

8. **Right panel header**: "PDD + Z3" in teal `#2AA198`, same styling as left. Fades in frames 180-225 with `easeOutCubic`. Matches spec (spec lines 29, 68-69, 348).

9. **Right panel code icon**: SVG icon with angle brackets and a slash (representing code), rendered in teal. Appears with right header opacity. Matches spec intent (spec line 30).

10. **Right panel proof description**: "SMT solver proves" / "code satisfies spec" / "for all inputs" with identical styling to left panel. Fades in frames 270-360 with `easeOutCubic`. Matches spec (spec lines 31-33, 72-76).

11. **Parallel structure**: Both panels use identical phrasing "SMT solver proves ... for all inputs" with matching visual styling. This is the key visual device per spec (spec line 374).

12. **Mathematical notation**: LEFT: "∀x ∈ Inputs: Synth(RTL, x) ≡ Impl(gates, x)", RIGHT: "∀x ∈ Inputs: Code(x) ⊨ Spec(x)". Rendered in Georgia serif, italic, color `#8090A0`, letterSpacing 1, fontSize 18. Fades to max opacity 0.6 over frames 360-450 with `easeOutCubic`. Matches spec (spec lines 48-51, 78-82, 322-341, 349).

13. **Shared bottom label**: "Mathematical proof, not testing." in white `#FFFFFF`, fontSize 30, fontWeight 700, Inter font. Centered at bottom, flanked by green `#5AAA6E` checkmark SVGs (28x28). Fades in frames 450-540 with `easeOutCubic`. Matches spec (spec lines 41-45, 84-88, 350).

14. **Label pulse animation**: After frame 510, sinusoidal scale oscillation `1.0 + sin((frame - 510) * 0.06) * 0.05`. Matches spec (spec lines 91-93, 351).

15. **Color palette**: All specified colors present -- BACKGROUND `#1a1a2e`, TEAL `#2AA198`, GREEN_CHECK `#5AAA6E`, BRIGHT_WHITE `#FFFFFF`, MUTED_WHITE `#B0B0C0`, MATH_GRAY `#8090A0`. Matches spec throughout.

16. **Animation sequence timing**: Divider (0-60), left header (0-45), left text (90-180), right header (180-225), right text (270-360), math notation (360-450), bottom label (450-540), pulse starts at 510. All frame ranges match the spec's animation sequence (spec lines 55-94).

17. **All easing functions correct**: Divider uses `easeInOutQuad`, all other fades use `easeOutCubic`, pulse uses manual `Math.sin`. Matches spec (spec lines 346-351).

18. **Text content accurate**: All text strings in `constants.ts` match spec verbatim -- headers, prefixes, relations, qualifiers, math formulas, and bottom label.

### Issues Found

1. **Composition not registered in Root.tsx**: The `FormalVerification` component is not imported or registered as a `<Composition>` in `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/Root.tsx`. It cannot be previewed or rendered in the Remotion Studio. The composition files exist but are effectively orphaned.

2. **Not integrated into S03-MoldThreeParts sequence**: The `Part3MoldThreeParts.tsx` orchestrator does not import or use `FormalVerification`. The narration segments at visuals 8 and 9 (frames ~3528-5143, covering the Z3/SMT narration at ~117s-171s) reuse `TraditionalVsPdd` instead of using this dedicated `FormalVerification` composition. The spec calls for this as a distinct side-by-side comparison (spec section 9b), but the parent sequence does not incorporate it.

3. **Missing subtle background patterns**: The spec calls for "subtle circuit-board pattern in background at low opacity" on the left panel (spec line 26) and "subtle code-pattern in background at low opacity" on the right panel (spec line 34). The implementation has no background patterns in either panel -- just plain backgrounds.

4. **Missing breathing animation during hold**: The spec states frames 540-750 should have "subtle breathing animation (very slight scale oscillation)" on the full composition (spec line 92). The implementation only pulses the bottom label text, not the full composition. The panels themselves have no breathing/oscillation effect during the hold period.

5. **Missing "not testing" strikethrough effect**: The spec states the bottom label should have "the word 'not testing' draws a subtle strikethrough on an implied 'testing' concept" (spec line 87). The implementation renders the bottom label as plain text without any strikethrough visual effect.

6. **Missing panel glow during hold**: The spec states "both panels glow slightly in unison" at frames 450-540 and during the hold (spec line 88). There is no glow effect applied to either panel at any point.

7. **Math notation font family deviation**: The spec calls for "CMU Serif, Georgia, serif" (spec line 334) as the font family for mathematical notation. The implementation uses "Georgia, serif" only, omitting the preferred CMU Serif (Computer Modern Unicode) typeface.

8. **Panel padding deviation**: The spec's code reference shows `padding: '80px 60px'` (spec line 194-195), meaning 80px vertical and 60px horizontal. The implementation uses `LAYOUT.PANEL_PADDING_V = 100` and `LAYOUT.PANEL_PADDING_H = 80`, which is larger padding than specified.

9. **Left text fade timing slightly adjusted**: The spec code shows `leftTextOpacity` interpolating over frames `[90, 150]` (spec line 143-144), but the implementation uses `[90, 180]` (constants.ts line 17-18). This makes the left text fade-in 30 frames slower than the spec's code reference. However, this aligns with the prose description "Frame 90-180 (3-6s): Left panel text" (spec line 61), so this may be intentional to match the prose over the code snippet.

10. **Right text fade timing slightly adjusted**: Similarly, the spec code shows `rightTextOpacity` over `[270, 330]` (spec line 153-154), but implementation uses `[270, 360]` (constants.ts line 21-22). Same rationale as above -- matches the prose "Frame 270-360 (9-12s)" (spec line 72).

11. **Math notation fade timing adjusted**: Spec code shows `[360, 420]` (spec line 158-159) but implementation uses `[360, 450]` (constants.ts line 23-24). The prose says "Frame 360-450" (spec line 78) so this matches the prose description.

### Notes

The core visual composition is well-implemented. The side-by-side parallel structure, the central visual device of this section, is faithfully reproduced. All text content, color values, and the fundamental animation sequence are correct.

The two critical issues are:

1. **Registration gap**: The composition exists as standalone files but is not registered in Root.tsx or used in the S03-MoldThreeParts parent sequence. This means it currently cannot be rendered. The narration segments covering the formal verification comparison (roughly 117s-171s in the Part 3 narration) currently fall through to `TraditionalVsPdd` rather than this dedicated composition.

2. **Missing visual polish**: Several spec-defined visual enhancements are absent -- background patterns, full-composition breathing animation, panel glow effects, and the strikethrough on "testing." These are secondary to the core layout but would elevate the visual quality to match the spec's intended polish level.

The timing discrepancies between the spec's code snippets and the implementation (items 9-11) are minor and defensible, since the implementation consistently follows the spec's prose animation sequence descriptions rather than the code snippets. The prose descriptions appear to be the authoritative source for frame ranges.
