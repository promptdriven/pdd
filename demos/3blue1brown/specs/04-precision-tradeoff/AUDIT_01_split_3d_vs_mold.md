# Audit: Split Screen - 3D Printer vs Injection Mold (01_split_3d_vs_mold)

## Status: PASS

### Requirements Met

1. **Video Base Layer** (spec line 102): The spec requires `<Video src="3d_vs_mold.mp4" />` inside an `<AbsoluteFill>`. The implementation at `SplitComparison.tsx:22-26` renders an `<OffthreadVideo>` with `src={staticFile("split_3d_vs_mold.mp4")}` inside `<AbsoluteFill>`. `OffthreadVideo` is Remotion's performant, thread-offloaded variant of `<Video>` -- functionally equivalent and preferred for production. The filename differs slightly (`split_3d_vs_mold.mp4` vs `3d_vs_mold.mp4`), which is acceptable since the spec filename was illustrative.

2. **Center Divider Element** (spec lines 105-112): The spec requires a `<div>` with `position: absolute`, `left: 50%`, `top: 0`, `width: 2`, `height: 100%`, and white background color. The implementation at `SplitComparison.tsx:31-42` provides all of these properties exactly. The `backgroundColor` is set via `COLORS.DIVIDER_WHITE` which resolves to `"#ffffff"` (`constants.ts:21`).

3. **Divider Opacity Animation** (spec lines 92-96): The spec requires opacity interpolation from 0 to 0.5 over frames [0, 30] with `extrapolateRight: 'clamp'`. The implementation at `SplitComparison.tsx:13-17` performs exactly this interpolation using `BEATS.DIVIDER_FADE_START` (0) and `BEATS.DIVIDER_FADE_END` (30) from `constants.ts:14-16`, and caps the max at the `dividerOpacityMax` prop which defaults to 0.5. The `extrapolateRight: "clamp"` option is present.

4. **Divider Opacity via rgba vs. separate property** (spec line 111): The spec uses `rgba(255, 255, 255, ${dividerOpacity})` as `backgroundColor`. The implementation instead uses a solid `backgroundColor: "#ffffff"` with a separate `opacity` CSS property set to the interpolated value. These are visually identical when the divider is the only element with that background -- the rendered result is the same white-at-half-opacity line.

5. **Duration and Frame Rate** (spec line 5): The spec states ~15 seconds. `constants.ts:4-7` defines `SPLIT_COMPARISON_FPS = 30` and `SPLIT_COMPARISON_DURATION_SECONDS = 15`, yielding `SPLIT_COMPARISON_DURATION_FRAMES = 450`. This matches the spec.

6. **Resolution** (spec line implied): `constants.ts:8-9` defines 1920x1080, matching standard HD resolution consistent with the rest of the project.

7. **Minimal Overlay** (spec line 85): The spec states "Minimal overlay for this section - the video carries the message." The implementation matches this: only a single divider line is rendered over the video, with no text, labels, or additional graphics.

8. **Integration into Section 4** (spec line 141, narration sync): The `Part4PrecisionTradeoff.tsx:39-43` renders `SplitComparison` as `activeVisual === 0` starting at `BEATS.VISUAL_00_START` (frame 0, 0.0s). The narration line "Here's something subtle that changes how you think about prompts" is synced to this segment per `S04-PrecisionTradeoff/constants.ts:9`.

9. **Configurable Props with Zod Validation** (beyond spec): `constants.ts:25-35` defines a Zod schema with `showDivider` (boolean, default true) and `dividerOpacityMax` (number, default 0.5). The component signature at `SplitComparison.tsx:6-8` destructures these with matching defaults. This adds flexibility beyond the spec baseline.

10. **Module Structure and Exports**: `index.ts` cleanly re-exports the component, constants, props schema, and defaults. The module is properly consumed by `Part4PrecisionTradeoff.tsx:10`.

### Issues Found

None. All spec requirements are fully satisfied.

### Notes

- The implementation adds `transform: "translateX(-50%)"` to the divider (`SplitComparison.tsx:40`). The spec does not include this, but it is a sub-pixel centering improvement that ensures the 2px divider is perfectly centered at the 50% mark rather than starting at 50% and extending 2px to the right.
- The `<OffthreadVideo>` element includes `loop` and `style={{ objectFit: "cover" }}` attributes (`SplitComparison.tsx:24-26`) not present in the spec. `loop` ensures the 15-second source video does not show a blank frame if the composition duration extends beyond it, and `objectFit: "cover"` ensures proper scaling to fill the frame. Both are sensible production defaults.
- The on-screen duration of this visual in the parent composition is approximately 3 seconds (frames 0 to ~91), governed by `VISUAL_00_END: s2f(3.02)` in the parent constants. The 15-second duration in the spec header refers to the Veo-generated source video file length. The actual screen time is dictated by narration sync -- the next narration segment ("In 3D printing, there's no mold") begins at 4.4s, so the visual correctly transitions before then.
- The spec's "Post-Production (Remotion Overlay)" section provides reference TypeScript code. The implementation follows the architectural intent of that code (AbsoluteFill > Video + divider overlay) while making appropriate Remotion best-practice adaptations (OffthreadVideo, staticFile, externalized constants, Zod props).

### Resolution Status: RESOLVED
