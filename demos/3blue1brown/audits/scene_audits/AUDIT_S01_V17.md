# Audit: S01 V17 - PatchCycle

## Status: NEEDS_FIX

## Scene Details

- **Section:** S01 Part 1 Economics
- **Visual ID:** VISUAL_17
- **Time range:** 280.16s - 290.38s (10.22s duration)
- **Remotion component:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/10-PatchCycle/PatchCycle.tsx`
- **Spec file:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/specs/01-economics/10_patch_cycle.md`
- **Frames extracted:** t=281s, t=285s, t=289s

## Script Requirements

- **Visual description:** "Arrow from small-codebase fork curving upward toward large-codebase fork. Label: 'Every patch adds code.'"
- **Narration:** "And here's the catch: every patch makes the codebase bigger. So patching pushes you from the world where AI helps into the world where it doesn't."

## Spec Requirements (10_patch_cycle.md)

The spec describes a Veo 3.1 video generation shot of a developer sighing and beginning another patch cycle -- a medium shot at a workstation with cool blue monitor lighting, warm ambient light, and a "here we go again" expression. The spec treats this as the emotional low point of Part 1.

## What Is Actually Rendered

All three extracted frames (t=281s, t=285s, t=289s) show the **placeholder mode** of the PatchCycle component:

- **Frame at 281s:** Dark background with a faint blue radial glow in the center and a warm orange glow at bottom-right. The text "Patch Cycle" is visible in the center (subtitle and asset indicator are still fading in).
- **Frame at 285s:** Full placeholder displayed -- "Patch Cycle" title in white, subtitle text "Veo 3.1 -- Developer sighs, accepts, begins another patch", and a bordered monospace label reading "AWAITING VIDEO ASSET: veo_patch_cycle.mp4".
- **Frame at 289s:** Identical to the 285s frame. Static placeholder with no animation progression beyond the initial fade-in.

## Issues Found

### 1. Placeholder Rendering Instead of Final Content (Severity: HIGH)

The scene renders only a dark placeholder screen with text labels and a message stating the video asset `veo_patch_cycle.mp4` is awaited. The `usePlaceholder` prop defaults to `true` in `defaultPatchCycleProps`, and no Veo 3.1 video has been generated or placed in the `remotion/public/` directory. This means the rendered output contains no meaningful visual content for the viewer -- just a production-internal placeholder.

### 2. Script Visual Description Not Implemented (Severity: HIGH)

The script calls for "Arrow from small-codebase fork curving upward toward large-codebase fork. Label: 'Every patch adds code.'" -- a conceptual diagram-style animation showing code growth pushing from a good region to a bad region. Neither the placeholder nor the spec's Veo video concept delivers this visual. The spec describes a live-action developer shot, while the script describes a diagrammatic/schematic animation. These are fundamentally different visual concepts. The current implementation satisfies neither.

### 3. No Animated Content During 10-Second Window (Severity: MEDIUM)

After the initial ~2-second fade-in, the placeholder is completely static for the remaining ~8 seconds. The only subtle animation is the breathing glow effect (sinusoidal intensity on the radial gradients) and a barely perceptible 3% scale push-in over 10 seconds. For a 10-second slot accompanying narration about a critical conceptual insight, this is visually inert.

### 4. Production Labels Visible in Final Output (Severity: HIGH)

The text "AWAITING VIDEO ASSET: veo_patch_cycle.mp4" is rendered in the final exported video. This is production-internal information that should never appear in a viewer-facing output. If this video were distributed, it would look unfinished.

## Comparison Summary

| Criterion | Expected | Actual | Match |
|-----------|----------|--------|-------|
| Arrow from small to large codebase | Conceptual diagram with arrow and fork visuals | Dark placeholder with text labels | NO |
| Label: "Every patch adds code" | Visible label in scene | No such label; only "Patch Cycle" title | NO |
| Narration sync | Visual reinforces "patching pushes you to worse world" | Placeholder conveys no conceptual meaning | NO |
| Duration alignment | 10.22s of content | 10.22s of static placeholder | PARTIAL (timing correct) |
| Production-ready output | Final visual suitable for viewers | Contains "AWAITING VIDEO ASSET" text | NO |

## Recommendations

1. **Decide on visual approach:** The script describes a diagrammatic arrow animation, while the spec describes a live-action Veo 3.1 developer shot. These need to be reconciled. The diagrammatic approach (arrow from small-codebase fork to large-codebase fork with "Every patch adds code" label) would be more in the 3Blue1Brown style and could be implemented entirely in Remotion without waiting for a Veo video asset.

2. **If keeping the Veo approach:** Generate the `veo_patch_cycle.mp4` asset, place it in `remotion/public/`, and set `usePlaceholder` to `false` in the default props.

3. **If switching to diagrammatic approach:** Rewrite the PatchCycle component to render an animated arrow/curve from a small codebase representation to a large codebase representation, with the label "Every patch adds code" appearing in sync with the narration.

4. **Regardless of approach:** Remove or gate the "AWAITING VIDEO ASSET" text so it never appears in exported video.

## Verdict: NEEDS_FIX

The scene currently renders a static production placeholder with internal asset-tracking text. It does not match the script's visual description (arrow diagram), does not match the spec's visual description (developer video), and is not suitable for viewer-facing output. The timing slot is correctly wired, and the Remotion infrastructure (composition registration, Part1Economics integration) is in place, but the visual content itself is entirely missing.
