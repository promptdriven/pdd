# Scene Audit: S00 Cold Open - V1 Veo Zoom Out Reveal

**Video:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/outputs/sections/cold_open.mp4`
**Time range:** 5.24s - 7.72s
**Script visual:** "Zoom out on the LEFT: The single edit is revealed to be one of thousands of patches in a massive codebase. Files everywhere, diff markers, TODO comments. Zoom out on the RIGHT: Grandmother's drawer opens--dozens of carefully mended socks, shirts, trousers."
**Spec:** `specs/00-cold-open/01d_zoom_out_reveal.md`
**Date:** 2026-02-09

## Frames Examined
- t=5s: Split screen maintained. LEFT: Same close-up framing as V0 -- developer at keyboard, monitor edge visible, no zoom-out yet. Appears to be the tail end of the previous scene or start of transition. RIGHT: Grandmother in same close framing as V0, still working on sock with darning egg.
- t=6s: SIGNIFICANT CHANGE. LEFT: Camera has pulled back substantially. Developer now visible at mid-distance, sitting at desk with monitor. Multiple screens/windows of code now visible -- floating code panels with syntax highlighting (red, green, blue text) surround the developer. A small red dot/indicator visible on one screen. Blue ambient lighting fills the room. RIGHT: Camera has also pulled back. Grandmother now visible full-body seated in chair. Oil lamp visible on side table. She is working with the sock in her lap. Warm amber lighting. A thin bright vertical line divides the halves.
- t=7s: LEFT: Zoom out continues further. Developer is smaller in frame. Multiple code editor windows/floating panels surround the workspace -- at least 4-5 visible panels with colored syntax-highlighted code. Some panels show red/orange text (suggesting errors, diffs, or warnings). The sense of accumulated code complexity is building. RIGHT: Grandmother remains seated, working. Oil lamp on table. More of the room is visible but no drawer/basket of additional mended garments is revealed. She appears to be working on the same single sock. Dark vignette around edges.

## Assessment

### Matches Script
- Dolly zoom out is present and active on BOTH sides simultaneously -- matches script and spec
- LEFT zoom reveals multiple code files/windows surrounding the developer -- matches "one of thousands of patches" concept directionally
- LEFT side shows floating code panels with syntax highlighting and colored text -- partially matches "diff markers" concept
- Camera movement is smooth and cinematic -- matches spec
- Cool blue (left) vs warm amber (right) color temperature contrast maintained throughout zoom -- matches spec
- Developer becomes progressively smaller in frame as complexity is revealed -- matches spec
- Split screen with vertical divider maintained -- matches spec

### Issues Found
| # | Severity | Description | Fix Suggestion |
|---|----------|-------------|----------------|
| 1 | MAJOR | RIGHT side does NOT show the "zoom out reveal" described in the script. The script says "Grandmother's drawer opens--dozens of carefully mended socks, shirts, trousers." At t=7s, the grandmother is still working on a single sock with no drawer, basket, or collection of mended garments visible. The right-side zoom out reveals more of the room but not accumulated repair work. | The right side needs to reveal an overflowing mending basket or open drawer with dozens of repaired garments. This is a key narrative beat -- the "weight of accumulated work" on both sides. If this is a Veo limitation, consider compositing additional mended garments into the scene, or regenerating the right-side Veo clip with stronger emphasis on the basket/drawer reveal. |
| 2 | MAJOR | The scene is only 2.48 seconds long (5.24-7.72s) but the spec calls for a 14-second zoom out with detailed timing breakdown. The zoom begins and the complexity starts to build, but the clip ends before the full reveal can complete. At t=7s we see only the beginning of the complexity -- not the full "codebase chaos" or "full mending collection" that the spec's final frame describes. | This appears to be an intentional editorial choice to use only the first portion of the zoom, with V1B presumably holding the zoomed-out frame. However, the truncation means neither side reaches the full "overwhelming accumulated work" state described in the spec. Verify that V1B (7.72-13.72s) shows the final zoomed-out state with full complexity visible. |
| 3 | MODERATE | LEFT side shows multiple code windows but no visible "TODO", "FIXME", or floating text labels as described in the spec. No tangled dependency lines visible either. The code panels are present but lack the specific annotation overlay elements. | These text overlays (TODO, FIXME, etc.) may need to be composited via Remotion if Veo cannot generate them. Consider adding them as a Remotion overlay on top of the Veo footage. |
| 4 | MINOR | At t=5s the framing appears nearly identical to V0 (the previous establish shot), with no zoom movement yet. This suggests the first ~0.76s of this scene is essentially a continuation of the static establish shot before the zoom begins. | Minor timing/editorial issue. The zoom does begin by t=6s so this is just a brief delay. |

## Status: NEEDS_FIX

**Rationale:** The LEFT side's zoom-out works reasonably well, revealing multiple code windows and building complexity, though it lacks the specific text overlays (TODO/FIXME) from the spec. However, the RIGHT side has a MAJOR issue: it fails to reveal the accumulated mending work (drawer of dozens of garments) that is central to the script's visual metaphor. The zoom out on the right merely shows more of the grandmother's room rather than the "dozens of carefully mended socks, shirts, trousers" that the script describes. This is a key narrative beat -- both sides should reveal the overwhelming weight of accumulated work -- and the right side currently does not deliver this. The 2.48-second duration also means neither side reaches the full complexity described in the 14-second spec, though this may be addressed by V1B.
