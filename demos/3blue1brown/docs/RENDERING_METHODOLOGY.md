# Script-to-Video Rendering Methodology

Lessons learned from debugging the cold open section. This document codifies the
end-to-end process for turning a written script into a rendered Remotion video
with Veo-generated footage and programmatic animations.

---

## Phase 1: Script Decomposition

### 1.1 Map narration segments to visual beats

The script describes visuals alongside narration, but TTS audio is often
**condensed** from the full script. The narration audio is the source of truth
for timing, not the script's timestamp estimates.

**Process:**
1. Generate TTS audio from the narration text
2. Run Whisper to get `word_timestamps.json` with segment boundaries
3. Map each Whisper segment to the script's visual description
4. Document the mapping explicitly, noting where condensed narration merges
   multiple script beats into one segment

**Mistake we made:** Assumed the 5 Whisper segments mapped 1:1 to the first 5
script visual beats. In reality, the condensed narration reshuffled which visuals
belong to which audio segment (e.g., "60 years ago, when socks got cheap enough,
she stopped" covered the sock-toss beat, not the completion beat).

### 1.2 Identify visual types per segment

Every segment needs exactly one of:

| Prefix | Source | When to use |
|--------|--------|-------------|
| `veo:filename` | Veo-generated video clip | Live-action footage, establishing shots, character scenes |
| `ComponentName` | Remotion animation | Data visualizations, charts, diagrams, abstract concepts |
| `title:Text` | Inline title card | Simple text on solid background |
| `title_over_code:Text` | Title over code backdrop | Title cards that layer over previous visual context |
| `code_regen:label` | Code animation | Code deletion/regeneration sequences |

**Mistake we made:** Initially used a Remotion animation (`DeveloperEditZoomout`)
for segments that needed video footage. A 10-second animation crammed into a
1-2 second window showed only its first frames. Rule: **match the visual type
to the segment duration and content requirements.**

### 1.3 Audit for production gaps

Before any generation, walk through every segment and verify that either:
- A Veo clip exists (or will be generated) for it, OR
- A Remotion component exists (or will be created) for it

**Mistake we made:** The spec only produced Veo clips for the first half of the
cold open. The second half (sock toss, code regeneration, title card) had no
planned visuals. This wasn't caught until after multiple render iterations.

**Checklist:**
```
For each segment in visual_sequence:
  [ ] Visual source identified (veo clip / remotion component / inline)
  [ ] Asset exists or generation is planned
  [ ] Duration is compatible (Veo clips are 8s; animations have their own timing)
  [ ] Character consistency requirements documented
```

---

## Phase 2: Veo Clip Generation

### 2.1 Always use reference images

Veo generates different-looking people every time unless constrained by a
reference image. This is the single biggest source of visual inconsistency.

**Process:**
1. Generate reference images first: `python tools/veo/generate_references.py`
2. Always generate with: `--use-references --separate-sides`
3. Verify character consistency after EVERY generation by extracting frames

```bash
# Extract a frame for visual inspection
ffmpeg -ss 2 -i output.mp4 -vframes 1 -q:v 2 check_frame.png
```

**Mistake we made:** Clips 01c, 01d, and 01e were generated without reference
images (or references failed to constrain the output for wide shots). The
developer changed from white to Black between clips. This required multiple
re-generation cycles to fix.

### 2.2 Reference images must match the scene type

Even with reference images, Veo may ignore them when the scene description
diverges significantly from the reference (e.g., a close-up portrait reference
used for a wide zoom-out shot).

**Mitigation:**
- For wide/zoom shots, the reference image still helps but results are less
  reliable. Always verify the output.
- Consider generating multiple candidates and selecting the best match.
- If consistency fails, regenerate the specific clip individually with
  `--segment ID --use-references`.

### 2.3 Split-screen vs full-frame clips

Split-screen clips (developer + grandmother) require separate left/right
generation in 9:16 vertical format, then compositing:

```bash
# Generate
python tools/veo/generate_segments.py --use-references --separate-sides --segment 01a

# Composite
python tools/veo/composite_segments.py --segment 01a
```

Full-frame clips (e.g., modern sock toss scene) generate directly in 16:9:

```bash
python tools/veo/generate_segments.py --segment 01f
```

**Key:** Full-frame clips use different characters/scenes by design. Don't force
reference images onto scenes that are intentionally showing different people.

### 2.4 Post-generation verification checklist

After every Veo generation run:

```
[ ] Extract frame from each clip and visually inspect
[ ] Character appearance matches reference images
[ ] Scene matches the script's visual description
[ ] No artifacts, frozen frames, or black segments
[ ] Clip duration is sufficient for the segment it will fill
[ ] Copy verified clips to remotion/public/ with correct filenames
```

---

## Phase 3: Remotion Composition

### 3.1 OffthreadVideo timing: always wrap in Sequence

**Critical bug:** Remotion's `<OffthreadVideo>` seeks to the composition's
absolute frame time, NOT relative to when the clip appears. If a clip is 8
seconds long and the segment starts at 10 seconds, OffthreadVideo tries to
seek to 10s in an 8s clip, showing a frozen last frame.

**Fix:** Always wrap `<OffthreadVideo>` in a `<Sequence from={startFrame}>`:

```tsx
// WRONG - video freezes for segments starting after clip duration
<OffthreadVideo src={staticFile("clip.mp4")} />

// CORRECT - Sequence resets video playback to 0 at segment start
<Sequence from={BEATS.VISUAL_03_START}>
  <OffthreadVideo src={staticFile("clip.mp4")} />
</Sequence>
```

The generator (`generate_section_compositions.py`) handles this automatically
for `veo:` prefixed entries. Never bypass it.

### 3.2 interpolate() requires strictly increasing input ranges

Remotion's `interpolate()` requires input ranges to be **strictly monotonically
increasing**. No duplicate values allowed.

```tsx
// WRONG - duplicate 10 causes runtime error
interpolate(frame, [0, 10, 10, 25], [1, 1, 1, 0])

// CORRECT - use 11 instead of second 10
interpolate(frame, [0, 10, 11, 25], [1, 1, 1, 0])
```

For "hold then fade" patterns, offset the second value by 1 frame. At 30fps,
a 1-frame difference (33ms) is imperceptible.

### 3.3 Frame math for short segments

When a segment is only 1-2 seconds (30-60 frames), animation timing must be
compressed accordingly. Standard Remotion components designed for 10-20 second
durations will only show their first few frames.

**Rules:**
- Calculate available frames: `(segment_end - segment_start) * FPS`
- Design animations to complete within 80% of available frames
- For <1s segments, use simple crossfades rather than multi-phase animations
- The `activeVisual` pattern means the last segment plays until composition end
  (not just until its BEAT end), giving it extra time

### 3.4 useCurrentFrame() scope

`useCurrentFrame()` returns the frame relative to the **innermost** `<Sequence>`.
However, in the section composition pattern, `frame` is captured at the top
level (outside all Sequences). So manual offset calculation is needed:

```tsx
const frame = useCurrentFrame(); // absolute composition frame

// Inside a conditional render:
opacity: interpolate(frame - BEATS.VISUAL_03_START, [0, 15], [0, 1], ...)
//                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//                   manual offset to get "local" frame
```

---

## Phase 4: Generator Pipeline

### 4.1 Visual sequence format

Each entry in `visual_sequence` is a tuple:
```python
(whisper_seg_start, whisper_seg_end, "visual_id", "description")
```

The `visual_id` determines how the generator produces JSX:

| Prefix | Generator behavior |
|--------|-------------------|
| `veo:filename` | `<OffthreadVideo>` wrapped in `<Sequence>` |
| `title:Text` | Centered text with fade-in on dark background |
| `title_over_code:Text` | Text fade-in over dimmed code backdrop |
| `code_regen:label` | Inline code dissolution + regeneration animation |
| bare name | Imports and renders Remotion component with default props |

### 4.2 Adding new visual types

When the script requires a visual that doesn't fit existing types:

1. Add a new prefix (e.g., `code_regen:`) to the generator
2. Update the `has_*` detection flags in `generate_component()`
3. Update the Remotion import list (e.g., add `interpolate` if needed)
4. Add the `elif` template branch in the switch_cases builder
5. Test with `python tools/generate_section_compositions.py`
6. Verify generated TSX compiles: `npx remotion render ... --frames=0-1`

**Python f-string escaping for JSX:**
```
Python f-string    Output (TSX)      Meaning
──────────────     ────────────      ───────
{{                 {                 JSX expression start
}}                 }                 JSX expression end
{{{{               {{                JSX inline style start
}}}}               }}                JSX inline style end
${{expr}}          ${expr}           JS template literal interpolation
{{ key: "val" }}   { key: "val" }    JS object literal
{i:02d}            03                Python variable substitution
\\n                \n                JS string newline escape
```

### 4.3 End-to-end generation + render

```bash
cd demos/3blue1brown

# 1. Generate section compositions (constants.ts, Component.tsx, index.ts)
python tools/generate_section_compositions.py

# 2. Render the section
cd remotion
npx remotion render src/remotion/index.ts ColdOpenSection \
  --output ../outputs/sections/cold_open.mp4 --overwrite

# 3. Verify by extracting frames at segment boundaries
for t in 2 6 10 13 15; do
  ffmpeg -ss $t -i ../outputs/sections/cold_open.mp4 \
    -vframes 1 -q:v 2 check_t${t}s.png
done
```

---

## Phase 5: Verification

### 5.1 Frame-by-frame segment audit

After every render, extract a frame from the middle of each segment and verify:

```
[ ] Correct visual for this narration segment
[ ] Character consistency across all Veo clips
[ ] No frozen/still frames (file size should be >10MB for 19s video with motion)
[ ] Animations complete within their segment window
[ ] Title cards readable and properly positioned
[ ] Audio-visual sync feels natural
```

### 5.2 File size as a smoke test

A 19-second 1080p video with actual motion should be 10-20MB. If the file is
suspiciously small (<5MB), segments likely contain still frames or black.

| File size | Likely cause |
|-----------|-------------|
| <5 MB | Multiple frozen/black segments |
| 5-10 MB | Some segments are still frames |
| 10-20 MB | Normal range for mixed video + animation |
| >25 MB | Unusual; check if clips are duplicated |

---

## Common Pitfalls Summary

| # | Pitfall | Prevention |
|---|---------|-----------|
| 1 | All segments show same clip | Verify visual_sequence maps to distinct assets |
| 2 | Character changes between clips | Always use `--use-references` for Veo generation |
| 3 | Video freezes after 8s | Wrap OffthreadVideo in `<Sequence from={startFrame}>` |
| 4 | Script visuals have no corresponding asset | Audit every segment for production gaps before rendering |
| 5 | Long animation in short segment | Match component duration to segment duration |
| 6 | Title on black instead of over context | Use `title_over_code:` prefix for layered title cards |
| 7 | interpolate() runtime error | Ensure input arrays are strictly increasing (no duplicates) |
| 8 | Veo ignores reference for wide shots | Verify every clip post-generation; regenerate individually if needed |
| 9 | Wrong segment-to-script mapping | Map from Whisper timestamps (actual audio), not script estimates |
| 10 | Mixed visual styles (Veo + Remotion) | Keep visual style consistent within a section; don't mix unless intentional |

---

## Workflow Diagram

```
Script (main_script.md)
  |
  v
TTS Generation --> word_timestamps.json (Whisper segments)
  |
  v
Visual Beat Mapping (segment -> script visual -> asset type)
  |
  +---> Veo Clips                    +---> Remotion Components
  |     1. Generate references       |     1. Check component exists
  |     2. Generate with refs        |     2. Verify duration fits segment
  |     3. Composite split-screen    |     3. Test standalone render
  |     4. Verify characters         |
  |     5. Copy to public/           |
  |                                  |
  +---> Inline Animations (code_regen, title_over_code, etc.)
  |     1. Add prefix to generator
  |     2. Test f-string escaping
  |
  v
generate_section_compositions.py --> constants.ts + Component.tsx + index.ts
  |
  v
npx remotion render --> section.mp4
  |
  v
Frame Extraction Verification
  |
  v
Ship
```
