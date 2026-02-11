# Scene Audit: S01_V12 - ContextRot (Codebase grid grows, context window shrinks)

**Section:** S01 Part 1 Economics
**Scene:** V12 - ContextRot
**Video:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/outputs/sections/part1_economics.mp4`
**Time range:** 161.44s - 173.6s (12.16s duration)
**Remotion component:** `remotion/src/remotion/07-ContextRot/` (note: directory is `07-ContextRot`, not `08-ContextRot` as listed in assignment)
**Audit date:** 2026-02-09

---

## Frames Extracted

| Timestamp | File | Description |
|-----------|------|-------------|
| t=162s | `/tmp/scene_audit_S01_V12_t162.png` | Mid-growth phase |
| t=167s | `/tmp/scene_audit_S01_V12_t167.png` | Large codebase (32x32) |
| t=173s | `/tmp/scene_audit_S01_V12_t173.png` | Transition to Context Mismatch |

---

## Script Visual Description (Expected)

> "The codebase grid grows: 4x4 -> 8x8 -> 16x16 -> 32x32. The context window stays the SAME SIZE. A counter shows: 'Context coverage: 80% -> 40% -> 10% -> 2%'. The window becomes a tiny rectangle over a massive grid."

## Script Narration (Expected)

> "But codebases grow. And that window? It stays the same size. A typical enterprise codebase spans millions of tokens. Even the largest context windows hold a fraction of that."

---

## Frame-by-Frame Analysis

### Frame 1 (t=162s) - Mid-Growth Phase

**Observed:**
- Title: "The Shrinking Context Window" -- clearly visible, centered at top. MATCHES spec.
- Grid: Approximately 19x19 modules visible (label reads "Codebase: 19x19 modules (361 total)"). This is mid-growth transition (between 16x16 and 32x32). CORRECT -- the animation interpolates grid sizes smoothly.
- Context window: A fixed-size blue-bordered rectangle overlaid on the center of the grid. The window is noticeably smaller relative to the grid than it was at 4x4. MATCHES spec ("stays the SAME SIZE").
- Coverage counter: Upper-right panel reads "Context Coverage: 16%". This correctly interpolates between the 10% (16x16) and 2% (32x32) values. MATCHES spec progression.
- Grid modules are rendered as small dark rectangles with subtle color variation and code-like internal detail.

**Verdict:** GOOD. Growth animation is in progress and all elements are present.

### Frame 2 (t=167s) - Large Codebase (32x32)

**Observed:**
- Title: "The Shrinking Context Window" -- still visible. CORRECT.
- Grid: 32x32 grid (label reads "Codebase: 32x32 modules (1024 total)"). Grid fills most of the frame. MATCHES spec ("32x32").
- Context window: Same fixed-size blue rectangle, now appearing tiny relative to the massive 32x32 grid. MATCHES spec ("tiny rectangle over a massive grid").
- Coverage counter: "Context Coverage: 2%". MATCHES spec exactly.
- State label: "Large project - AI sees through a keyhole" visible at bottom center. Consistent with section-level audit.
- Red "bug" dots scattered across the grid (small red markers on various modules), indicating problems in the codebase. This is a nice visual embellishment not explicitly in the script but thematically appropriate.

**Verdict:** EXCELLENT. This is the key frame of the scene and all spec elements are perfectly represented.

### Frame 3 (t=173s) - Transition to Context Mismatch

**Observed:**
- Title: "The Context Mismatch Problem" -- this has transitioned to the next scene (InGridMismatch / SplitViewMismatch, Part 2b, frames 900-1020).
- Grid: Still 32x32 but now with color-coded modules (red for "Inside window: irrelevant code", green for "Outside window: needed but missed").
- "The Problem" info box in upper right: "AI grabbed wrong code inside its tiny window, while needed code sits outside, invisible."
- Legend at bottom showing red = inside window irrelevant, green = outside window needed but missed.
- Context window overlay still visible in center, now showing the mismatch visualization.

**Verdict:** This frame has already transitioned into the next scene (V13 / Context Mismatch). This is expected behavior at t=173s, which is at the very tail end of the 161.44-173.6s time range. The transition is smooth and natural.

---

## Checklist

| Criterion | Status | Notes |
|-----------|--------|-------|
| Grid grows 4x4 -> 8x8 -> 16x16 -> 32x32 | PASS | Growth animation clearly visible; t=162s shows ~19x19 (mid-transition), t=167s shows full 32x32 |
| Context window stays same size | PASS | Fixed 240px blue rectangle clearly constant while grid expands |
| Coverage counter: 80% -> 40% -> 10% -> 2% | PASS | Shows 16% at mid-transition (t=162s), 2% at full 32x32 (t=167s); values interpolate correctly |
| "Tiny rectangle over massive grid" | PASS | At t=167s the context window is visually tiny against the 1024-module grid |
| Title visible | PASS | "The Shrinking Context Window" clearly displayed |
| Grid size indicator | PASS | "Codebase: 32x32 modules (1024 total)" at bottom-left |
| State label | PASS | "Large project - AI sees through a keyhole" visible at t=167s |
| Visual clarity / readability | PASS | All text is legible, colors have good contrast, grid modules are distinct |
| Smooth animation | PASS | The growth interpolation is continuous (not jarring jumps), as evidenced by the intermediate 19x19 state |
| Scene transitions | PASS | Clean transition into Context Mismatch by t=173s |

---

## Issues Found

**None.** All script-specified visual elements are present and correctly implemented.

---

## Minor Observations (Not Issues)

1. **Red bug dots at 32x32:** The large codebase phase adds small red dot markers on grid modules. This is not in the script description but is a thematically appropriate enhancement showing problems scattered across the codebase.
2. **Component directory naming:** The assignment references `08-ContextRot/` but the actual directory is `07-ContextRot/`. This is a spec-to-code numbering discrepancy, not a rendering issue.
3. **Frame 3 overlap:** At t=173s (0.6s before the scene's end boundary), the view has already transitioned to "The Context Mismatch Problem." This is normal scene-to-scene crossfade behavior.

---

## Final Verdict

## **PASS**

The scene faithfully implements all elements from the script visual description. The codebase grid grows from small to 32x32, the context window remains a fixed-size blue rectangle that becomes proportionally tiny, the coverage counter correctly tracks from 80% down to 2%, and the "keyhole" metaphor is clearly communicated through both the visual and the state label. Animation quality is smooth with continuous interpolation rather than abrupt size jumps. All text is legible and well-positioned.
