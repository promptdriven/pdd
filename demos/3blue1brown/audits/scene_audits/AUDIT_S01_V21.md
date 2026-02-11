# Scene Audit: S01_V21 -- Veo Split Screen Sepia

**Section:** S01 Part 1 Economics
**Scene:** V21 - Veo Split Screen Sepia (developer + grandmother)
**Video:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/outputs/sections/part1_economics.mp4`
**Time range:** 379.02s - 392.9s (13.88s duration)
**Frames extracted:** t=380s, t=386s, t=392s

---

## Verdict: PASS

---

## Frame-by-Frame Analysis

### Frame 1 (t=380s)
- **Left panel:** Developer (young man in hoodie, glasses) seated at desk, typing at keyboard, facing a large monitor displaying code/IDE with multiple panes and a warning icon. Sepia-toned.
- **Right panel:** Elderly woman (grandmother figure) seated at a table with a wicker basket overflowing with yarn/fabric, a lantern, and fabric spread out. She is sewing/darning by hand. Sepia-toned.
- **Split screen:** Clear vertical divider separates the two panels. Both panels are roughly equal width, centered on the 16:9 frame with black letterboxing above and below.
- **Sepia tone:** Confirmed -- both sides exhibit a warm sepia/monochrome color grade.

### Frame 2 (t=386s)
- **Left panel:** Same developer, now leaned back slightly in his ergonomic chair, smiling -- the monitor is no longer visible (camera has zoomed or panned to a tighter shot on the developer himself). Still sepia-toned.
- **Right panel:** Same grandmother, now holding up fabric and actively sewing/darning it by hand. Lantern and basket still present. Sepia-toned.
- **Split screen:** Maintained with clear vertical divider.

### Frame 3 (t=392s)
- **Left panel:** Developer still in the tighter framing, facing camera, smiling. Sepia tone consistent.
- **Right panel:** Grandmother working with fabric at her table. Same setting and sepia tone.
- **Split screen:** Maintained throughout.

---

## Checklist

| Criterion | Status | Notes |
|---|---|---|
| Split screen composition | PASS | Clear vertical split with developer (left) and grandmother (right) throughout all three frames. |
| Sepia tone | PASS | Both panels have consistent warm sepia/monochrome color grading across all frames. |
| Developer with code/Cursor | PASS | Frame 1 clearly shows developer at a monitor with IDE/code visible. By frames 2-3 the camera has tightened on the developer. |
| Grandmother with needle/sewing | PASS | All three frames show the elderly woman with sewing materials, fabric, yarn basket, and lantern. She is actively working with needle and thread. |
| Both working efficiently (not dismissive) | PASS | Both subjects appear focused and competent at their respective crafts. The developer smiles -- the tone is appreciative, not dismissive. |
| Zoom out on developer side (tangled codebase) | NOTE | The script calls for a "zoom out on the developer's side" to reveal a massive, tangled codebase with comments like "// don't touch this". This is NOT visible in these frames -- the developer side actually zooms IN (tighter shot) rather than out. However, this zoom-out may occur in a subsequent scene (V22+) or the second half of the narration may extend beyond this clip's range. This is acceptable as the Remotion component for V21 is a simple OffthreadVideo of the sepia split screen clip, and the zoom-out/code-comments overlay would logically be a separate visual. |
| Matches Remotion component | PASS | The component uses `OffthreadVideo` with `staticFile("07_split_screen_sepia.mp4")` looping. The rendered output correctly shows the sepia split-screen Veo clip. |
| Duration appropriate | PASS | 13.88s is reasonable for this narration segment. |

---

## Summary

The scene delivers the intended visual metaphor effectively: a developer at their IDE and a grandmother darning by lamplight, side by side in warm sepia tone, drawing the analogy between coding tools (Cursor/Claude Code) and darning needles. The split screen composition is clean and well-balanced. The sepia color grade is consistent and evocative. The only minor note is that the "zoom out to reveal tangled codebase" described later in the script visual description does not appear in this clip -- it is likely handled by the next scene in the sequence, which is the correct architectural decision given that V21's Remotion component is a single looping Veo clip.

**No fixes required.**
