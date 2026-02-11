# Scene Audit: S01 V18 - Veo Developer Edit (OffthreadVideo)

**Status:** NEEDS_FIX

**Section:** S01 Part 1 Economics
**Time range:** 292.48s - 319.86s (27.38s duration)
**Component:** OffthreadVideo with `veo_developer_edit.mp4`
**Source file:** `remotion/src/remotion/S01-Economics/Part1Economics.tsx` (lines 184-194)

---

## Summary

The Veo clip `veo_developer_edit.mp4` is only **8 seconds** long but the scene runs for **27.38 seconds**. Although the `loop` attribute is set on `<OffthreadVideo>`, looping is **not functioning** in the rendered output. The clip plays once and then **freezes on its last frame** for the remaining ~19 seconds.

## Evidence

### Frame Analysis

| Timestamp | Description | Motion? |
|-----------|-------------|---------|
| t=293s | Developer smiling, hands on keyboard, blue reflection in glasses | YES - clip playing |
| t=295s | Different pose from t=293 (pixel diff: 44.01) | YES - clip playing |
| t=297s | Different pose from t=295 (pixel diff: 37.77) | YES - clip playing |
| t=299s | Different pose from t=297 (pixel diff: 34.27) | YES - clip playing |
| t=301s | Identical to t=299 (pixel diff: 0.00) | **FROZEN** |
| t=303s-t=319s | All identical to t=301 (pixel diff: 0.00) | **FROZEN** |

### Pixel Difference Data

- Active motion period (t=293 to t=299): Consecutive frame diffs of 29-44
- Frozen period (t=301 to t=319): Consecutive frame diffs of 0.00
- Freeze onset: ~t=300.5s (292.48 + 8.0 = 300.48s, matching the clip's 8s duration)

### Clip Properties

- `veo_developer_edit.mp4` duration: **8.000 seconds** (192 frames)
- Scene duration: **27.38 seconds** (822 frames at 30fps)
- Clip-to-scene ratio: clip covers only 29% of the scene

## Frozen Frame Description

The frozen frame shows the developer in a thoughtful pose -- hand on chin, looking at monitor, red/orange reflection in glasses, navy hoodie, gray background. This static image persists for approximately 19 seconds, which is the majority of the scene.

## Previous Section-Level Audit Note

The section-level audit reported this as "GOOD" and stated the freeze was "FIXED (loop added)." However, the detailed pixel analysis proves that the loop is not functioning in the actual rendered output. The section audit may have been comparing t=294 (first play) with t=310 (frozen frame) which do show different content, but this is because t=294 is early in the first play and t=310 is stuck on the last frame -- not because the clip is looping.

## Root Cause

The `<OffthreadVideo loop>` component at line 187-191 of `Part1Economics.tsx` has the `loop` attribute, but the Remotion `OffthreadVideo` component may not be honoring it correctly during rendering. Possible causes:

1. `OffthreadVideo` `loop` prop may not work as expected during server-side rendering / final render (as opposed to preview)
2. The `<Sequence from={BEATS.VISUAL_18_START}>` wrapper may interfere with video looping by providing a timeline context that doesn't reset

## Recommended Fix

Option A: Replace `loop` with explicit `startFrom` and `endAt` props combined with manual looping via multiple `<Sequence>` wrappers, each offset by the clip duration (8s = 240 frames at 30fps).

Option B: Pre-process the Veo clip to be at least 28 seconds long (4 concatenated copies) using ffmpeg:
```bash
ffmpeg -stream_loop 3 -i veo_developer_edit.mp4 -c copy -t 28 veo_developer_edit_looped.mp4
```

Option C: Use Remotion's `<Loop durationInFrames={240}>` wrapper around the `<OffthreadVideo>`:
```tsx
<Loop durationInFrames={240}>
  <OffthreadVideo
    src={staticFile("veo_developer_edit.mp4")}
    style={{ width: "100%", height: "100%" }}
  />
</Loop>
```

---

**Audited:** 2026-02-09
**Frames extracted:** t=293, t=294, t=295, t=297, t=299, t=301, t=303, t=305, t=307, t=308, t=309, t=311, t=313, t=315, t=317, t=318, t=319
