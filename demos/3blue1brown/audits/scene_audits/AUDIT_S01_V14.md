# Scene Audit: S01 V14 - ContextRot (EMNLP study / performance vs context length)

**Section:** S01 Part 1 Economics
**Scene:** V14 - ContextRot
**Time Range:** 201.16s - 230.52s (29.36s duration)
**Frames Extracted:** t=202s, t=215s, t=228s
**Remotion Component:** `remotion/src/remotion/07-ContextRot/`
**Audit Date:** 2026-02-09

---

## Script Requirements

**Visual description:** "A subtle graph inset: 'Performance vs. Context Length'. Line drops steadily. Label: 'Even with perfect retrieval, performance degrades 14-85% as context grows (EMNLP, 2025)'."

**Narration:** "A 2025 EMNLP study proved that even when the model retrieves the right information, performance still degrades... It's not about finding the right code. The extra tokens themselves hurt the model's ability to reason."

---

## Frame Analysis

### Frame at t=202s
- **Observed:** "The Consequence" chart is fully rendered. Shows the multi-line chart with Cost to Generate (blue), Patch (Small CB, orange), Patch (Large CB), True Cost (dashed), and Context Rot (shaded area) over 2015-2025. Two annotations are visible: "Faster patching -> faster growth -> faster rot" (center-right, in amber) and "Small modules. Clear prompts. Always fits in context." (bottom-left, in blue). Legend in upper-right. No PerformanceGraphInset visible.
- **Expected:** A "Performance vs. Context Length" graph inset should be appearing.

### Frame at t=215s
- **Observed:** Identical to t=202s. Same "The Consequence" chart with both annotations. Static -- no animation or transition happening. No PerformanceGraphInset visible.
- **Expected:** The performance graph inset should be prominently displayed with the declining performance line and the EMNLP citation.

### Frame at t=228s
- **Observed:** Identical to t=202s and t=215s. Same static "The Consequence" chart. No change, no PerformanceGraphInset.
- **Expected:** The performance graph inset or its aftermath (possibly transitioning out) should be visible.

---

## Technical Root Cause

The PerformanceGraphInset component **does exist** and is fully implemented (`/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/PerformanceGraphInset.tsx`). It renders a well-designed sub-visualization with:
- Title: "Performance vs. Context Length"
- A declining curve with data points modeling 14-85% degradation
- Axes labeled "Small" to "Large" (context length) and 0-100% (performance)
- Citation: "Even with perfect retrieval, performance degrades 14-85% as context grows (EMNLP, 2025)"
- Animated line drawing with fade-in/fade-out

**However, the timing offset makes it invisible during V14.** The issue is in `Part1Economics.tsx` at line 155-158:

```tsx
{activeVisual === 14 && (
  <Sequence from={BEATS.VISUAL_14_START}>
    <Sequence from={-1350}>
      <ContextRot {...defaultContextRotProps} />
    </Sequence>
  </Sequence>
)}
```

The inner `<Sequence from={-1350}>` offsets the ContextRot component so that when V14 starts at global frame 6035 (t=201.16s), the ContextRot internal clock is already at frame 1350 -- its very last frame. The PerformanceGraphInset is conditionally rendered only when `frame >= 1020 && frame < 1110` (frames 1020-1110), which corresponds to seconds 34-37 within the ContextRot's 45-second timeline. Since ContextRot is already at frame 1350+ by the time V14 begins, the inset has long since faded out.

The PerformanceGraphInset was visible briefly during V13 (around t=175-178s in the overall video), but it flashes by during that earlier scene's animation, not during V14 when the narration specifically discusses the EMNLP study.

---

## Findings

### Issue 1: PerformanceGraphInset not visible during its narrated segment
- **Severity:** MAJOR
- **Category:** Timing / Sync
- **Description:** The script calls for the "Performance vs. Context Length" graph inset to appear during the EMNLP study narration (t=201-230s). The component exists and is fully implemented, but the frame offset (`-1350`) places the ContextRot component past its end state when V14 begins. The inset was only briefly visible during V13 (around t=175-178s), completely out of sync with the narration about the EMNLP study.
- **Impact:** The viewer hears about performance degradation with context length but sees a static chart that was set up for the previous scene's conclusion. The key data visualization that would reinforce the narration's scientific claim is entirely absent.
- **Suggested Fix:** Either (a) adjust the `<Sequence from={-1350}>` offset for V14 so that the ContextRot internal clock is around frame 1020-1110 when V14 starts, or (b) create a separate standalone PerformanceGraphInset sequence specifically for V14 with its own fade-in/out timing synced to the EMNLP narration.

### Issue 2: Scene is entirely static for 29+ seconds
- **Severity:** MODERATE
- **Category:** Visual engagement
- **Description:** All three sample frames (t=202, t=215, t=228) are identical. There is no animation, transition, or visual change during the entire 29-second V14 segment. The ContextRot component at frame 1350+ renders a static end-state chart. The only "animation" is a subtle pulsing opacity on the context rot fill, which is imperceptible across snapshots.
- **Impact:** A 29-second static image during narration about a study that the script specifically visualizes as "a subtle graph inset" with "a line drops steadily" is a significant missed opportunity for viewer engagement and information retention.

### Issue 3: Annotations from prior scene persist inappropriately
- **Severity:** MINOR
- **Category:** Design / Continuity
- **Description:** The visible annotations ("Faster patching -> faster growth -> faster rot" and "Small modules. Clear prompts. Always fits in context.") are conclusions from the prior scene (V13's "The Consequence" wrap-up). During V14's narration about the EMNLP study, these annotations are not relevant to what the viewer is hearing. They create a disconnect between audio and visual.

---

## Verdict

**NEEDS_FIX**

The primary issue is a **timing synchronization bug**: the PerformanceGraphInset is fully implemented but its frame range (1020-1110 within ContextRot) does not align with V14's timeline due to the `-1350` offset. The narration at t=201-230s discusses the EMNLP study in detail, but the viewer sees only a static end-state chart from the prior conceptual beat. This is the same "MODERATE design limitation" flagged by the section-level audit ("Script calls for a Performance vs. Context Length graph inset -- Not implemented as a sub-visualization") but is more accurately described as a timing bug rather than a missing implementation; the component exists but is never shown at the right time.

---

## Files Referenced

- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/ContextRot.tsx` (main component, lines 187-189 control inset visibility)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/PerformanceGraphInset.tsx` (fully implemented inset, never shown during V14)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/07-ContextRot/constants.ts` (BEATS timing: RETURN_TO_CHART_START=1020)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S01-Economics/Part1Economics.tsx` (V14 offset at line 156: `from={-1350}`)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S01-Economics/constants.ts` (V14 timing: 201.16s-230.52s)
