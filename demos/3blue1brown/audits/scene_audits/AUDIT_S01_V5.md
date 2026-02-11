# Scene Audit: S01_V5 - CodeCostChart (Second Appearance, AI Patch Line)

**Section:** S01 Part 1 Economics
**Scene:** V5 - CodeCostChart (second appearance, with AI patch line)
**Video:** `outputs/sections/part1_economics.mp4`
**Time Range:** 40.78s - 54.68s (13.9s duration)
**Auditor:** Claude Opus 4.6
**Date:** 2026-02-09

---

## Verdict: PASS (with one known MODERATE issue documented)

---

## Frame Analysis

### Internal Frame Mapping

Visual 5 mounts `CodeCostChart` with `<Sequence from={-1800}>`. Given `VISUAL_05_START` = frame 1223 (40.78s), the internal CodeCostChart frame for any section time is:

```
internal_frame = (section_time * 30) - 1223 + 1800
```

| Sample Time | Section Frame | Internal Frame | Phase 2 Progress | Key Animation State |
|-------------|--------------|----------------|-------------------|---------------------|
| t=42s       | 1260         | 1837           | 28%               | "Same tools" annotation just appeared (1837 > 1800) |
| t=48s       | 1440         | 2017           | 43%               | Lines extending past 2022 toward 2023 |
| t=53s       | 1590         | 2167           | 56%               | Arrow visible (2167 > 2100), lines approaching 2023-2024 |

Phase 2 runs from DRAW_LINE_MID (1500) to DRAW_LINE_END (2700), covering the 2020-2025 year range.

### Frame 1: t=42s (Internal Frame ~1837)

**Observed:**
- Title "The Economics of Code" is displayed correctly at top
- Blue "Cost to Generate" line drawn from 2015 (~32 hrs) to just past 2020 (~29 hrs), beginning its Phase 2 descent
- Amber solid "Immediate Cost to Patch" baseline line flat at ~10 hrs from 2015-2020
- Amber dashed "Total Cost" line visible from 2015 (~22 hrs) to 2020 (~25 hrs), rising as expected
- Shaded tech debt area between the baseline and total cost lines is fully drawn for Phase 1 (2015-2020) and starting Phase 2
- Two forking amber lines just beginning to diverge past 2020: small codebase fork dropping (already ~9 hrs), large codebase staying near 10
- "Same tools. Different codebase sizes." annotation is centered on-screen in a dark overlay box

**Assessment:** Animation is progressing correctly. The fork is beginning. The blue "generate" line has just started dropping from ~30 hrs. All chart elements consistent with spec data points.

### Frame 2: t=48s (Internal Frame ~2017)

**Observed:**
- Blue "Cost to Generate" line has extended further, now reaching past 2021 and dropping more steeply (to ~26 hrs at the drawing tip around 2022)
- Small codebase fork has drawn down to roughly 5-6 hrs (around year 2022)
- Large codebase fork barely moved, still near 10 hrs
- Dashed total cost line has extended to ~26-27 hrs
- Tech debt shaded area is expanding into Phase 2 territory
- "Same tools. Different codebase sizes." annotation still visible
- No arrow yet (expected: appears at internal frame 2100)

**Assessment:** Animation matches expected behavior. The fork divergence is clearly visible. The blue generate line is beginning its dramatic plunge, consistent with the 2022 data point (28 hrs) and heading toward the steep 2023 drop. Small codebase amber fork is convincingly separating from the flat large codebase line.

### Frame 3: t=53s (Internal Frame ~2167)

**Observed:**
- Blue "Cost to Generate" line has plunged dramatically through 2023, now at approximately 13-14 hrs around 2023, headed toward the eventual 3 hrs at 2025
- Small codebase fork has dropped to approximately 3 hrs near 2023
- Large codebase fork has risen slightly to approximately 11 hrs
- Dashed total cost line has risen to approximately 30 hrs
- Tech debt shaded area has grown significantly, now spanning a wide vertical range
- "Same tools. Different codebase sizes." annotation still visible
- Curved arrow from small codebase fork to large codebase fork IS now visible with "Every patch adds code" label
- Arrow appears as a dashed curved path at approximately x=2023.5

**Assessment:** Excellent. The key dramatic moment is landing well. The blue line plunging (GPT-4/Claude era) is visually impactful. The fork divergence is clear. The arrow annotation appears at the right time and conveys the self-defeating cycle. The large codebase line staying flat/rising while the small codebase line drops creates the intended contrast.

---

## Script Alignment Check

**Script narration (40.78-54.68s):**
> "Now, here's where it gets interesting. AI made patching faster too. Cursor, Claude Code, Copilot -- they're incredible tools. They understand your codebase, suggest fixes, catch bugs before you make them."

**Visual alignment:**
- The narration talks about AI making patching faster. The visual shows the patch line forking, with the small-codebase fork dropping. This is a reasonable match -- the viewer sees the immediate cost dropping, which illustrates "AI made patching faster."
- The blue "generate" line is also beginning its dramatic plunge (GPT-4/Claude arriving ~2023). The script mentions Claude and Copilot -- so seeing the blue line drop simultaneously reinforces that AI impacts both activities.
- The narration does not explicitly mention the fork or codebase sizes, but the visual is setting up the next beat. The "Same tools. Different codebase sizes." annotation is somewhat forward-looking.

**Verdict:** Narration-visual sync is acceptable. The visual is slightly ahead of the narration (showing the fork and the "Same tools" annotation before the narration discusses codebase size differences), but this is a known issue documented below.

---

## Known Issues

### MODERATE: Premature "Same tools. Different codebase sizes." Annotation

**Description:** The annotation "Same tools. Different codebase sizes." appears at t=42s (internal frame 1800), but the narration about different codebase sizes doesn't arrive until much later (V15, around t=232s). At t=42s, the narration is still talking about how AI tools are incredible ("Cursor, Claude Code, Copilot -- they're incredible tools").

**Severity:** MODERATE -- This is a timing mismatch documented in the prior section-level audit. The annotation is contextually appropriate to the visual (the fork is happening), but it front-loads a message that the narration won't address for another 3 minutes. Viewers may be confused about the annotation's meaning before the narration explains it.

**Status:** Known from section-level audit. Does not block PASS. The fork visual itself (without the annotation) would be sufficient for this scene.

---

## Spec Compliance Summary

| Criterion | Status | Notes |
|-----------|--------|-------|
| Chart title "The Economics of Code" | PASS | Visible and correctly styled |
| Blue generate line starts high (~32 hrs) | PASS | Visible at 2015, stays high through 2020, then drops |
| Blue generate line plunges 2023+ | PASS | Dramatic drop visible at t=53s, matching GPT-4/Claude arrival |
| Amber baseline 2015-2020 (~10 hrs) | PASS | Flat line at 10 hrs |
| Fork at 2020 into two paths | PASS | Small CB dropping, large CB flat -- clearly visible |
| Small codebase fork drops to ~3 hrs by 2023 | PASS | Visible at t=53s |
| Large codebase fork stays flat ~10-12 hrs | PASS | Visible at t=53s, approximately 11 hrs |
| Dashed total cost line rises | PASS | Rising from ~25 to ~30 hrs by t=53s |
| Tech debt shaded area grows | PASS | Expanding noticeably through Phase 2 |
| "Same tools" annotation appears | PASS | Visible from t=42s (but timing vs narration is a known MODERATE issue) |
| "Every patch adds code" arrow | PASS | Appears at t=53s with curved arrow + label |
| Dark background gradient | PASS | Consistent 3Blue1Brown style |
| Legend visible | N/A | Legend appears at DRAW_LINE_END (frame 2700), after this scene ends |
| Color scheme matches spec | PASS | Blue #4A90D9, amber #D9944A consistent |

---

## Conclusion

The V5 scene successfully renders the second appearance of the CodeCostChart showing the post-2020 AI era. The fork divergence between small and large codebases is clearly visible and visually dramatic. The blue "generate" line's plunge beginning at 2023 aligns with the narration about AI tools arriving. The "Every patch adds code" arrow appears at the appropriate animation point. The one known MODERATE issue (premature "Same tools" annotation) was previously identified and does not block the overall PASS verdict.

**Result: PASS**
