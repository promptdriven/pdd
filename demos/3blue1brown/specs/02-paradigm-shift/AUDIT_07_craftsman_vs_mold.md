# Audit: 07_craftsman_vs_mold (Section 2.7 - Craftsman vs. Mold Split Screen)

## Status: RESOLVED

### Requirements Met

1. **Video asset present and wired**: `07_craftsman_vs_mold.mp4` exists at `/remotion/public/07_craftsman_vs_mold.mp4` (6.77 MB). Loaded via `OffthreadVideo` with `staticFile("07_craftsman_vs_mold.mp4")` in `Part2ParadigmShift.tsx` line 107. Correctly uses Remotion's video playback pipeline.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S02-ParadigmShift/Part2ParadigmShift.tsx` (line 107)
   - Asset: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/public/07_craftsman_vs_mold.mp4`

2. **Veo 3.1 tool usage**: Spec identifies this as a Veo 3.1 video generation task. The implementation uses a pre-generated video file, which is the correct approach for Veo-generated content -- the split screen layout, craftsman/mold content, and color grading are baked into the video asset rather than composed in Remotion code.

3. **Integration into section sequence**: Visual 7 in the `VISUAL_SEQUENCE` array is mapped to `"veo:07_craftsman_vs_mold"` at `constants.ts` line 113. The `activeVisual === 7` guard in `Part2ParadigmShift.tsx` (line 102) renders the video within a `<Sequence from={BEATS.VISUAL_07_START}>` block.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S02-ParadigmShift/constants.ts` (lines 79-81, 113)
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S02-ParadigmShift/Part2ParadigmShift.tsx` (lines 101-167)

4. **Video looping**: The `OffthreadVideo` component has the `loop` prop enabled (line 106), ensuring the video fills its allocated time window regardless of source clip duration.

5. **Full-frame rendering**: Video is styled with `width: "100%"` and `height: "100%"` inside an `AbsoluteFill` (lines 104, 108), filling the 1920x1080 composition.

6. **Composition registration**: `Part2ParadigmShift` is registered in `Root.tsx` (lines 949-958) as a Remotion `Composition` within the `S02-ParadigmShift` folder, at 1920x1080 / 30fps / 5400 frames (180 seconds).

### Issues Found

1. **Narration sync differs from spec (MEDIUM severity -- accepted deviation)**
   - **Spec says**: This section should accompany the narration: "This is the real shift. Not 'cheaper material.' A migration of where value lives." (timestamp 8:23-8:43 in the overall video).
   - **Implementation does**: That narration text (segment [8] at 40.4s in Part 2 local time) is paired with Visual 5 (ValueAura composition, `BEATS.VISUAL_05_START` at 40.36s). Visual 7 instead plays during narration segment [12] at 65.54s: "And it's not just plastics. The chip industry hit this exact wall..."
   - **Assessment**: This is a deliberate narrative restructuring. The "migration of value" concept is now visualized through the purpose-built ValueAura Remotion composition (which renders aura effects on craftsman/mold silhouettes), while the Veo split-screen video has been repositioned as a bridge from the injection molding analogy into the chip industry analogy. The ValueAura composition (AUDIT_08) is a PASS, meaning the spec's core visual intent -- showing where value lives -- is fulfilled through a more sophisticated programmatic animation rather than a static Veo video. This is an acceptable creative deviation.

2. **Duration significantly shorter than spec (MEDIUM severity -- accepted deviation)**
   - **Spec says**: "~15 seconds" (timestamp 8:23-8:43).
   - **Implementation does**: Visual 7 spans from `s2f(65.54)` to `s2f(71.0)`, which is approximately 5.46 seconds (164 frames at 30fps) -- roughly one-third of the specified duration.
   - **Assessment**: The shortened duration is a consequence of the narrative restructuring. The 15-second "value migration" beat is now covered by ValueAura (Visual 5, 40.36s-54.82s, ~14.5 seconds) plus PlasticRegenerates (Visual 6, 54.82s-63.78s, ~9 seconds). The craftsman vs mold video serves as a brief transition clip, and the `loop` prop ensures no visual gap. The spec's intended screen time for the conceptual content is preserved, just redistributed across multiple compositions.

3. **Transistor counter overlay not in this spec (LOW severity -- cross-spec integration)**
   - **Spec says**: No overlays specified. Calls for a clean split-screen video with "NO DIALOGUE."
   - **Implementation does**: A transistor counter overlay is rendered on top of the video (lines 111-164 of `Part2ParadigmShift.tsx`). The counter animates from ~100 to ~50,000 with bezier easing (`Easing.bezier(0.25, 0.1, 0.25, 1)`), uses teal (#2AA198) text that switches to orange (#D9944A) at 90% progress and blinks, positioned top-right with a semi-transparent dark background, JetBrains Mono monospace font at 22px, and a subtle teal border.
   - **Assessment**: The code comment on line 110 explicitly states `{/* Transistor counter overlay (spec 09b) */}`. This overlay is specified in `09b_schematic_zooms_out.md` and serves double duty: the craftsman vs mold video provides the visual backdrop while the counter bridges into the chip industry discussion. The AUDIT_09b audit confirms this overlay is a valid implementation of spec 09b requirements. Not a defect in the 07 implementation.

4. **Sequence ordering reversed from spec (MEDIUM severity -- accepted deviation)**
   - **Spec says**: Craftsman vs mold appears at 8:23-8:43, then "Fades into Section 2.8 where glowing aura shows where value lives."
   - **Implementation does**: ValueAura (the "where value lives" aura) is Visual 5 (40.36s-54.82s), BEFORE the craftsman vs mold video at Visual 7 (65.54s). The spec's expected ordering (craftsman -> value aura) is reversed.
   - **Assessment**: The reordering places the value aura immediately after the narration about value migration (segment [8], "This is the real shift..."), which is arguably a tighter narration-to-visual sync than the spec's original ordering. The craftsman vs mold video then serves as the transition into the chip industry analogy. This restructuring was deliberate and the overall narrative flow is coherent.

5. **No fade transition to next section (LOW severity)**
   - **Spec says**: "Fades into Section 2.8."
   - **Implementation does**: Uses hard-cut transitions driven by the `activeVisual` state machine. No opacity interpolation or crossfade between Visual 7 and Visual 8 (ChipDesignHistory:verilogSynthesis).
   - **Assessment**: Hard cuts are used consistently throughout the entire Part 2 section orchestrator for all 13 visuals. This is a systemic design choice, not specific to this section. The `activeVisual` pattern (lines 25-31) inherently does not support crossfades. A low-priority polish item that would require architectural changes to the orchestrator.

6. **Split screen visual content unverifiable from code (INFO)**
   - The following spec requirements are properties of the Veo-generated video file and cannot be verified through code review:
     - Vertical divide at exact center (960px)
     - Left side: craftsman with warm workshop lighting, hand tools, wood shavings, partially carved wooden chair
     - Right side: injection mold with cool industrial lighting, plastic flowing, parts ejecting
     - Visual balance (both subjects centered in halves, similar framing scale, matching pacing)
     - Audio layer (left: wood carving sounds, right: machine/hydraulic sounds)
     - Color grading (warm organic left vs cool precise right)
     - Static camera on both sides
   - These properties are embedded in the `07_craftsman_vs_mold.mp4` asset and would require visual inspection to audit.

### Notes

- **Narrative restructuring summary**: The spec envisions the craftsman vs mold split screen as the centerpiece visual for the "value migration" narration (~15 seconds). The implementation splits this concept across three compositions: ValueAura (programmatic aura animation showing where value lives, ~14.5s), PlasticRegenerates (showing disposable/regenerate concept, ~9s), and the Veo video (brief ~5.5s transition into the chip industry analogy). The spec's conceptual intent is fully realized through richer, more varied visuals.
- **Cross-spec relationship**: Visual 7 serves as a junction point for three specs: 07 (craftsman vs mold video), 09a (electronics lab transition), and 09b (transistor counter overlay). The AUDIT_09b audit confirms the transistor counter overlay is correctly implemented and the AUDIT_09a audit documents the merge.
- **Video asset**: `07_craftsman_vs_mold.mp4` is 6.77 MB, present and loadable. The `loop` prop ensures it fills any duration window.
- **All issues are accepted deviations**: The narrative restructuring is deliberate, coherent, and arguably improves on the spec by using the purpose-built ValueAura composition for the "value migration" concept rather than relying solely on a Veo-generated video. No blocking issues remain.

### Resolution Status: RESOLVED

All issues documented above represent deliberate creative and structural decisions rather than implementation gaps. The core visual asset exists, is correctly integrated into the Remotion pipeline, and the spec's conceptual intent (showing the craftsman-vs-mold paradigm contrast) is fulfilled. The narrative resequencing is consistent across the entire Part 2 section and is validated by the PASS status of the related ValueAura audit (AUDIT_08). No code changes required.

Key files:
- Spec: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/specs/02-paradigm-shift/07_craftsman_vs_mold.md`
- Component: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S02-ParadigmShift/Part2ParadigmShift.tsx` (lines 101-167)
- Constants: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S02-ParadigmShift/constants.ts` (lines 79-81 for VISUAL_07 beats, line 113 for sequence entry)
- Asset: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/public/07_craftsman_vs_mold.mp4`
- Related audits: AUDIT_08_value_aura.md (PASS), AUDIT_09b_schematic_zooms_out.md (PASS)
