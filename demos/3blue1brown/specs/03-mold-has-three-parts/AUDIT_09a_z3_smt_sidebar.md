# Audit: Z3 SMT Sidebar (09a)

## Status: RESOLVED

### Requirements Met

1. **Composition exists with correct file structure**: Standalone composition at `29a-Z3SmtSidebar/` with `Z3SmtSidebar.tsx`, `constants.ts`, `index.ts`. Clean module boundary with proper exports.
   - `constants.ts:1-66`, `index.ts:1-9`

2. **Canvas / resolution / duration**: 1920x1080 at 30fps, 20-second duration = 600 frames. All values defined in `constants.ts:4-9`. Matches spec ("Resolution: 1920x1080", "Duration: ~20 seconds").

3. **Background color**: `#1a1a2e` applied via `AbsoluteFill` at `Z3SmtSidebar.tsx:61`. Matches spec ("Background: Dark (#1a1a2e)").

4. **Synopsys Formality icon**: Checkmark SVG path rendered in teal `#2AA198` at `Z3SmtSidebar.tsx:121-130`. Container is 100x100 with 80x80 SVG. Matches spec requirement for "Synopsys checkmark/logo visual" in "Teal color (#2AA198)".

5. **Synopsys label**: "Synopsys Formality" rendered below icon in teal, 16px Inter font at `Z3SmtSidebar.tsx:132-141`. Text from `constants.ts:40`. Matches spec line 25: "Label below: Synopsys Formality".

6. **Synopsys fade-in timing**: Interpolates opacity from 0 to 1 over frames 0-60 at `Z3SmtSidebar.tsx:11-16`. Beat values `SYNOPSYS_START: 0, SYNOPSYS_END: 60` at `constants.ts:13-14`. Matches spec "Frame 0-60 (0-2s): Synopsys callback".

7. **Z3 logo**: Stylized "Z3" text in teal `#2AA198`, 48px bold JetBrains Mono at `Z3SmtSidebar.tsx:197-206`. Container is 100x100. Matches spec "Z3 solver logo or stylized Z3 text" in "Teal color (#2AA198)".

8. **Z3 label**: "Z3 (Microsoft Research)" rendered below in teal, 16px Inter font at `Z3SmtSidebar.tsx:208-217`. Text from `constants.ts:41`. Matches spec line 31: "Label below: Z3 (Microsoft Research)".

9. **Z3 fade-in timing**: Interpolates opacity 0 to 1 over frames 60-120 at `Z3SmtSidebar.tsx:19-24`. Beat values `Z3_START: 60, Z3_END: 120` at `constants.ts:15-16`. Matches spec "Frame 60-120 (2-4s): Z3 appears".

10. **Bridge line**: Horizontal teal line, 200px wide (`LAYOUT.BRIDGE_WIDTH` at `constants.ts:53`), 2px height, with `boxShadow: 0 0 8px` glow at `Z3SmtSidebar.tsx:144-160`. Width animates via percentage (`bridgeProgress * 100`). Matches spec "Horizontal line or bridge between the two logos, Teal, subtle glow".

11. **Bridge timing**: Progress interpolates 0 to 1 over frames 120-180 at `Z3SmtSidebar.tsx:27-32`. Beat values `BRIDGE_START: 120, BRIDGE_END: 180` at `constants.ts:17-18`. Matches spec "Frame 120-180 (4-6s): Connection established".

12. **Equivalence symbol on bridge**: Equals sign `=` appears at center of bridge when `bridgeProgress > 0.5`, opacity `(bridgeProgress - 0.5) * 2` at `Z3SmtSidebar.tsx:162-176`. Matches spec "An equals sign or ~ appears at the center of the bridge".

13. **Text line 1**: "Hardware: SMT-based formal proof" in 24px, `#B0B0C0` muted white, Inter font, 12px bottom margin at `Z3SmtSidebar.tsx:230-240`. Opacity fades frames 180-220. Matches spec lines 41-44.

14. **Text line 2**: "PDD: SMT-based formal proof" in 24px, `#B0B0C0`, Inter font, 20px bottom margin at `Z3SmtSidebar.tsx:241-251`. Opacity fades frames 220-260. Matches spec lines 41-44.

15. **Text line 3 ("Same math.")**: 32px, `#FFFFFF` bright white, fontWeight 700, Inter font at `Z3SmtSidebar.tsx:252-263`. Opacity fades frames 260-300. Matches spec "Same math. in brighter white (#FFFFFF), bold, slightly larger".

16. **Text sequential appearance**: Three separate opacity interpolations with staggered frame ranges (180-220, 220-260, 260-300) at `Z3SmtSidebar.tsx:35-52`. Matches spec "Text appears sequentially, line by line".

17. **"Same math." pulse animation**: Sinusoidal pulse `1.0 + Math.sin((frame - 300) * 0.08) * 0.1` applied as `transform: scale()` after frame 300 at `Z3SmtSidebar.tsx:55-58, 259`. Matches spec "Same math. pulses gently" and "Sinusoidal (manual Math.sin)" easing.

18. **Sidebar accent lines**: Top and bottom teal lines at 80px from edges, inset 120px left/right, 1px height, opacity 0.3, controlled by `showOverlay` prop at `Z3SmtSidebar.tsx:62-88`. Matches spec "Thin teal border at top and bottom" for sidebar frame.

19. **Easing - logo fade-ins**: `Easing.out(Easing.cubic)` at `Z3SmtSidebar.tsx:15,23`. Matches spec "Logo fade-ins: easeOutCubic".

20. **Easing - bridge line draw**: `Easing.inOut(Easing.quad)` at `Z3SmtSidebar.tsx:31`. Matches spec "Bridge line draw: easeInOutQuad".

21. **Easing - text line fade-ins**: `Easing.out(Easing.cubic)` at `Z3SmtSidebar.tsx:39,45,51`. Matches spec "Text line fade-ins: easeOutCubic".

22. **Color palette completeness**: All spec colors present in `constants.ts:30-36` -- BACKGROUND `#1a1a2e`, TEAL `#2AA198`, MUTED_WHITE `#B0B0C0`, BRIGHT_WHITE `#FFFFFF`. Additionally defines `TEAL_DIM: #1a7a75` (unused but available).

23. **Text content accuracy**: All text strings in `constants.ts:39-44` match spec verbatim.

24. **Beat timings completeness**: All timing constants in `constants.ts:12-27` match the spec animation sequence frame-for-frame:
    - Synopsys: 0-60 (spec 0-2s at 30fps = 0-60)
    - Z3: 60-120 (spec 2-4s = 60-120)
    - Bridge: 120-180 (spec 4-6s = 120-180)
    - Line1: 180-220, Line2: 220-260, Line3: 260-300 (spec 6-10s)
    - Pulse: 300 (spec 10s), Hold: 420 (spec 14s)

25. **Props schema**: Zod validation with `showOverlay` boolean defaulting to `true` at `constants.ts:58-66`. Clean typed props.

### Issues Found

1. **[HIGH] ~~Not integrated into S03-MoldThreeParts parent sequence~~**: RESOLVED. `Z3SmtSidebar` is now imported in `Part3MoldThreeParts.tsx` and replaces `TraditionalVsPdd` for Visual 8 and Visual 9 slots. The `VISUAL_SEQUENCE` entries in `constants.ts` have been updated to reference `Z3SmtSidebar` instead of `TraditionalVsPdd`.

2. **[HIGH] ~~Not registered in Root.tsx~~**: RESOLVED. `Z3SmtSidebar` is now registered as a `<Composition>` in `Root.tsx` under a `29a-Z3SmtSidebar` folder, with all required dimension/fps/duration constants and default props imported from `./29a-Z3SmtSidebar`.

3. **[LOW] Missing Synopsys shimmer/pulse recognition effect**: Spec line 57 requires "Brief shimmer/pulse -- you remember this from Part 2" on the Synopsys icon during frames 0-60. The implementation only applies a simple opacity fade-in (`Z3SmtSidebar.tsx:11-16`). No shimmer, scale pulse, or glow animation is present on the Synopsys icon to signal recognition callback. This is a visual polish item that affects the "you've seen this before" feel described in the spec.

4. **[LOW] Missing synchronized logo pulse during bridge phase**: Spec line 69 requires "Both logos pulse gently in unison" during frames 120-180 (bridge connection phase). Neither the Synopsys nor Z3 logo containers have any pulsing animation during this phase (`Z3SmtSidebar.tsx:104-108, 180-183`). After their initial fade-in, both logos remain at static opacity 1.0.

5. **[LOW] Sidebar accent lines lack animated fade-in**: Spec line 293 specifies "Sidebar frame: easeOutCubic" easing, implying the accent lines should fade in with easing. The implementation renders them with a static `opacity: 0.3` from frame 0 (`Z3SmtSidebar.tsx:73, 84`). No interpolation or easing is applied to the sidebar frame appearance.

6. **[LOW] Missing directional slide for logo entrances**: Spec line 56 says Synopsys "fades in from left" and spec line 63 says Z3 "fades in from right", implying positional movement (translateX) in addition to opacity. The implementation only animates opacity (`Z3SmtSidebar.tsx:106, 182`). No positional translation is applied to either logo during its entrance.

7. **[LOW] Bridge glow not intensified during hold phase**: Spec line 81 states "Bridge line glows" during the hold phase (frames 300-420), suggesting the glow should be more prominent or animated during this phase. The implementation has a constant `boxShadow: 0 0 8px` from the moment the bridge appears (`Z3SmtSidebar.tsx:158`). No glow intensification occurs during the hold/emphasis phase.

### Notes

- The standalone `Z3SmtSidebar` composition is well-structured and faithfully implements the core visual layout, color scheme, text content, beat timings, and primary easing curves from the spec. The fundamental visual design -- two logos, bridge line, three-line comparison text, and "Same math." punchline -- is accurately built.
- The two HIGH severity issues are integration problems: the composition exists as an isolated module but is not wired into either the parent S03 sequence or the Root composition registry. In the parent sequence, `TraditionalVsPdd` serves as a placeholder for both Visual 8 and Visual 9 slots that the spec clearly intends for this Z3 sidebar content.
- The five LOW severity issues are animation polish items: the Synopsys recognition shimmer, synchronized logo pulsing, sidebar frame animated entrance, directional logo slides, and bridge glow intensification. These are secondary animations that enhance the "callback recognition" and "emphasis" feel described in the spec but do not affect core layout, content, or timing accuracy.
- The narration timing in S03 constants maps frames 3528-5143 (117.6s-171.4s) to the Z3/SMT content. The standalone composition's own 600-frame (20s) duration aligns with the spec's stated 13:00-13:20 timestamp. Integration would require coordinating these parent-sequence frame offsets with the child composition's internal beat timings.
- The `gap` property on the logo row uses `LAYOUT.BRIDGE_WIDTH` (200) at `Z3SmtSidebar.tsx:96`, which means the visual gap between the Synopsys container and bridge, and between bridge and Z3 container, is each 200px -- effectively making the total distance between the two logos wider than the spec layout diagram suggests. The spec pseudocode uses `gap: 200` for the entire row but has the bridge element as a separate child in between. The implementation matches the spec pseudocode structure.

## Resolution Status: RESOLVED
